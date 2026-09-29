#!/usr/bin/env python3
"""Kimi Code 会话监控看板 — 本地 Web 服务（零依赖，仅标准库）。

用法: python3 server.py   （或 PORT=7788 python3 server.py）
"""
import faulthandler
import codecs
import fcntl
import json
import os
import pty
import re
import struct
import termios
import secrets
import signal
import socket
import subprocess
import tempfile
import threading
import time
import traceback
import urllib.error
import urllib.request
import zipfile
from collections import deque
from datetime import datetime
from urllib.parse import parse_qs, quote, urlparse
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path

HOME = Path.home()
SESSIONS_DIR = HOME / ".kimi-code" / "sessions"
PUBLIC_DIR = Path(__file__).parent / "public"
PORT = int(os.environ.get("PORT", "7788"))
RUNNING_WINDOW_MS = 60 * 1000          # wire.jsonl 最近 60s 有写入 => running
STALE_WAIT_MS = 5 * 60 * 1000          # 待确认但 5 分钟无动静 => stale
KEEP_MS = 7 * 24 * 3600 * 1000         # 内存中明细保留 7 天
TREND_DAYS = 7
# kimi web 本机地址：看板未覆盖的路径（/sessions/*、/assets/*、/api/* 等）反代到这里，
# 使本机访问时 iframe 同源——首次加载走本机毫秒级，之后点卡片走前端无刷新切换（不再整页重载）
KIMI_WEB_LOCAL = os.environ.get("KIMI_WEB_LOCAL", "http://127.0.0.1:58628")
# kimi web 外部访问地址（可选，如内网穿透/公网代理）：看板「进入会话」跳转拼 {webBase}/sessions/{sid} 用；
# 未设置时回退本机地址
WEB_BASE = os.environ.get("KIMI_WEB_BASE", KIMI_WEB_LOCAL)
_kw = urlparse(KIMI_WEB_LOCAL)
KIMI_WEB_HOST = _kw.hostname or "127.0.0.1"
KIMI_WEB_PORT = _kw.port or (443 if _kw.scheme == "https" else 80)
KIMI_WEB_HOSTPORT = _kw.netloc
PROXY_SKIP_HEADERS = {"connection", "keep-alive", "proxy-authenticate", "proxy-authorization",
                      "te", "trailers", "transfer-encoding", "upgrade", "host", "content-length"}


class _NoRedirect(urllib.request.HTTPRedirectHandler):
    """3xx 不跟随，原样透传给浏览器（OAuth 等跳转需由前端完成）。"""
    def redirect_request(self, req, fp, code, msg, headers, newurl):
        return None


_proxy_opener = urllib.request.build_opener(_NoRedirect)

# 会话「任务完成未查看」记录：sessionId -> 最后查看时间(ms)。
# 回合结束时间晚于查看时间 => 卡片显示「任务完成」；点击进入会话即记录查看
SEEN_FILE = Path(__file__).parent / "seen.json"
seen_map = {}
try:
    if SEEN_FILE.exists():
        seen_map = json.loads(SEEN_FILE.read_text(encoding="utf-8"))
except (OSError, ValueError):
    seen_map = {}


def save_seen():
    try:
        SEEN_FILE.write_text(json.dumps(seen_map, ensure_ascii=False), encoding="utf-8")
    except OSError:
        pass


# 清理 30 天以上的旧查看记录，防止 seen.json 无限增长；有缩减时立即回写
_seen_cutoff = int(time.time() * 1000) - 30 * 24 * 3600 * 1000
_seen_pruned = {k: v for k, v in seen_map.items() if isinstance(v, (int, float)) and v > _seen_cutoff}
if len(_seen_pruned) != len(seen_map):
    seen_map = _seen_pruned
    save_seen()
CONTEXT_MAX_TOKENS = 256_000           # 无法识别模型时的默认上下文窗口
# 模型上下文窗口规则：按名称子串匹配（小写），先命中先用
# 依据：GLM-5.3/Flash=1M（智谱官方文档）；Kimi K3=1M、K2.7-Code(coding)=256k（火山方舟文档）
MODEL_CONTEXT_RULES = [
    ("k3-256k", 256_000),
    ("256k", 256_000),
    ("k3", 1_000_000),
    ("kimi-k2", 256_000),
    ("kimi-for-coding", 256_000),
    ("kimi", 256_000),
    ("glm-5", 1_000_000),
    ("glm", 200_000),
]
MODEL_CONTEXT_FILE = Path(__file__).parent / "models.json"  # 可选：用户自定义覆盖

_rules_cache = {"mtime": None, "rules": MODEL_CONTEXT_RULES}


def get_model_rules():
    """models.json 变化时自动重载（无需重启服务）。"""
    try:
        mtime = MODEL_CONTEXT_FILE.stat().st_mtime
    except OSError:
        mtime = None
    if mtime != _rules_cache["mtime"]:
        rules = list(MODEL_CONTEXT_RULES)
        try:
            custom = json.loads(MODEL_CONTEXT_FILE.read_text())
            if isinstance(custom, dict):
                rules = [(str(k).lower(), int(v)) for k, v in custom.items()] + rules
        except (OSError, ValueError):
            pass
        _rules_cache["mtime"] = mtime
        _rules_cache["rules"] = rules
    return _rules_cache["rules"]


def model_context(name):
    low = (name or "").lower()
    for pat, v in get_model_rules():
        if pat in low:
            return v
    return CONTEXT_MAX_TOKENS
TODO_REFRESH_S = 60                    # 待办刷新间隔
TODOS_DIR = HOME / "knowledge" / "todos"
KB_VAULT = HOME / "Library/Mobile Documents/iCloud~md~obsidian/Documents/我的知识库"
KB_DIRS = ("Areas", "BulletJournal", "Projects", "Products")
KB_EXCLUDE_FILES = {"待办清单.md", "市场线索.md", "重点关注.md", "Inbox.md", "临时任务.md"}
KB_SKIP_DIRS = {"Archive", ".trash", ".obsidian", "copilot", ".git", "Temp"}
KB_MAX_FILE = 512 * 1024

# wirePath -> {offset, mtimeMs, rem, usage, pending, lastPrompt, tools, turns, files, ctx}
wire_cache = {}
scan_lock = threading.Lock()
events_buf = deque(maxlen=50)          # 全局实时事件流
events_lock = threading.Lock()
todos_cache = {"ok": None, "items": [], "hint": "", "updatedAt": 0}
sys_stats = {"cpu": 0.0, "memUsed": 0, "memTotal": 0, "diskUsed": 0, "diskTotal": 0,
             "netDown": 0.0, "netUp": 0.0, "updatedAt": 0}


def day_start_ms(now=None):
    dt = datetime.fromtimestamp((now or time.time()) / 1000)
    return int(datetime(dt.year, dt.month, dt.day).timestamp() * 1000)


def date_str(ms):
    return datetime.fromtimestamp(ms / 1000).strftime("%Y-%m-%d")


def _to_ms(v):
    """把 state.json 里的时间字段统一转成毫秒时间戳，失败返回 0。"""
    if isinstance(v, (int, float)):
        return int(v)
    if isinstance(v, str):
        try:
            return int(datetime.fromisoformat(v.replace("Z", "+00:00")).timestamp() * 1000)
        except ValueError:
            return 0
    return 0


def push_event(etype, t, text, meta):
    if not text:
        return
    with events_lock:
        events_buf.appendleft({
            "t": int(t or time.time() * 1000),
            "type": etype,
            "sessionId": meta.get("sessionId", ""),
            "title": (meta.get("title") or "")[:40],
            "text": str(text)[:120],
        })


def extract_prompt_text(e):
    origin = e.get("origin") or {}
    for m in origin.get("clientMetadata") or []:
        composer = (m or {}).get("kimi_code_composer")
        if composer and composer.get("display_text"):
            return composer["display_text"]
    parts = [p.get("text", "") for p in e.get("input") or [] if p.get("type") == "text"]
    return " ".join(parts) if parts else ""


def _cheap_time(line):
    """从原始行里廉价提取第一个 "time":<毫秒>，避免解析超大 JSON。"""
    marker = '"time":'
    pos = line.find(marker)
    if pos < 0:
        return None
    start = pos + len(marker)
    end = start
    while end < len(line) and line[end].isdigit():
        end += 1
    if end == start:
        return None
    try:
        return int(line[start:end])
    except ValueError:
        return None


def handle_line(entry, line):
    # 快速预过滤：绝大多数行不是目标事件，避免昂贵的 JSON 解析
    if not ('"usage.record"' in line or '"interaction.' in line or '"turn.prompt"' in line
            or '"tool.call"' in line or '"token_counting.measured"' in line
            or '"turn.ended"' in line or '"file_history.tracked"' in line or '"llm.request"' in line
            or '"tool.result"' in line):
        return
    try:
        e = json.loads(line)
    except ValueError:
        return
    if not isinstance(e, dict) or not isinstance(e.get("type"), str):
        return
    etype = e["type"]
    if etype == "usage.record":
        # 按天/按小时增量聚合，不保留原始事件（内存 O(天数×模型数)）
        t = e.get("time") or int(time.time() * 1000)
        if t > entry["reqEndT"]:
            entry["reqEndT"] = t  # 请求已返回（思考/生成结束）
        ds = date_str(t)
        usage = e.get("usage") or {}
        vec = [usage.get("inputOther") or 0, usage.get("output") or 0,
               usage.get("inputCacheRead") or 0, usage.get("inputCacheCreation") or 0]
        model = e.get("model") or "unknown"
        day_models = entry["usageByDay"].setdefault(ds, {})
        mvec = day_models.get(model)
        if mvec is None:
            day_models[model] = list(vec)
        else:
            for i in range(4):
                mvec[i] += vec[i]
        ut = entry["usageTotal"]
        for i in range(4):
            ut[i] += vec[i]
        if entry["hourDay"] != ds:
            entry["usageByHour"].clear()
            entry["hourDay"] = ds
        hour = datetime.fromtimestamp(t / 1000).hour
        hour_models = entry["usageByHour"].setdefault(hour, {})
        hvec = hour_models.get(model)
        if hvec is None:
            hour_models[model] = list(vec)
        else:
            for i in range(4):
                hvec[i] += vec[i]
        # 记录最新使用的模型
        if model and t >= entry["lastModelTime"]:
            entry["lastModel"] = model
            entry["lastModelTime"] = t
    elif etype == "interaction.request":
        req = e.get("request") or {}
        entry["pending"][e.get("id")] = {
            "id": e.get("id"),
            "kind": e.get("kind") or req.get("kind") or "approval",
            "toolName": req.get("toolName") or e.get("toolName") or "?",
            "action": req.get("action") or "",
            "requestedAt": e.get("time") or int(time.time() * 1000),
        }
        push_event("approval", e.get("time"),
                   f"{req.get('toolName') or '?'} 请求确认", entry["meta"])
    elif etype == "interaction.resolved":
        entry["pending"].pop(e.get("id"), None)
    elif etype == "turn.prompt":
        text = extract_prompt_text(e)
        if text:
            entry["lastPrompt"] = text
            push_event("task", e.get("time"), text, entry["meta"])
    elif etype == "llm.request":
        rt = e.get("time") or int(time.time() * 1000)
        if rt > entry["reqStartT"]:
            entry["reqStartT"] = rt  # 请求已发出（思考/生成开始）
    elif etype == "turn.ended":
        ds = date_str(e.get("time") or 0)
        acc = entry["turnsByDay"].setdefault(ds, [0, 0])
        acc[0] += 1
        acc[1] += e.get("durationMs") or 0
        hour = datetime.fromtimestamp((e.get("time") or 0) / 1000).hour
        day_h = entry["turnsByHour"].setdefault(ds, {})
        day_h[hour] = day_h.get(hour, 0) + 1
    elif etype == "token_counting.measured":
        tokens = e.get("tokens") or 0
        if tokens and (entry["ctx"] is None or e.get("time", 0) >= entry["ctxTime"]):
            entry["ctx"] = tokens
            entry["ctxTime"] = e.get("time") or 0
    elif etype == "file_history.tracked":
        p = e.get("path")
        if p:
            entry["filesByDay"].setdefault(date_str(e.get("time") or 0), set()).add(p)
    # 回合生命周期信号：回合开始/结束、工具在途、最后活动时间
    if etype in ("turn.prompt", "llm.request"):
        t = e.get("time") or int(time.time() * 1000)
        if t > entry["turnStartT"]:
            entry["turnStartT"] = t
    if etype == "turn.ended":
        t = e.get("time") or int(time.time() * 1000)
        if t > entry["turnEndT"]:
            entry["turnEndT"] = t
    if etype == "tool.call" or (etype == "context.append_loop_event" and isinstance(e.get("event"), dict) and e["event"].get("type") == "tool.call"):
        t = e.get("time") or int(time.time() * 1000)
        if t > entry["toolCallT"]:
            entry["toolCallT"] = t
    if etype == "tool.result" or (etype == "context.append_loop_event" and isinstance(e.get("event"), dict) and e["event"].get("type") == "tool.result"):
        t = e.get("time") or int(time.time() * 1000)
        if t > entry["toolResultT"]:
            entry["toolResultT"] = t
    if etype in ("usage.record", "token_counting.measured", "interaction.request", "interaction.resolved", "file_history.tracked") or \
       (etype in ("turn.prompt", "llm.request")) or \
       (etype == "context.append_loop_event" and isinstance(e.get("event"), dict) and e["event"].get("type") in ("tool.call", "tool.result")):
        t = e.get("time") or int(time.time() * 1000)
        if t > entry["lastAnyT"]:
            entry["lastAnyT"] = t

    elif etype == "context.append_loop_event":
        # 超大行（可达数十 MB）不做完整 JSON 解析，只廉价提取工具名
        if len(line) > 1_000_000:
            marker = '"name":"'
            pos = line.find(marker, line.find('"tool.call"'))
            if pos >= 0:
                end = line.find('"', pos + len(marker))
                name = line[pos + len(marker):end] if end > pos else "?"
                ds = date_str(e_time if (e_time := _cheap_time(line)) else int(time.time() * 1000))
                day_tools = entry["toolsByDay"].setdefault(ds, {})
                day_tools[name] = day_tools.get(name, 0) + 1
            return
        ev = e.get("event") or {}
        if isinstance(ev, dict) and ev.get("type") == "tool.call":
            name = ev.get("name") or "?"
            ds = date_str(e.get("time") or 0)
            day_tools = entry["toolsByDay"].setdefault(ds, {})
            day_tools[name] = day_tools.get(name, 0) + 1
            push_event("tool", e.get("time"),
                       ev.get("description") or f"调用 {name}", entry["meta"])


def prune_entry(entry, today_ds, oldest_ds):
    def keep(ds):
        return oldest_ds <= ds <= today_ds
    for store in (entry["usageByDay"], entry["toolsByDay"], entry["turnsByDay"], entry["filesByDay"], entry.get("turnsByHour", {})):
        for ds in [d for d in store if not keep(d)]:
            del store[ds]
    if entry["hourDay"] != today_ds:
        entry["usageByHour"].clear()
        entry["hourDay"] = today_ds


def new_entry():
    return {"offset": 0, "mtimeMs": 0, "rem": bytearray(),
            "usageByDay": {}, "usageByHour": {}, "hourDay": "",
            "toolsByDay": {}, "turnsByDay": {}, "filesByDay": {},
            "usageTotal": [0, 0, 0, 0],
            "turnsByHour": {},
            "pending": {}, "lastPrompt": "", "lastModel": "", "lastModelTime": 0,
            "turnStartT": 0, "turnEndT": 0, "lastAnyT": 0, "toolCallT": 0, "toolResultT": 0,
            "reqStartT": 0, "reqEndT": 0,
            "ctx": None, "ctxTime": 0, "meta": {}}


def feed_chunk(entry, chunk_bytes):
    # 基于 bytearray 的线性扫描：按偏移找行，避免对大缓冲反复切片/拼接
    rem = entry["rem"]
    rem += chunk_bytes
    start = 0
    while True:
        idx = rem.find(b"\n", start)
        if idx < 0:
            if start:
                del rem[:start]
            return
        line = bytes(rem[start:idx]).decode("utf-8", errors="replace")
        start = idx + 1
        handle_line(entry, line)
    # 循环只会经 return 退出；走完循环说明消费到末尾
    # （while True 内两个分支均已处理 del/clear）


def update_wire_file(wire_path, min_mtime, meta):
    try:
        st = wire_path.stat()
    except OSError:
        return None
    mtime = st.st_mtime_ns // 1_000_000
    key = str(wire_path)
    if mtime < min_mtime:
        wire_cache.pop(key, None)  # 超过统计窗口不再活跃，缓存条目一并释放
        return None  # 太久没有写入，不可能是活跃/待确认，也无近期 token
    entry = wire_cache.get(key)
    if entry is None or st.st_size < entry["offset"] or mtime < entry["mtimeMs"] - 1000:
        entry = new_entry()
        wire_cache[key] = entry
    entry["mtimeMs"] = mtime
    entry["meta"] = meta

    if st.st_size > entry["offset"]:
        try:
            with open(wire_path, "rb") as f:
                f.seek(entry["offset"])
                while True:
                    data = f.read(1 << 20)
                    if not data:
                        break
                    feed_chunk(entry, data)
                    entry["offset"] += len(data)
        except OSError:
            return entry
    return entry


def empty_usage():
    return {"inputOther": 0, "output": 0, "cacheRead": 0, "cacheCreation": 0, "byModel": {}}


def add_vec(acc, model, vec):
    """把 [inputOther, output, cacheRead, cacheCreation] 向量累加进聚合结构。"""
    acc["inputOther"] += vec[0]
    acc["output"] += vec[1]
    acc["cacheRead"] += vec[2]
    acc["cacheCreation"] += vec[3]
    m = acc["byModel"].setdefault(model, empty_usage())
    for i, k in enumerate(("inputOther", "output", "cacheRead", "cacheCreation")):
        m[k] += vec[i]


def _scan_sessions():
    now = int(time.time() * 1000)
    today = day_start_ms(now)
    week_ago = now - TREND_DAYS * 24 * 3600 * 1000
    today_ds = date_str(now)
    oldest_ds = date_str(week_ago)
    sessions = []
    trend7d, trend24h = {}, {}
    seen_wires = set()
    tool_counts = {}
    turn_count, turn_ms = 0, 0  # 今日轮次统计（turnStats）
    turn_hours = [0] * 24       # 今日按小时轮次分布（轮次卡浮层用）

    base = Path(SESSIONS_DIR)
    try:
        workspaces = sorted(d for d in os.listdir(base) if d.startswith("wd_"))
    except OSError:
        workspaces = []

    for wd in workspaces:
        wd_path = base / wd
        try:
            session_dirs = sorted(d for d in os.listdir(wd_path) if d.startswith("session_"))
        except OSError:
            continue
        for sid in session_dirs:
            sess_path = wd_path / sid
            try:
                with open(sess_path / "state.json", encoding="utf-8") as f:
                    state = json.load(f)
            except (OSError, ValueError):
                continue
            if state.get("archived"):
                continue

            agents_dir = sess_path / "agents"
            try:
                agent_dirs = sorted(os.listdir(agents_dir))
            except OSError:
                continue

            meta = {"sessionId": state.get("id") or sid,
                    "title": state.get("title") or ""}
            usage_today = empty_usage()
            sess_usage_total = [0, 0, 0, 0]   # 本会话所有 agent 的累计 token（entry 为循环内变量，不能在循环外引用）
            last_active = 0
            last_prompt = ""
            pending = {}
            tools_today = {}
            sess_turn_count = 0        # 近 7 天累计轮次（单会话）
            sess_turn_count_today = 0
            sess_turn_ms_today = 0
            files_changed = 0
            ctx = None
            sub_agents = 0
            last_model, last_model_time = "", 0
            turn_start = 0        # 最近回合开始
            turn_end = 0          # 最近回合结束
            last_any = 0          # 最后任一事件时间
            tool_call_t = 0       # 最近工具调用
            tool_result_t = 0     # 最近工具返回
            req_start = 0         # 最近 LLM 请求发出
            req_end = 0           # 最近 LLM 请求返回
            phase = "idle"
            in_turn = False
            thinking = False
            executing = False

            for agent_name in agent_dirs:
                wire_path = agents_dir / agent_name / "wire.jsonl"
                if not wire_path.is_file():
                    continue
                entry = update_wire_file(wire_path, week_ago, meta)
                seen_wires.add(str(wire_path))
                if entry is None:
                    continue
                prune_entry(entry, today_ds, oldest_ds)

                # 按天分桶聚合（内存中无原始事件明细）
                for ds, models in entry["usageByDay"].items():
                    is_today = ds == today_ds
                    acc = trend7d.setdefault(ds, empty_usage())
                    for model, vec in models.items():
                        add_vec(acc, model, vec)
                        if is_today:
                            add_vec(usage_today, model, vec)
                for i in range(4):
                    sess_usage_total[i] += entry["usageTotal"][i]
                for hour, models in entry["usageByHour"].items():
                    acc = trend24h.setdefault(hour, empty_usage())
                    for model, vec in models.items():
                        add_vec(acc, model, vec)
                pending.update(entry["pending"])
                for ds, cnts in entry["toolsByDay"].items():
                    if ds != today_ds:
                        continue
                    for name, c in cnts.items():
                        tools_today[name] = tools_today.get(name, 0) + c
                        tool_counts[name] = tool_counts.get(name, 0) + c
                for ds, acc in entry["turnsByDay"].items():
                    sess_turn_count += acc[0]
                    if ds == today_ds:
                        sess_turn_count_today += acc[0]
                        sess_turn_ms_today += acc[1]
                for h, c in entry.get("turnsByHour", {}).get(today_ds, {}).items():
                    try:
                        turn_hours[int(h)] += c
                    except (ValueError, IndexError):
                        pass
                today_files = entry["filesByDay"].get(today_ds)
                if today_files:
                    files_changed = max(files_changed, len(today_files))
                if entry["lastPrompt"]:
                    last_prompt = entry["lastPrompt"]
                if entry["lastModelTime"] > last_model_time:
                    last_model, last_model_time = entry["lastModel"], entry["lastModelTime"]
                if entry["ctx"]:
                    ctx = max(ctx or 0, entry["ctx"])
                turn_start = max(turn_start, entry["turnStartT"])
                turn_end = max(turn_end, entry["turnEndT"])
                last_any = max(last_any, entry["lastAnyT"])
                tool_call_t = max(tool_call_t, entry["toolCallT"])
                tool_result_t = max(tool_result_t, entry["toolResultT"])
                req_start = max(req_start, entry["reqStartT"])
                req_end = max(req_end, entry["reqEndT"])
                try:
                    m = wire_path.stat().st_mtime_ns // 1_000_000
                    last_active = max(last_active, m)
                    if agent_name != "main" and now - m < RUNNING_WINDOW_MS:
                        sub_agents += 1
                except OSError:
                    pass

            # 全局今日轮次统计（turnStats）
            turn_count += sess_turn_count_today
            turn_ms += sess_turn_ms_today

            in_turn = turn_start > turn_end
            thinking = req_start > req_end
            executing = tool_call_t > tool_result_t
            if last_active == 0 and not usage_today["inputOther"] and not usage_today["output"]:
                # 一周内没有 wire 写入：若 48h 内结束过，仍以空闲会话列出
                updated = _to_ms(state.get("updatedAt"))
                if updated == 0 or now - updated > 48 * 3600 * 1000:
                    continue
                last_active = updated
                status = "idle"
            elif pending:
                phase = "confirm"
                status = "stale" if now - last_active > STALE_WAIT_MS else "waiting"
            elif in_turn and now - last_any < 10 * 60_000:
                # 回合进行中：思考/执行工具均属运行中（wire 静默不影响）
                if thinking:
                    phase = "thinking"
                elif executing:
                    phase = "executing"
                else:
                    phase = "running"
                status = "running"
            elif turn_end and now - turn_end > 3000:
                phase = "idle"
                status = "idle"  # 回合明确结束 3s 后（防自动续跑抖动）→ 空闲
            elif now - last_active < RUNNING_WINDOW_MS:
                phase = "running"
                status = "running"  # 长工具执行中（60s 活跃窗口兜底）
            else:
                phase = "idle"
                status = "idle"

            title = state.get("title") or last_prompt or "(无标题)"
            # 与官方会话列表对齐：只隐藏「完全空壳」会话——空闲且 0 轮次 0 token
            # （一次性脚本/空开的 New Session）；有实际对话内容的会话始终展示，
            # 无论标题是用户命名还是自动生成。运行中/待确认的也始终展示。
            if status == "idle" and sess_turn_count == 0 and not any(sess_usage_total) \
                    and state.get("titleKind") != "custom":
                continue
            # 任务完成未查看：回合已结束（status=idle），且结束时间晚于该会话最后查看时间
            done_unseen = False
            if status == "idle":
                done_at = turn_end or _to_ms(state.get("updatedAt"))
                key = state.get("id") or sid
                done_unseen = bool(done_at and done_at > seen_map.get(key, 0))
            context_max = model_context(last_model)
            sessions.append({
                "sessionId": state.get("id") or sid,
                "workspace": wd,
                "cwd": state.get("cwd") or "",
                "title": title[:120],
                "lastPrompt": last_prompt[:200],
                "status": status,
                "phase": phase,
                "doneUnseen": done_unseen,
                "lastActive": int(last_active),
                "pending": list(pending.values()),
                "usageToday": usage_today,
                "contextTokens": ctx,
                "contextMax": context_max,
                "usageTotal": {"inputOther": sess_usage_total[0], "output": sess_usage_total[1], "cacheRead": sess_usage_total[2], "cacheCreation": sess_usage_total[3]},
                "turnCount": sess_turn_count,
                "turnCountToday": sess_turn_count_today,
                "filesChanged": files_changed,
                "subAgents": sub_agents,
                "model": last_model.split("/")[-1] if last_model else "",
            })

    sessions.sort(key=lambda s: s["lastActive"], reverse=True)

    totals = {"inputOther": 0, "output": 0, "cacheRead": 0, "cacheCreation": 0, "byModel": {}}
    counts = {"running": 0, "waiting": 0, "idle": 0, "stale": 0}
    for s in sessions:
        for k in ("inputOther", "output", "cacheRead", "cacheCreation"):
            totals[k] += s["usageToday"][k]
        for model, u in s["usageToday"]["byModel"].items():
            m = totals["byModel"].setdefault(model, empty_usage())
            for k in ("inputOther", "output", "cacheRead", "cacheCreation"):
                m[k] += u[k]
        counts[s["status"]] = counts.get(s["status"], 0) + 1

    def tokens(u):
        return u["inputOther"] + u["output"] + u["cacheRead"] + u["cacheCreation"]

    today_ds = date_str(now)
    days = []
    for i in range(TREND_DAYS - 1, -1, -1):
        ds = date_str(now - i * 24 * 3600 * 1000)
        days.append({"date": ds, "tokens": tokens(trend7d.get(ds, empty_usage()))})
    hours = []
    for h in range(24):
        u = trend24h.get(h, empty_usage())
        hours.append({"hour": h, "tokens": tokens(u)})
    top_tools = sorted(tool_counts.items(), key=lambda x: -x[1])[:8]

    # 清理已删除/不再活跃的 wire 缓存，防止长期运行内存缓增
    for stale_key in [k for k in wire_cache if k not in seen_wires]:
        del wire_cache[stale_key]

    with events_lock:
        events = list(events_buf)

    page_ver = ""
    try:
        page_ver = str(int((PUBLIC_DIR / "index.html").stat().st_mtime * 1000))
    except OSError:
        pass

    return {
        "now": now, "todayStart": today, "counts": counts, "totals": totals,
        "pageVer": page_ver,
        "webBase": WEB_BASE,
        "sessions": sessions,
        "trend7d": days, "trend24h": hours,
        "toolStats": [{"name": n, "count": c} for n, c in top_tools],
        "turnStats": {"count": turn_count, "avgMs": int(turn_ms / turn_count) if turn_count else 0},
        "turnHours": turn_hours,
        "events": events,
        "todos": todos_cache,
        "sys": {k: v for k, v in sys_stats.items() if not k.startswith("_")},
    }


# ---------- 系统资源监控（macOS） ----------

def _parse_size(text):
    """'16G' / '588M' / '1024K' -> 字节数。"""
    text = text.strip().upper()
    mult = 1
    if text.endswith("G"):
        mult, text = 1024 ** 3, text[:-1]
    elif text.endswith("M"):
        mult, text = 1024 ** 2, text[:-1]
    elif text.endswith("K"):
        mult, text = 1024, text[:-1]
    try:
        return int(float(text) * mult)
    except ValueError:
        return 0


def collect_sys_stats():
    snap = dict(sys_stats)

    # CPU：top 第 2 次采样才是真实区间（第 1 次是开机以来均值）
    r = subprocess.run(["top", "-l", "2", "-n", "0"], capture_output=True, text=True, timeout=30)
    usage_lines = [ln for ln in r.stdout.splitlines() if ln.startswith("CPU usage")]
    if usage_lines:
        vals = {}
        for part in usage_lines[-1].split(":", 1)[1].split(","):
            if "%" in part:
                v, k = part.split("%", 1)
                vals[k.strip()] = float(v)
        snap["cpu"] = round(vals.get("user", 0) + vals.get("sys", 0), 1)

    # 内存：vm_stat，口径对齐活动监视器（active + wired + compressed）
    try:
        total = int(subprocess.run(["sysctl", "-n", "hw.memsize"],
                                   capture_output=True, text=True, timeout=10).stdout.strip())
        r = subprocess.run(["vm_stat"], capture_output=True, text=True, timeout=10)
        pages = {}
        psize = 16384
        m = re.search(r"page size of (\d+)", r.stdout)
        if m:
            psize = int(m.group(1))
        for line in r.stdout.splitlines():
            if ":" in line and "." in line:
                k, v = line.split(":", 1)
                v = v.strip().rstrip(".")
                if v.isdigit():
                    pages[k.strip()] = int(v)
        used_pages = (pages.get("Pages active", 0) + pages.get("Pages wired down", 0)
                      + pages.get("Pages occupied by compressor", 0))
        snap["memTotal"] = total
        snap["memUsed"] = min(total, used_pages * psize)
    except (ValueError, subprocess.TimeoutExpired):
        pass

    # 存储空间：Data 数据卷才是用户真实占用（/ 是只读系统卷）
    r = subprocess.run(["df", "-k", "/System/Volumes/Data"], capture_output=True, text=True, timeout=10)
    lines = r.stdout.strip().splitlines()
    if len(lines) >= 2:
        cols = lines[1].split()
        snap["diskTotal"] = int(cols[1]) * 1024
        snap["diskUsed"] = int(cols[2]) * 1024

    # 网络速率：两次采样差值
    r = subprocess.run(["netstat", "-ib"], capture_output=True, text=True, timeout=10)
    rx = tx = 0
    for line in r.stdout.splitlines():
        cols = line.split()
        if len(cols) >= 10 and cols[0].startswith("en") and not cols[2].startswith("<"):
            try:
                rx += int(cols[6])
                tx += int(cols[9])
            except ValueError:
                pass
    prev = sys_stats
    now_ms = int(time.time() * 1000)
    dt = (now_ms - prev.get("updatedAt", 0)) / 1000
    if prev.get("updatedAt") and dt > 0 and rx >= prev.get("_rx", rx) and tx >= prev.get("_tx", tx):
        snap["netDown"] = round((rx - prev["_rx"]) / dt, 0)
        snap["netUp"] = round((tx - prev["_tx"]) / dt, 0)
    snap["_rx"], snap["_tx"] = rx, tx
    snap["updatedAt"] = now_ms
    sys_stats.clear()
    sys_stats.update(snap)


notified_approvals = {}  # "sessionId:approvalId" -> True（同一条只通知一次）


def notify_worker():
    """轮询待确认状态，新出现的审批弹 macOS 系统通知。"""
    while True:
        try:
            d = scan_sessions()
            current = {}
            for s in d.get("sessions", []):
                for p in s.get("pending", []):
                    key = s["sessionId"] + ":" + str(p.get("id"))
                    current[key] = (s.get("title") or "", p.get("toolName") or "?")
            fresh = {k: v for k, v in current.items() if k not in notified_approvals}
            for key in [k for k in notified_approvals if k not in current]:
                del notified_approvals[key]  # 已解决的允许再次出现时重新通知
            if fresh:
                notified_approvals.update({k: True for k in fresh})
                for key, (title, tool) in list(fresh.items())[:3]:
                    msg = f"{title[:40]}：{tool} 请求确认".replace('"', "'").replace("\\", "")
                    subprocess.run(["osascript", "-e",
                                    f'display notification "{msg}" with title "Kimi 看板 · 待确认" sound name "Glass"'],
                                   capture_output=True, timeout=10)
        except Exception:
            traceback.print_exc()
        time.sleep(5)


def read_kb_todos():
    """今日待办：优先读 ~/knowledge/todos/YYYY-MM.md 当日小节；无则回退 Obsidian 全库扫描。"""
    items = read_daily_todos()
    return items if items else read_obsidian_todos()


def _clean_todo_title(raw):
    """与 read_daily_todos 相同的标题清洗规则。"""
    title = re.sub(r"^⏭\s*", "", raw.strip()).strip()
    title = re.sub(r"\s+[✅⏭].*$", "", title).strip()
    return title or "(空事项)"


def set_kb_todo_state(title, done):
    """把今日小节中匹配 title 的任务设为完成/未完成（同步写回知识库文件）。"""
    title = (title or "").strip()
    if not title:
        return False
    fp = TODOS_DIR / (datetime.now().strftime("%Y-%m") + ".md")
    try:
        text = fp.read_text(encoding="utf-8", errors="replace")
    except OSError:
        return False
    lines = text.splitlines()
    today_head = datetime.now().strftime("%m-%d")
    start = None
    for i, ln in enumerate(lines):
        if ln.startswith("## ") and ln[3:].strip().startswith(today_head):
            start = i
            break
    if start is None:
        return False
    end = len(lines)
    for i in range(start + 1, len(lines)):
        if lines[i].startswith("## "):
            end = i
            break
    target = None
    for i in range(start + 1, end):
        s = lines[i].strip()
        for box in ("- [ ] ", "- [x] ", "- [X] "):
            if s.startswith(box):
                if _clean_todo_title(s[6:]) == title:
                    target = i
                    lines[i] = ("- [x] " if done else "- [ ] ") + s[6:]
                break
        if target is not None:
            break
    if target is None:
        return False
    try:
        fp.write_text("\n".join(lines) + "\n", encoding="utf-8")
    except OSError:
        return False
    return True


def add_kb_todo(title):
    """向今日小节追加一条待办（同步写回知识库文件，立即刷新缓存）。"""
    title = (title or "").strip()
    if not title:
        return False, "empty"
    title = re.sub(r"[\r\n#*]+", " ", title)[:100].strip()
    if not title:
        return False, "empty"
    fp = TODOS_DIR / (datetime.now().strftime("%Y-%m") + ".md")
    today_head = datetime.now().strftime("%m-%d")
    try:
        text = fp.read_text(encoding="utf-8", errors="replace")
    except OSError:
        text = ""
    lines = text.splitlines() if text else []
    # 定位今日小节
    start = None
    for i, ln in enumerate(lines):
        if ln.startswith("## ") and ln[3:].strip().startswith(today_head):
            start = i
            break
    # 查重：今日小节已有同标题项则拒绝
    if start is not None:
        end = len(lines)
        for i in range(start + 1, len(lines)):
            if lines[i].startswith("## "):
                end = i
                break
        for i in range(start + 1, end):
            s = lines[i].strip()
            for box in ("- [ ] ", "- [x] ", "- [X] "):
                if s.startswith(box):
                    if _clean_todo_title(s[6:]) == title:
                        return False, "dup"
                    break
    item_line = f"- [ ] {title}"
    if start is None:
        # 无今日小节：追加一个小节（含 **今日** 分组）
        if lines:
            lines.append("")
        lines.append(f"## {today_head}")
        lines.append("")
        lines.append("**今日**")
        lines.append(item_line)
    else:
        # 插入今日小节首条：优先 **今日** 组标题后，其余插到小节头/分组标题后
        insert_at = start + 1
        for i in range(start + 1, len(lines)):
            if lines[i].startswith("## "):
                insert_at = i
                break
            s = lines[i].strip()
            if s.startswith("**"):
                insert_at = i + 1
                break
        lines.insert(insert_at, item_line)
    try:
        fp.write_text("\n".join(lines) + "\n", encoding="utf-8")
    except OSError:
        return False, "io"
    # 立即刷新待办缓存 → payload 哈希变化 → SSE 推送
    try:
        items = read_kb_todos()
        todos_cache.clear()
        todos_cache.update({"ok": True, "items": items, "hint": "",
                            "updatedAt": int(time.time() * 1000)})
    except Exception:
        pass
    return True, ""


def read_daily_todos():
    """解析 knowledge/todos 当月文件中今天的小节：今日未完成 + 昨日遗留（标红）。"""
    fp = TODOS_DIR / (datetime.now().strftime("%Y-%m") + ".md")
    try:
        text = fp.read_text(encoding="utf-8", errors="replace")
    except OSError:
        return []
    sec = re.split(r"^## ", text, flags=re.M)
    head = datetime.now().strftime("%m-%d")
    block = next((s for s in sec if s.startswith(head)), "")
    if not block:
        return []
    items, legacy, done_items = [], False, []
    for ln in block.splitlines()[1:]:
        s = ln.strip()
        if s.startswith("**"):          # **今日** / **昨日遗留** 分组标题
            legacy = "遗留" in s or "顺延" in s
            continue
        done = None
        if s.startswith("- [ ] "):
            done = False
        elif s.lower().startswith("- [x] "):
            done = True
        else:
            continue                    # 跳过已取消、说明行
        title = s[6:].strip()
        if "❌" in title:
            continue
        carry = legacy or title.startswith("⏭")
        title = re.sub(r"^⏭\s*", "", title).strip()
        title = re.sub(r"\s+[✅⏭].*$", "", title).strip() or "(空事项)"
        item = {"id": title[:40], "title": title[:100],
                "priority": 0, "overdue": carry, "flag": "遗留" if carry else "",
                "done": done}
        (items if not done else done_items).append(item)
    return items + done_items


def read_obsidian_todos():
    """回退：读取 Obsidian 知识库中未完成的任务（对齐待办清单.md 的 Dataview 规则）。"""
    items = []
    base = KB_VAULT
    if not base.is_dir():
        return items
    for d in KB_DIRS:
        dp = base / d
        if not dp.is_dir():
            continue
        for root, dirs, files in os.walk(dp):
            dirs[:] = [x for x in dirs if x not in KB_SKIP_DIRS and not x.startswith(".")]
            for fn in files:
                if not fn.endswith(".md") or fn in KB_EXCLUDE_FILES:
                    continue
                fp = Path(root) / fn
                try:
                    if fp.stat().st_size > KB_MAX_FILE:
                        continue
                    text = fp.read_text(encoding="utf-8", errors="replace")
                except OSError:
                    continue
                for ln in text.splitlines():
                    s = ln.strip()
                    if s.startswith("- [ ] ") and 6 < len(s) <= 320:
                        title = s[6:].strip()
                        if title and not title.startswith("[[日期]]"):
                            items.append({"title": title[:100], "file": fn[:-3]})
    seen, out = set(), []
    for it in items:
        k = it["title"]
        if k not in seen:
            seen.add(k)
            out.append({"id": k[:40], "title": k, "priority": 0, "overdue": False})
            if len(out) >= 50:
                break
    return out


def sys_worker():
    while True:
        try:
            collect_sys_stats()
        except Exception:
            traceback.print_exc()
        time.sleep(10)  # top -l 2 采样本身有开销，10s 足够看板展示；网速速率基于 dt 差值自动适配


_scan_cache = {"ts": 0.0, "result": None}


def todo_worker():
    """每 5 分钟读取个人知识库的未完成任务。"""
    while True:
        try:
            items = read_kb_todos()
            todos_cache.clear()
            todos_cache.update({"ok": True, "items": items, "hint": "",
                                "updatedAt": int(time.time() * 1000)})
        except Exception as err:
            todos_cache.clear()
            todos_cache.update({"ok": False, "items": [], "hint": f"读取失败: {str(err)[:120]}",
                                "updatedAt": int(time.time() * 1000)})
        time.sleep(TODO_REFRESH_S)


def state_signature(d):
    """轻量变更签名：只包含会影响展示的字段，替代全量状态 json.dumps 哈希（省 CPU）。
    刻意排除：now（每秒必变）、sys 的 updatedAt/netDown/netUp/_rx/_tx（瞬时网速）。"""
    uk = ("inputOther", "output", "cacheRead", "cacheCreation")
    td = d.get("todos") or {}
    sysv = d.get("sys") or {}
    parts = (
        tuple(sorted((d.get("counts") or {}).items())),
        tuple((d.get("totals") or {}).get(k, 0) for k in uk),
        d.get("pageVer"), d.get("webBase"), d.get("todayStart"),
        tuple(
            (s.get("sessionId"), s.get("status"), s.get("phase"), s.get("lastActive"),
             len(s.get("pending") or ()), sum(s.get("usageToday", {}).get(k, 0) for k in uk),
             s.get("contextTokens"), s.get("doneUnseen"), s.get("turnCountToday"),
             s.get("filesChanged"), s.get("subAgents"))
            for s in d.get("sessions", [])
        ),
        tuple((x["date"], x["tokens"]) for x in d.get("trend7d", [])),
        tuple((x["hour"], x["tokens"]) for x in d.get("trend24h", [])),
        tuple((x["name"], x["count"]) for x in d.get("toolStats", [])),
        (d.get("turnStats") or {}).get("count"), (d.get("turnStats") or {}).get("avgMs"),
        tuple(d.get("turnHours") or []),
        (td.get("updatedAt"), len(td.get("items") or []), tuple(i.get("done") for i in td.get("items") or [])),
        tuple((e.get("time"), e.get("type"), e.get("text")) for e in d.get("events", [])),
        (round(sysv.get("cpu", 0), 1), sysv.get("memUsed"), sysv.get("diskUsed")),
    )
    return hash(parts)


def scan_sessions():
    now = time.time()
    with scan_lock:
        if _scan_cache["result"] is not None and now - _scan_cache["ts"] < 1.0:
            return _scan_cache["result"]
        result = _scan_sessions()
        _scan_cache["ts"] = now
        _scan_cache["result"] = result
        return result


# ---------- 文件看板 ----------

FILE_TOKEN_FILE = Path(__file__).parent / ".filetoken"
TEXT_READ_MAX = 512 * 1024           # 文本预览上限（超出截断）
WRITE_MAX = 2 * 1024 * 1024          # 编辑保存上限
RAW_PREVIEW_MAX = 20 * 1024 * 1024   # raw 预览上限（超限提示改下载）
# 已知文本扩展名 → raw 以 text/plain 下发；其余未知扩展名一律 octet-stream
TEXT_EXTS = {".py", ".js", ".ts", ".tsx", ".jsx", ".css", ".scss", ".html", ".htm",
             ".md", ".txt", ".log", ".sh", ".bash", ".zsh", ".yml", ".yaml", ".toml",
             ".ini", ".cfg", ".conf", ".xml", ".csv", ".sql", ".java", ".kt", ".go",
             ".rs", ".c", ".h", ".cpp", ".hpp", ".m", ".mm", ".swift", ".rb", ".php",
             ".lua", ".gradle", ".properties", ".plist", ".json", ".gitignore"}
RAW_TYPES = {
    ".png": "image/png", ".jpg": "image/jpeg", ".jpeg": "image/jpeg",
    ".gif": "image/gif", ".webp": "image/webp", ".svg": "image/svg+xml",
    ".ico": "image/x-icon", ".bmp": "image/bmp",
    ".pdf": "application/pdf",
    ".mp3": "audio/mpeg", ".wav": "audio/wav", ".mp4": "video/mp4", ".webm": "video/webm",
    ".zip": "application/zip", ".gz": "application/gzip", ".tgz": "application/gzip",
    ".tar": "application/x-tar", ".json": "application/json",
    ".woff2": "font/woff2", ".woff": "font/woff", ".ttf": "font/ttf",
}


def _file_token():
    """首访令牌：首次启动生成 64 位 hex 写入 .filetoken（chmod 600），之后读取复用。"""
    try:
        tok = FILE_TOKEN_FILE.read_text(encoding="utf-8").strip()
        if tok:
            return tok
    except OSError:
        pass
    tok = secrets.token_hex(32)
    try:
        FILE_TOKEN_FILE.write_text(tok, encoding="utf-8")
        os.chmod(FILE_TOKEN_FILE, 0o600)
    except OSError:
        pass
    return tok


FILE_TOKEN = _file_token()


def allowed_roots():
    """允许浏览的根 = 当前展示会话的 cwd 去重（与看板工作空间口径一致）。"""
    roots = set()
    for s in scan_sessions().get("sessions", []):
        cwd = (s.get("cwd") or "").strip()
        if cwd:
            rp = os.path.realpath(cwd)
            if os.path.isdir(rp):
                roots.add(rp)
    return roots


def resolve_file_path(raw):
    """规范化并校验路径必须位于某个允许根内（防 ../ 与软链逃逸）。
    多根嵌套时取最长匹配（最具体的根），否则会把子工作空间误归属到浅根。"""
    raw = (raw or "").strip()
    if not raw.startswith("/"):
        return None
    p = os.path.realpath(raw)
    best = None
    for root in allowed_roots():
        if p == root or p.startswith(root + os.sep):
            if best is None or len(root) > len(best):
                best = root
    return (p, best) if best else None


def is_sensitive(path):
    """敏感文件黑名单：密钥/凭证类一律拒绝读写。"""
    parts = [x.lower() for x in Path(path).parts]
    if ".ssh" in parts:
        return True
    name = parts[-1]
    return (name.startswith(".env") or name == ".filetoken"
            or name.startswith("id_rsa")
            or name.startswith("id_ed25519") or name.endswith(".pem")
            or name.endswith(".p12") or name.endswith(".pfx")
            or "credential" in name)


def file_list_data(p, root):
    items = []
    with os.scandir(p) as it:
        for e in it:
            try:
                st = e.stat()
                is_dir = e.is_dir()
                items.append({"name": e.name, "isDir": is_dir,
                              "size": 0 if is_dir else st.st_size,
                              "mtime": int(st.st_mtime * 1000)})
            except OSError:
                continue
    items.sort(key=lambda x: (not x["isDir"], x["name"].lower()))
    parent = os.path.dirname(p)
    if not (parent == root or parent.startswith(root + os.sep)):
        parent = ""
    return {"path": p, "root": root, "parent": parent, "isRoot": p == root, "items": items}


def file_read_data(p):
    st = os.stat(p)
    size = st.st_size
    with open(p, "rb") as f:
        data = f.read(TEXT_READ_MAX)
    mtime = int(st.st_mtime * 1000)
    if b"\x00" in data:
        return {"binary": True, "size": size, "mtime": mtime}
    text, enc = None, ""
    for e in ("utf-8", "gbk"):
        try:
            text = data.decode(e)
            enc = e
            break
        except UnicodeDecodeError:
            continue
    if text is None:
        return {"binary": True, "size": size, "mtime": mtime}
    return {"content": text, "encoding": enc, "truncated": size > len(data),
            "size": size, "mtime": mtime}


VENDOR_DIR = PUBLIC_DIR / "vendor"
VENDOR_NAME_RE = re.compile(r"^[A-Za-z0-9._-]+$")
CONVERT_EXTS = (".doc", ".docx", ".rtf", ".odt")   # textutil 可转换的 Word 系格式
CONVERT_MAX = 10 * 1024 * 1024
THUMB_MAX = 20 * 1024 * 1024


def pptx_outline_data(p):
    """pptx → 分页文本大纲（纯标准库：zipfile + 正则抽 <a:t> 文本）。"""
    slides = []
    with zipfile.ZipFile(p) as z:
        for name in z.namelist():
            m = re.match(r"^ppt/slides/slide(\d+)\.xml$", name)
            if m:
                slides.append((int(m.group(1)), name))
        out = []
        for n, name in sorted(slides):
            xml = z.read(name).decode("utf-8", errors="replace")
            lines = []
            for para in re.findall(r"<a:p>(.*?)</a:p>", xml, re.S):
                line = "".join(re.findall(r"<a:t>(.*?)</a:t>", para, re.S)).strip()
                if line:
                    lines.append(line)
            out.append({"n": n, "lines": lines[:40]})
    return {"slides": out}


# ---------- 终端（PTY 真 shell） ----------

TERMS = {}                  # ts -> {pid, fd, buf, lock, alive, total, ws, last_poll}
TERMS_LOCK = threading.RLock()
TERMS_MAX = 6               # 存活终端上限
TERM_BUF_MAX = 1024 * 1024  # 输出缓冲上限（字符）
TERM_IDLE_MAX = 1800        # 30 分钟无轮询回收


def _term_kill(ts):
    with TERMS_LOCK:
        t = TERMS.pop(ts, None)
    if not t:
        return
    try:
        os.killpg(t['pid'], signal.SIGHUP)
    except (ProcessLookupError, PermissionError, OSError):
        pass
    try:
        os.close(t['fd'])
    except OSError:
        pass


def _term_reaper(ts):
    """读线程：PTY 输出 → utf-8 增量解码 → 缓冲；EOF 后收尸。"""
    t = TERMS.get(ts)
    if not t:
        return
    dec = codecs.getincrementaldecoder('utf-8')('replace')
    try:
        while True:
            try:
                data = os.read(t['fd'], 65536)
            except OSError:
                break
            if not data:
                break
            text = dec.decode(data)
            with t['lock']:
                t['buf'] = (t['buf'] + text)[-TERM_BUF_MAX:]
                t['total'] += len(text)
    except Exception:
        pass
    try:
        os.close(t['fd'])
    except OSError:
        pass
    try:
        _, st = os.waitpid(t['pid'], 0)
        with TERMS_LOCK:
            cur = TERMS.get(ts)
            if cur:
                cur['exit'] = st
    except (ChildProcessError, OSError):
        pass
    with TERMS_LOCK:
        cur = TERMS.get(ts)
        if cur:
            cur['alive'] = False
            cur['exit'] = cur.get('exit', -1)


def _term_reap_idle():
    """回收线程：长时间无轮询的终端自动关闭。"""
    while True:
        time.sleep(60)
        now = time.time()
        with TERMS_LOCK:
            stale = [ts for ts, t in TERMS.items() if now - t.get('last_poll', 0) > TERM_IDLE_MAX]
        for ts in stale:
            _term_kill(ts)


def _term_open(cwd):
    rp = os.path.realpath((cwd or '').strip())
    roots = allowed_roots()
    if not any(rp == r or rp.startswith(r + os.sep) for r in roots):
        return None, 'forbidden'
    if not os.path.isdir(rp):
        return None, 'not a directory'
    with TERMS_LOCK:
        alive = [k for k, v in TERMS.items() if v['alive']]
        if len(alive) >= TERMS_MAX:
            _term_kill(alive[0])
    pid, fd = pty.fork()
    if pid == 0:   # 子进程：exec zsh（登录 shell，读 .zshrc）
        try:
            os.chdir(rp)
            os.environ['TERM'] = 'xterm-256color'
            os.environ['COLORTERM'] = 'truecolor'
            os.execvp('/bin/zsh', ['zsh', '-l'])
        except Exception:
            os._exit(127)
    try:
        fcntl.ioctl(fd, termios.TIOCSWINSZ, struct.pack('HHHH', 40, 120, 0, 0))
    except OSError:
        pass
    ts = 'T' + secrets.token_hex(8)
    with TERMS_LOCK:
        TERMS[ts] = {'pid': pid, 'fd': fd, 'buf': '', 'lock': threading.Lock(),
                     'alive': True, 'total': 0, 'ws': rp, 'last_poll': time.time()}
    threading.Thread(target=_term_reaper, args=(ts,), daemon=True).start()
    return ts, None

# ---------- HTTP 接口 ----------

class Handler(BaseHTTPRequestHandler):
    def _json_reply(self, obj):
        body = json.dumps(obj, ensure_ascii=False).encode("utf-8")
        self.send_response(200)
        self.send_header("Content-Type", "application/json; charset=utf-8")
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def _read_body(self):
        length = int(self.headers.get("Content-Length") or 0)
        return json.loads(self.rfile.read(length).decode("utf-8")) if length else {}

    # ---- 文件看板接口 ----

    def _json_code(self, code, obj):
        body = json.dumps(obj, ensure_ascii=False).encode("utf-8")
        self.send_response(code)
        self.send_header("Content-Type", "application/json; charset=utf-8")
        self.send_header("Cache-Control", "no-store")
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def _token_ok(self):
        q = parse_qs(self.path.split("?", 1)[1], keep_blank_values=True) if "?" in self.path else {}
        supplied = (q.get("k") or [None])[0]
        src = 'query' if supplied else None
        if not supplied:
            supplied = self.headers.get("X-KD-Token")
            src = 'header' if supplied else None
        if not supplied:
            m = re.search(r'(?:^|;\s*)kd_token=([0-9a-fA-F]+)', self.headers.get("Cookie") or "")
            if m:
                supplied, src = m.group(1), 'cookie'
        try:
            if supplied and secrets.compare_digest(str(supplied), FILE_TOKEN):
                self._kd_tsrc = src
                return True
        except TypeError:
            pass
        return False

    def _kd_cookie(self):
        """令牌经查询参数/header 提供时，回种 HttpOnly Cookie：
        供反代页面内 iframe/子请求（无法带自定义 header）自动携带凭证。"""
        if getattr(self, '_kd_tsrc', '') == 'cookie':
            return None
        return f"kd_token={FILE_TOKEN}; Path=/; Max-Age=31536000; HttpOnly; SameSite=Lax"

    def _file_guard(self, raw, want="any"):
        """令牌 + 路径 + 黑名单统一前置校验。通过返回 (p, root)，失败已回复并返回 None。"""
        if not self._token_ok():
            self._json_code(401, {"error": "unauthorized"})
            return None
        got = resolve_file_path(raw)
        if got is None:
            self._json_code(403, {"error": "forbidden"})
            return None
        p, root = got
        if is_sensitive(p):
            self._json_code(403, {"error": "forbidden"})
            return None
        if want == "dir" and not os.path.isdir(p):
            self._json_code(400, {"error": "not a directory"})
            return None
        if want == "file" and not os.path.isfile(p):
            self._json_code(400, {"error": "not a file"})
            return None
        return p, root

    def file_list(self, qs):
        got = self._file_guard((qs.get("path") or [""])[0], want="dir")
        if not got:
            return
        try:
            self._json_reply(file_list_data(got[0], got[1]))
        except OSError:
            self._json_code(500, {"error": "list failed"})

    def file_read(self, qs):
        got = self._file_guard((qs.get("path") or [""])[0], want="file")
        if not got:
            return
        try:
            self._json_reply(file_read_data(got[0]))
        except OSError:
            self._json_code(500, {"error": "read failed"})

    def file_write(self):
        if not self._token_ok():
            self._json_code(401, {"error": "unauthorized"})
            return
        try:
            req = self._read_body()
        except ValueError:
            self._json_code(400, {"error": "bad request"})
            return
        if not isinstance(req, dict):
            self._json_code(400, {"error": "bad request"})
            return
        got = self._file_guard(req.get("path") or "", want="file")
        if not got:
            return
        p = got[0]
        content = req.get("content")
        if not isinstance(content, str):
            self._json_code(400, {"error": "content must be string"})
            return
        if len(content.encode("utf-8", errors="replace")) > WRITE_MAX:
            self._json_code(413, {"error": "too large"})
            return
        enc = req.get("encoding") if req.get("encoding") in ("utf-8", "gbk") else "utf-8"
        try:
            data = content.encode(enc)
        except (UnicodeEncodeError, LookupError):
            self._json_code(400, {"error": "encode failed"})
            return
        try:
            cur = int(os.stat(p).st_mtime * 1000)
        except OSError:
            self._json_code(404, {"error": "file gone"})
            return
        base = int(req.get("baseMtime") or 0)
        if base and cur != base and not req.get("force"):
            self._json_reply({"ok": False, "reason": "conflict", "mtime": cur})
            return
        try:
            with open(p, "wb") as f:
                f.write(data)
            new = int(os.stat(p).st_mtime * 1000)
        except OSError:
            self._json_code(500, {"error": "write failed"})
            return
        self._json_reply({"ok": True, "mtime": new})

    def file_raw(self, qs):
        got = self._file_guard((qs.get("path") or [""])[0], want="file")
        if not got:
            return
        p = got[0]
        dl = (qs.get("dl") or [""])[0] == "1"
        try:
            size = os.stat(p).st_size
        except OSError:
            self._json_code(404, {"error": "file gone"})
            return
        if not dl and size > RAW_PREVIEW_MAX:
            self._json_code(413, {"error": "too large for preview", "size": size})
            return
        ext = os.path.splitext(p)[1].lower()
        ctype = RAW_TYPES.get(ext)
        if ctype is None:
            ctype = "text/plain; charset=utf-8" if ext in TEXT_EXTS else "application/octet-stream"
        if ext in (".html", ".htm") and not dl:
            ctype = "text/plain; charset=utf-8"  # 预览不执行文件内嵌脚本
        self.send_response(200)
        self.send_header("Content-Type", ctype)
        if dl:
            self.send_header("Content-Disposition",
                             "attachment; filename*=UTF-8''" + quote(os.path.basename(p)))
        self.send_header("Content-Length", str(size))
        self.send_header("Cache-Control", "no-store")
        self.end_headers()
        try:
            with open(p, "rb") as f:
                while True:
                    chunk = f.read(1 << 20)
                    if not chunk:
                        break
                    self.wfile.write(chunk)
        except (BrokenPipeError, ConnectionResetError):
            pass

    def file_convert(self, qs):
        """Word 系文档 → HTML（macOS textutil，保真度较高）。"""
        got = self._file_guard((qs.get("path") or [""])[0], want="file")
        if not got:
            return
        p = got[0]
        if os.path.splitext(p)[1].lower() not in CONVERT_EXTS:
            self._json_code(400, {"error": "unsupported type"})
            return
        if os.stat(p).st_size > CONVERT_MAX:
            self._json_code(413, {"error": "too large"})
            return
        try:
            r = subprocess.run(["textutil", "-convert", "html", "-stdout", p],
                               capture_output=True, timeout=15)
        except (subprocess.TimeoutExpired, OSError):
            self._json_code(500, {"error": "convert failed"})
            return
        if r.returncode != 0 or not r.stdout:
            self._json_code(500, {"error": "convert failed"})
            return
        self.send_response(200)
        self.send_header("Content-Type", "text/html; charset=utf-8")
        self.send_header("Content-Length", str(len(r.stdout)))
        self.send_header("Cache-Control", "no-store")
        self.end_headers()
        self.wfile.write(r.stdout)

    def file_pptx(self, qs):
        got = self._file_guard((qs.get("path") or [""])[0], want="file")
        if not got:
            return
        p = got[0]
        if os.path.splitext(p)[1].lower() != ".pptx":
            self._json_code(400, {"error": "not a pptx"})
            return
        try:
            self._json_reply(pptx_outline_data(p))
        except (zipfile.BadZipFile, OSError, KeyError):
            self._json_code(500, {"error": "parse failed"})

    def file_thumb(self, qs):
        """Quick Look 首页缩略图（ppt/pages/key/numbers 等兜底）。"""
        got = self._file_guard((qs.get("path") or [""])[0], want="file")
        if not got:
            return
        p = got[0]
        if os.stat(p).st_size > THUMB_MAX:
            self._json_code(413, {"error": "too large"})
            return
        with tempfile.TemporaryDirectory() as td:
            try:
                r = subprocess.run(["qlmanage", "-t", "-s", "1200", "-o", td, p],
                                   capture_output=True, timeout=15)
            except (subprocess.TimeoutExpired, OSError):
                self._json_code(415, {"error": "thumbnail failed"})
                return
            pngs = [f for f in os.listdir(td) if f.endswith(".png")]
            if r.returncode != 0 or not pngs:
                self._json_code(415, {"error": "thumbnail failed"})
                return
            try:
                body = (Path(td) / pngs[0]).read_bytes()
            except OSError:
                self._json_code(415, {"error": "thumbnail failed"})
                return
        self.send_response(200)
        self.send_header("Content-Type", "image/png")
        self.send_header("Content-Length", str(len(body)))
        self.send_header("Cache-Control", "no-store")
        self.end_headers()
        self.wfile.write(body)

    # ---- kimi web 反代：透传非看板路由，配合 iframe 同源 ----
    def _proxy_kimi_web(self, method):
        if not self._token_ok():
            self._json_code(401, {"error": "unauthorized"})
            return
        length = int(self.headers.get("Content-Length") or 0)
        body = self.rfile.read(length) if length else None
        req = urllib.request.Request(KIMI_WEB_LOCAL + self.path, data=body, method=method)
        for h in ("Cookie", "Authorization", "Content-Type", "Accept", "Accept-Encoding",
                  "Origin", "Referer", "User-Agent"):
            v = self.headers.get(h)
            if v:
                req.add_header(h, v)
        try:
            with _proxy_opener.open(req, timeout=60) as r:
                self._relay_response(r.status, r.headers, r.read())
        except urllib.error.HTTPError as e:
            self._relay_response(e.code, e.headers, e.read())
        except Exception:
            self.send_error(502, "kimi web unavailable")

    def _relay_response(self, status, headers, rbody):
        self.send_response(status)
        for k, v in headers.items():
            if k.lower() not in PROXY_SKIP_HEADERS:
                self.send_header(k, v)
        ck = self._kd_cookie()
        if ck:
            self.send_header("Set-Cookie", ck)
        self.send_header("Content-Length", str(len(rbody)))
        self.end_headers()
        try:
            self.wfile.write(rbody)
        except (BrokenPipeError, ConnectionResetError):
            pass

    def _tunnel_ws(self):
        """WebSocket 升级请求：原始 TCP 双向转发（urllib 不支持 101 中间态）。"""
        if not self._token_ok():
            self.send_error(401, "unauthorized")
            return
        try:
            backend = socket.create_connection((KIMI_WEB_HOST, KIMI_WEB_PORT), timeout=10)
        except OSError:
            self.send_error(502, "kimi web unavailable")
            return
        try:
            head = [f"{self.command} {self.path} HTTP/1.1"]
            for k, v in self.headers.items():
                if k.lower() == "host":
                    v = KIMI_WEB_HOSTPORT
                head.append(f"{k}: {v}")
            backend.sendall(("\r\n".join(head) + "\r\n\r\n").encode())
        except OSError:
            backend.close()
            return

        def pump(src, dst):
            try:
                while True:
                    d = src.recv(65536)
                    if not d:
                        break
                    dst.sendall(d)
            except OSError:
                pass
            try:
                dst.shutdown(socket.SHUT_WR)
            except OSError:
                pass

        threading.Thread(target=pump, args=(self.connection, backend), daemon=True).start()
        pump(backend, self.connection)   # 阻塞当前 handler 线程直到任一侧断开
        try:
            backend.close()
        except OSError:
            pass

    def do_POST(self):
        url = self.path.split("?")[0]
        if url == "/kd/term/open":
            if not self._token_ok():
                self._json_code(401, {"error": "unauthorized"})
                return
            try:
                req = self._read_body()
            except ValueError:
                self._json_code(400, {"error": "bad request"})
                return
            ts, err = _term_open((req.get("cwd") or ""))
            if err:
                self._json_code(403 if err == "forbidden" else 400, {"error": err})
                return
            self._json_reply({"ts": ts})
            return
        if url == "/kd/term/in":
            if not self._token_ok():
                self._json_code(401, {"error": "unauthorized"})
                return
            try:
                req = self._read_body()
            except ValueError:
                self._json_code(400, {"error": "bad request"})
                return
            t = TERMS.get(req.get("ts") or "")
            data = req.get("data")
            if not t or not t['alive'] or not isinstance(data, str):
                self._json_code(404, {"error": "no terminal"})
                return
            try:
                os.write(t['fd'], data.encode('utf-8'))
            except OSError:
                self._json_code(404, {"error": "pty gone"})
                return
            self._json_reply({"ok": True})
            return
        if url == "/kd/term/size":
            if not self._token_ok():
                self._json_code(401, {"error": "unauthorized"})
                return
            try:
                req = self._read_body()
            except ValueError:
                self._json_code(400, {"error": "bad request"})
                return
            t = TERMS.get(req.get("ts") or "")
            cols, rows = int(req.get("cols") or 0), int(req.get("rows") or 0)
            if not t or cols <= 0 or rows <= 0:
                self._json_code(400, {"error": "bad request"})
                return
            try:
                fcntl.ioctl(t['fd'], termios.TIOCSWINSZ, struct.pack('HHHH', rows, cols, 0, 0))
            except OSError:
                self._json_code(404, {"error": "pty gone"})
                return
            self._json_reply({"ok": True})
            return
        if url == "/kd/term/close":
            if not self._token_ok():
                self._json_code(401, {"error": "unauthorized"})
                return
            try:
                req = self._read_body()
            except ValueError:
                self._json_code(400, {"error": "bad request"})
                return
            _term_kill(req.get("ts") or "")
            self._json_reply({"ok": True})
            return
        if url == "/kd/file/write":
            self.file_write()
            return
        if url == "/kd/seen":
            if not self._token_ok():
                self._json_code(401, {"error": "unauthorized"})
                return
            ok = False
            try:
                req = self._read_body()
                sid = (req.get("sessionId") or "").strip()
                if sid and sid.startswith("session_"):
                    seen_map[sid] = int(time.time() * 1000)
                    save_seen()
                    _scan_cache["ts"] = 0  # 作废扫描缓存：下一轮 SSE 立即重算并推送状态变化
                    ok = True
            except Exception:
                traceback.print_exc()
            self._json_reply({"ok": ok})
            return
        if url == "/kd/todo/add":
            if not self._token_ok():
                self._json_code(401, {"error": "unauthorized"})
                return
            ok, reason = False, ""
            try:
                req = self._read_body()
                title = (req.get("title") or "").strip()
                if title:
                    ok, reason = add_kb_todo(title)
            except Exception:
                traceback.print_exc()
            self._json_reply({"ok": ok, "reason": reason})
            return
        if url == "/kd/todo/done":
            if not self._token_ok():
                self._json_code(401, {"error": "unauthorized"})
                return
            ok = False
            try:
                req = self._read_body()
                title = (req.get("title") or "").strip()
                target = bool(req.get("done", True))
                if title:
                    ok = set_kb_todo_state(title, target)
                if ok:
                    for it in todos_cache.get("items", []):
                        if it.get("title") == title:
                            it["done"] = target
            except Exception:
                traceback.print_exc()
            self._json_reply({"ok": bool(ok)})
            return
        self._proxy_kimi_web("POST")

    def do_GET(self):
        url = self.path.split("?")[0]
        if url.startswith("/kd/file/"):
            action = url[len("/kd/file/"):]
            if action.startswith("raw/"):
                action = "raw"   # /kd/file/raw/<文件名> 别名：旧客户端从 URL 末段取名字
            qs = parse_qs(self.path.split("?", 1)[1], keep_blank_values=True) if "?" in self.path else {}
            if action == "list":
                self.file_list(qs)
            elif action == "read":
                self.file_read(qs)
            elif action == "raw":
                self.file_raw(qs)
            elif action == "convert":
                self.file_convert(qs)
            elif action == "pptx":
                self.file_pptx(qs)
            elif action == "thumb":
                self.file_thumb(qs)
            else:
                self.send_error(404)
            return
        if url.startswith("/vendor/"):
            name = url[len("/vendor/"):]
            fp = VENDOR_DIR / name if VENDOR_NAME_RE.match(name) else None
            if fp is None or not fp.is_file():
                self.send_error(404)
                return
            body = fp.read_bytes()
            ctype = {".js": "application/javascript; charset=utf-8",
                     ".css": "text/css; charset=utf-8"}.get(fp.suffix.lower(),
                                                            "application/octet-stream")
            self.send_response(200)
            self.send_header("Content-Type", ctype)
            self.send_header("Content-Length", str(len(body)))
            self.send_header("Cache-Control", "public, max-age=604800")
            self.end_headers()
            self.wfile.write(body)
            return
        if url == "/kd/term/out":
            if not self._token_ok():
                self._json_code(401, {"error": "unauthorized"})
                return
            qs = parse_qs(self.path.split("?", 1)[1], keep_blank_values=True) if "?" in self.path else {}
            ts = (qs.get("ts") or [""])[0]
            try:
                since = int((qs.get("since") or ["0"])[0] or 0)
            except ValueError:
                since = 0
            t = TERMS.get(ts)
            if not t:
                self._json_reply({"ts": ts, "out": "", "alive": False, "total": 0})
                return
            with t['lock']:
                buf, total, alive = t['buf'], t['total'], t['alive']
            t['last_poll'] = time.time()
            start_abs = max(since, total - len(buf))
            out = buf[start_abs - (total - len(buf)):]
            self._json_reply({"ts": ts, "out": out, "alive": alive, "total": total, "exit": t.get('exit', -1)})
            return
        if url == "/kd/state":
            if not self._token_ok():
                self._json_code(401, {"error": "unauthorized"})
                return
            try:
                data = scan_sessions()
            except Exception:
                traceback.print_exc()
                self.send_error(500, "scan failed")
                return
            body = json.dumps(data, ensure_ascii=False).encode("utf-8")
            self.send_response(200)
            self.send_header("Content-Type", "application/json; charset=utf-8")
            self.send_header("Cache-Control", "no-store")
            ck = self._kd_cookie()
            if ck:
                self.send_header("Set-Cookie", ck)
            self.send_header("Content-Length", str(len(body)))
            self.end_headers()
            self.wfile.write(body)
            return
        if url == "/kd/stream":
            if not self._token_ok():
                self._json_code(401, {"error": "unauthorized"})
                return
            self.send_response(200)
            self.send_header("Content-Type", "text/event-stream; charset=utf-8")
            self.send_header("Cache-Control", "no-store")
            ck = self._kd_cookie()
            if ck:
                self.send_header("Set-Cookie", ck)
            self.end_headers()
            last_sig = None
            last_push = 0.0
            try:
                while True:
                    data = scan_sessions()
                    sig = state_signature(data)
                    now_s = time.time()
                    if sig != last_sig and now_s - last_push >= 1.0:
                        last_sig = sig
                        last_push = now_s
                        body = json.dumps(data, ensure_ascii=False)
                        self.wfile.write(f"data: {body}\n\n".encode("utf-8"))
                    else:
                        self.wfile.write(b": ping\n\n")  # 心跳防超时
                    self.wfile.flush()
                    time.sleep(1)
            except (BrokenPipeError, ConnectionResetError):
                return
            except Exception:
                return
        if url in ("/manifest.webmanifest", "/icon-192.png", "/icon-512.png"):
            fp = PUBLIC_DIR / url.lstrip("/")
            try:
                body = fp.read_bytes()
            except OSError:
                self.send_error(404)
                return
            ctype = "application/manifest+json" if url.endswith(".webmanifest") else ("text/html; charset=utf-8" if url.endswith(".html") else "image/png")
            self.send_response(200)
            self.send_header("Content-Type", ctype)
            self.send_header("Cache-Control", "no-store" if url.endswith(".html") else "public, max-age=3600")
            self.send_header("Content-Length", str(len(body)))
            self.end_headers()
            self.wfile.write(body)
            return
        if url in ("/", "/index.html"):
            try:
                body = (PUBLIC_DIR / "index.html").read_bytes()
                ver = str(int((PUBLIC_DIR / "index.html").stat().st_mtime * 1000)).encode()
                body = body.replace(b"__PAGE_VER__", ver)
            except OSError:
                self.send_error(500, "index.html missing")
                return
            self.send_response(200)
            self.send_header("Content-Type", "text/html; charset=utf-8")
            self.send_header("Cache-Control", "no-store")
            self.send_header("Content-Length", str(len(body)))
            self.end_headers()
            self.wfile.write(body)
            return
        if self.headers.get("Upgrade") or self.headers.get("Sec-WebSocket-Key"):
            self._tunnel_ws()
            return
        self._proxy_kimi_web("GET")

    def do_PUT(self):
        self._proxy_kimi_web("PUT")

    def do_DELETE(self):
        self._proxy_kimi_web("DELETE")

    def do_PATCH(self):
        self._proxy_kimi_web("PATCH")

    def log_message(self, fmt, *args):
        pass  # 静默访问日志


if __name__ == "__main__":
    faulthandler.register(signal.SIGUSR1)  # kill -USR1 <pid> 转储所有线程栈（调试用）
    # 启动时后台预热缓存 + 待拉取钉钉待办
    threading.Thread(target=scan_sessions, daemon=True).start()
    threading.Thread(target=todo_worker, daemon=True).start()
    threading.Thread(target=notify_worker, daemon=True).start()
    threading.Thread(target=sys_worker, daemon=True).start()
    server = ThreadingHTTPServer(("127.0.0.1", PORT), Handler)
    print(f"Kimi Code 会话看板: http://127.0.0.1:{PORT}")
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        pass
