# Kimi Code 会话看板

[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](LICENSE)

监控本机 kimi-code CLI 所有会话的运行状态与当日 token 消耗，纯只读扫描 `~/.kimi-code`，零依赖（Python 标准库）。
另含**文件看板**：浏览各会话工作空间（cwd 项目目录）的文件，支持预览（文本/Markdown/图片/PDF）、编辑文本文件、下载。

## 启动

```bash
python3 server.py          # 默认 http://127.0.0.1:7788
PORT=8888 python3 server.py
```

浏览器打开 <http://127.0.0.1:7788>，页面每 3 秒自动刷新；`?view=files` 直达文件看板。

## 功能

- **待确认**：有未决审批请求的会话（含工具名、操作内容、等待时长）；超过 5 分钟无动静标记为僵死（stale）
- **运行中**：wire.jsonl 最近 60 秒内有写入的会话（显示当前任务、累计 token）
- **空闲**：48 小时内活动过的历史会话
- **今日 Token**：按 输入 / 缓存读 / 输出 分项统计，并按模型分布
- **文件看板**：按工作空间浏览文件；预览覆盖 文本(语法高亮)/Markdown/HTML/图片/
  **PDF(pdf.js 渲染)**/Excel/Word/PPT(pptx 文本大纲、ppt 首页缩略图)；
  文本编辑（带并发冲突检测），下载。
  首次使用需输入访问令牌：服务首次启动时自动生成 `.filetoken`，终端执行 `cat .filetoken` 获取

## 实现

- `server.py`：扫描 `~/.kimi-code/sessions/wd_*/session_*/agents/*/wire.jsonl`
  - 增量偏移缓存，只解析新增字节；启动时后台预热（首次冷扫描约 20s，之后每次 <100ms）
  - `GET /kd/state` 返回 JSON；token 来自 `usage.record`，待确认来自 `interaction.request` 减 `interaction.resolved`
  - 文件接口 `/kd/file/list|read|write|raw`：仅限当前会话 cwd 目录内，需访问令牌（`.filetoken`）
- `public/index.html`：单文件前端，深色主题三列看板 + 文件看板双视图

