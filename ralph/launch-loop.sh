#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
STAMP="$(date +%Y%m%d-%H%M%S)"
LOG="$ROOT/ralph/run-$STAMP.log"
PIDFILE="$ROOT/ralph/run.pid"
RUNNER="/Users/alokbeniwal/.codex/skills/ralph-loop/scripts/ralph-loop.py"

cd "$ROOT"

nohup env PYTHONUNBUFFERED=1 /opt/homebrew/bin/gtimeout 10h \
  uv run python "$RUNNER" \
    --runner codex \
    --iterations 9999 \
    --sleep 15 \
    --prd ralph/PRD.md \
    --progress ralph/progress.txt \
    --extra "Operate autonomously for the full 10-hour budget. Keep importing and replaying ACL2 proofs in Lean as the north star, but do not scope yourself so tightly that you finish early. If one line of attack blocks, immediately pivot to the next highest-leverage task across proof extraction, replay infrastructure, translator/import work, proving support, evaluator semantics, UI, or source research. Push useful commits to the current branch as you go. Do not wait for the user." \
  >"$LOG" 2>&1 &

echo $! >"$PIDFILE"
echo "Started Ralph loop"
echo "pid: $(cat "$PIDFILE")"
echo "log: $LOG"
