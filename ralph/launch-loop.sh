#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
STAMP="$(date +%Y%m%d-%H%M%S)"
LOG="$ROOT/ralph/run-$STAMP.log"
PIDFILE="$ROOT/ralph/run.pid"
RUNNER="/Users/alokbeniwal/.codex/skills/ralph-loop/scripts/ralph-loop.py"

cd "$ROOT"

nohup /opt/homebrew/bin/gtimeout 10h \
  uv run python "$RUNNER" \
    --runner codex \
    --iterations 9999 \
    --sleep 15 \
    --prd ralph/PRD.md \
    --progress ralph/progress.txt \
    --extra "Focus on importing existing ACL2 proofs and replaying them in Lean so Lean's kernel is the checker. Use the ACL proof-mode UI as a feedback surface, but prioritize actual imported theorem replay over UI polish. Push useful commits to the current branch as you go. Do not wait for the user." \
  >"$LOG" 2>&1 &

echo $! >"$PIDFILE"
echo "Started Ralph loop"
echo "pid: $(cat "$PIDFILE")"
echo "log: $LOG"
