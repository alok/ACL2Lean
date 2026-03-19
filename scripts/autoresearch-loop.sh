#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
STAMP="$(date +%Y%m%d-%H%M%S)"
STATE_DIR="$ROOT/.autoresearch"
LOG="$STATE_DIR/run-$STAMP.log"
PIDFILE="$STATE_DIR/run.pid"
PROMPT_FILE="$STATE_DIR/prompt.txt"

mkdir -p "$STATE_DIR"

cat >"$PROMPT_FILE" <<'EOF'
Read `program.md`, `AUTORESEARCH_PROGRESS.md`, and `results.tsv` from the repository root.

Operate in autoresearch mode. Pick one high-leverage task, complete it end-to-end, run relevant
verification, commit and push if it is a real advance, then update `AUTORESEARCH_PROGRESS.md` and
`results.tsv`.

Keep importing and replaying ACL2 proofs in Lean as the north star, but do not scope yourself so
tightly that you finish early. If one approach blocks, pivot immediately to the next most useful
task across proof extraction, replay infrastructure, translator/import work, proving support,
semantic alignment, UI, or source research.

Do not wait for user input. Continue autonomously.
EOF

nohup env PYTHONUNBUFFERED=1 /opt/homebrew/bin/gtimeout 10h bash -lc '
  set -euo pipefail
  ROOT="$1"
  PROMPT_FILE="$2"
  LOG="$3"
  cd "$ROOT"
  iter=1
  while true; do
    {
      printf "\n===== AUTORESEARCH ITERATION %s %s =====\n" "$iter" "$(date -Iseconds)"
      cat "$PROMPT_FILE" | codex exec --dangerously-bypass-approvals-and-sandbox -C "$ROOT" -
      printf "\n===== END ITERATION %s %s =====\n" "$iter" "$(date -Iseconds)"
    } >>"$LOG" 2>&1 || {
      printf "\n[autoresearch-loop] iteration %s exited non-zero at %s\n" "$iter" "$(date -Iseconds)" >>"$LOG"
    }
    iter=$((iter + 1))
    sleep 15
  done
' _ "$ROOT" "$PROMPT_FILE" "$LOG" >/dev/null 2>&1 &

echo $! >"$PIDFILE"
echo "Started autoresearch loop"
echo "pid: $(cat "$PIDFILE")"
echo "log: $LOG"
