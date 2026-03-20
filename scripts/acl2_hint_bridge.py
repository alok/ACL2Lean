#!/usr/bin/env python3

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path


THEOREM_FORM_RE = re.compile(r"Form:\s+\(\s*DEFTHM\s+([^\s)]+)", re.IGNORECASE)


def normalize_name(name: str) -> str:
    return name.strip().lower()


def run_acl2(book: str) -> subprocess.CompletedProcess[str]:
    script = f'(ld "{book}")\n(quit)\n'
    return subprocess.run(
        ["acl2"],
        input=script,
        text=True,
        capture_output=True,
        check=False,
    )


def previous_prompt_index(lines: list[str], idx: int) -> int:
    for j in range(idx, -1, -1):
        if lines[j].startswith("ACL2 !>"):
            return j
    return 0


def next_prompt_index(lines: list[str], idx: int) -> int:
    for j in range(idx + 1, len(lines)):
        if lines[j].startswith("ACL2 !>"):
            return j
    return len(lines)


def collect_checkpoint_blocks(lines: list[str]) -> list[dict[str, str]]:
    blocks: list[dict[str, str]] = []
    i = 0
    while i < len(lines):
        if "A key checkpoint:" in lines[i]:
            start = i + 1
            j = start
            while j < len(lines) and lines[j].strip() != "])":
                j += 1
            body = "\n".join(line.rstrip() for line in lines[start:j]).strip()
            if body:
                first = body.splitlines()[0].strip()
                blocks.append({"label": first, "text": body})
            i = j
        i += 1
    return blocks


def collect_prefixed(lines: list[str], prefix: str) -> list[str]:
    return [line.strip() for line in lines if line.startswith(prefix)]


def collect_induction_blocks(lines: list[str]) -> list[str]:
    blocks: list[str] = []
    i = 0
    while i < len(lines):
        if lines[i].startswith("We will induct according to"):
            block = [lines[i].rstrip()]
            j = i + 1
            while j < len(lines):
                line = lines[j].rstrip()
                if not line:
                    if j + 1 < len(lines) and not lines[j + 1].strip():
                        break
                    block.append(line)
                    j += 1
                    continue
                if line.startswith("Subgoal ") or line.startswith("*1 is COMPLETED!") or line.startswith("Q.E.D."):
                    break
                block.append(line)
                if line.startswith("When applied to the goal at hand"):
                    break
                j += 1
            blocks.append("\n".join(block).strip())
            i = j
        i += 1
    return blocks


def theorem_section(lines: list[str], theorem: str) -> dict[str, object]:
    theorem_norm = normalize_name(theorem)
    matches: list[tuple[int, str]] = []
    for idx, line in enumerate(lines):
        match = THEOREM_FORM_RE.search(line)
        if match and normalize_name(match.group(1)) == theorem_norm:
            matches.append((idx, match.group(1)))

    if not matches:
        return {
            "status": "not-found",
            "requested_theorem": theorem,
            "theorem_name": theorem,
            "summary_form": "",
            "checkpoints": [],
            "observations": [],
            "warnings": [],
            "inductions": [],
            "raw_excerpt": [],
        }

    idx, theorem_name = matches[0]
    start = previous_prompt_index(lines, idx)
    end = next_prompt_index(lines, idx)
    excerpt = [line.rstrip("\n") for line in lines[start:end]]

    return {
        "status": "proved",
        "requested_theorem": theorem,
        "theorem_name": theorem_name,
        "summary_form": lines[idx].strip(),
        "checkpoints": collect_checkpoint_blocks(excerpt),
        "observations": collect_prefixed(excerpt, "ACL2 Observation"),
        "warnings": collect_prefixed(excerpt, "ACL2 Warning"),
        "inductions": collect_induction_blocks(excerpt),
        "raw_excerpt": excerpt,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description="Extract ACL2-emitted hint/checkpoint artifacts for one theorem.")
    parser.add_argument("--book", required=True, help="Path to ACL2 book to load")
    parser.add_argument("--theorem", required=True, help="Theorem name to extract")
    args = parser.parse_args()

    book = str(Path(args.book))
    proc = run_acl2(book)
    stdout_lines = proc.stdout.splitlines()
    artifact = theorem_section(stdout_lines, args.theorem)
    artifact["book"] = book
    artifact["exit_code"] = proc.returncode
    artifact["stderr"] = proc.stderr.strip()

    json.dump(artifact, sys.stdout, indent=2)
    sys.stdout.write("\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
