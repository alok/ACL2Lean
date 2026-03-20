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


def collect_prefixed_blocks(lines: list[str], prefix: str) -> list[str]:
    blocks: list[str] = []
    i = 0
    while i < len(lines):
        if lines[i].startswith(prefix):
            block = [lines[i].rstrip()]
            j = i + 1
            while j < len(lines) and lines[j].strip():
                block.append(lines[j].rstrip())
                j += 1
            blocks.append("\n".join(block).strip())
            i = j
        i += 1
    return blocks


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


def summary_field(line: str) -> tuple[str, str] | None:
    fixed_prefixes = {
        "Form:": "summary_form",
        "Rules:": "summary_rules",
        "Hint-events:": "hint_events",
        "Warnings:": "warning_kinds",
        "Time:": "summary_time",
        "Prover steps counted:": "prover_steps",
    }
    for prefix, field in fixed_prefixes.items():
        if line.startswith(prefix):
            return field, line[len(prefix) :].strip()
    if line.startswith("Splitter rules"):
        _, _, rest = line.rpartition(":")
        return "splitter_rules", rest.strip()
    return None


def normalize_summary_entries(text: str) -> list[str]:
    stripped = text.strip()
    if not stripped or stripped == "NIL":
        return []
    lines = [line.strip() for line in stripped.splitlines() if line.strip()]
    if not lines:
        return []
    first = lines[0]
    if first.startswith("(("):
        lines[0] = "(" + first[2:]
    last = lines[-1]
    if last.endswith("))"):
        lines[-1] = last[:-2] + ")"
    return lines


def parse_warning_kinds(text: str) -> list[str]:
    stripped = text.strip()
    if not stripped:
        return []
    normalized = re.sub(r"\s+and\s+", ",", stripped)
    return [part.strip() for part in normalized.split(",") if part.strip()]


def parse_summary(lines: list[str], theorem_name: str) -> dict[str, object]:
    summary: dict[str, object] = {
        "summary_form": "",
        "summary_rules": [],
        "hint_events": [],
        "splitter_rules": [],
        "warning_kinds": [],
        "summary_time": "",
        "prover_steps": None,
    }
    try:
        start = lines.index("Summary")
    except ValueError:
        return summary

    current_field: str | None = None
    current_lines: list[str] = []

    def flush() -> None:
        nonlocal current_field, current_lines
        if current_field is None:
            return
        text = "\n".join(line.rstrip() for line in current_lines if line is not None).strip()
        if current_field == "summary_form":
            summary[current_field] = text
        elif current_field in {"summary_rules", "hint_events"}:
            summary[current_field] = normalize_summary_entries(text)
        elif current_field == "splitter_rules":
            summary[current_field] = [line.strip() for line in text.splitlines() if line.strip()]
        elif current_field == "warning_kinds":
            summary[current_field] = parse_warning_kinds(text)
        elif current_field == "summary_time":
            summary[current_field] = text
        elif current_field == "prover_steps":
            match = re.search(r"\d+", text)
            summary[current_field] = int(match.group(0)) if match else None
        current_field = None
        current_lines = []

    for raw_line in lines[start + 1 :]:
        line = raw_line.rstrip()
        if line.strip() == theorem_name or line.startswith("ACL2 !>"):
            break
        match = summary_field(line.strip())
        if match:
            flush()
            field_name, initial = match
            current_field = field_name
            current_lines = [initial] if initial else []
            continue
        if current_field is not None:
            current_lines.append(line)

    flush()
    return summary


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
            "summary_rules": [],
            "hint_events": [],
            "splitter_rules": [],
            "warning_kinds": [],
            "summary_time": "",
            "prover_steps": None,
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
    summary = parse_summary(excerpt, theorem_name)

    return {
        "status": "proved",
        "requested_theorem": theorem,
        "theorem_name": theorem_name,
        "summary_form": summary["summary_form"] or lines[idx].strip(),
        "summary_rules": summary["summary_rules"],
        "hint_events": summary["hint_events"],
        "splitter_rules": summary["splitter_rules"],
        "warning_kinds": summary["warning_kinds"],
        "summary_time": summary["summary_time"],
        "prover_steps": summary["prover_steps"],
        "checkpoints": collect_checkpoint_blocks(excerpt),
        "observations": collect_prefixed_blocks(excerpt, "ACL2 Observation"),
        "warnings": collect_prefixed_blocks(excerpt, "ACL2 Warning"),
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
