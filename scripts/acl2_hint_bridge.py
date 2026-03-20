#!/usr/bin/env python3

import argparse
from dataclasses import dataclass
from functools import lru_cache
import json
import os
import re
import shutil
import subprocess
import sys
from pathlib import Path


THEOREM_FORM_RE = re.compile(r"Form:\s+\(\s*DEFTHM\s+([^\s)]+)", re.IGNORECASE)
ACL2_ERROR_RE = re.compile(r"^ACL2 Error\b")
FAILED_MARKER = "******** FAILED ********"
GOAL_LINE_RE = re.compile(r"^Goal(?:'+)?$")
SUBGOAL_LINE_RE = re.compile(r"^Subgoal\b.+$")
PROMPT_RE = re.compile(r"^[^()\s]+\s+!>+")


def normalize_name(name: str) -> str:
    return name.strip().lower()


@dataclass(frozen=True)
class LoadPlan:
    requested_book: str
    book: Path
    preludes: tuple[Path, ...] = ()
    note: str = ""

    def script(self) -> str:
        lines = [f'(ld "{step.as_posix()}")' for step in self.preludes]
        lines.append(f'(ld "{self.book.as_posix()}")')
        lines.append("(quit)")
        return "\n".join(lines) + "\n"

    def load_steps(self) -> list[str]:
        return [str(step) for step in (*self.preludes, self.book)]


def run_acl2(plan: LoadPlan) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        ["acl2"],
        input=plan.script(),
        text=True,
        capture_output=True,
        check=False,
    )


@lru_cache(maxsize=1)
def find_system_books_root() -> Path | None:
    for env_var in ("ACL2_SYSTEM_BOOKS", "ACL2_BOOKS"):
        value = os.environ.get(env_var)
        if value:
            candidate = Path(value).expanduser()
            if candidate.exists():
                return candidate.resolve()

    acl2_path = shutil.which("acl2")
    if acl2_path:
        resolved_acl2 = Path(acl2_path).resolve()
        for parent in resolved_acl2.parents:
            candidate = parent / "libexec" / "books"
            if candidate.exists():
                return candidate

    for cellar_root in (Path("/opt/homebrew/Cellar/acl2"), Path("/usr/local/Cellar/acl2")):
        if cellar_root.exists():
            matches = sorted(cellar_root.glob("*/libexec/books"))
            if matches:
                return matches[-1]

    for candidate in (Path("/usr/share/acl2/books"), Path("/usr/local/share/acl2/books")):
        if candidate.exists():
            return candidate

    return None


def maybe_add_plan(
    plans: list[LoadPlan],
    requested_book: str,
    book: Path,
    *,
    preludes: tuple[Path, ...] = (),
    note: str = "",
) -> None:
    if not book.exists():
        return
    if any(not prelude.exists() for prelude in preludes):
        return
    plans.append(LoadPlan(requested_book=requested_book, book=book, preludes=preludes, note=note))


def fallback_plans(requested_book: str, requested_path: Path, system_root: Path | None) -> list[LoadPlan]:
    if system_root is None:
        return []

    requested_posix = requested_path.as_posix()
    plans: list[LoadPlan] = []

    if requested_posix.endswith("acl2_samples/die-hard-work.lisp"):
        maybe_add_plan(
            plans,
            requested_book,
            system_root / "projects" / "die-hard-bottle-game" / "work.lisp",
            note="canonical upstream book for excerpted die-hard sample",
        )

    if requested_posix.endswith("acl2_samples/die-hard-top.lisp"):
        maybe_add_plan(
            plans,
            requested_book,
            system_root / "projects" / "die-hard-bottle-game" / "top.lisp",
            note="canonical upstream book for excerpted die-hard top-level sample",
        )

    if requested_posix.endswith("acl2_samples/apply-model-apply-prim.lisp"):
        primary_portcullis = system_root / "projects" / "apply-model" / "portcullis.acl2"
        maybe_add_plan(
            plans,
            requested_book,
            requested_path,
            preludes=(primary_portcullis,),
            note="repo sample loaded with upstream MODAPP portcullis",
        )
        maybe_add_plan(
            plans,
            requested_book,
            system_root / "projects" / "apply-model" / "apply-prim.lisp",
            preludes=(primary_portcullis,),
            note="canonical upstream apply-model book with MODAPP portcullis",
        )

        alt_portcullis = system_root / "projects" / "apply-model-2" / "portcullis.acl2"
        maybe_add_plan(
            plans,
            requested_book,
            system_root / "projects" / "apply-model-2" / "apply-prim.lisp",
            preludes=(alt_portcullis,),
            note="alternate upstream apply-model-2 book with MODAPP portcullis",
        )

    if requested_posix.endswith("acl2_samples/apply-model-apply.lisp"):
        primary_portcullis = system_root / "projects" / "apply-model" / "portcullis.acl2"
        maybe_add_plan(
            plans,
            requested_book,
            requested_path,
            preludes=(primary_portcullis,),
            note="repo sample loaded with upstream MODAPP portcullis",
        )
        maybe_add_plan(
            plans,
            requested_book,
            system_root / "projects" / "apply-model" / "apply.lisp",
            preludes=(primary_portcullis,),
            note="canonical upstream apply-model book with MODAPP portcullis",
        )

    return plans


def resolve_load_plans(book: str, system_root: Path | None = None) -> list[LoadPlan]:
    requested_path = Path(book).expanduser()
    if not requested_path.is_absolute():
        requested_path = (Path.cwd() / requested_path).resolve()
    else:
        requested_path = requested_path.resolve()

    plans = [LoadPlan(requested_book=book, book=requested_path, note="requested book")]
    plans.extend(fallback_plans(book, requested_path, system_root or find_system_books_root()))

    deduped: list[LoadPlan] = []
    seen: set[tuple[str, tuple[str, ...]]] = set()
    for plan in plans:
        key = (str(plan.book), tuple(str(step) for step in plan.preludes))
        if key in seen:
            continue
        seen.add(key)
        deduped.append(plan)
    return deduped


def previous_prompt_index(lines: list[str], idx: int) -> int:
    for j in range(idx, -1, -1):
        if PROMPT_RE.match(lines[j].lstrip()):
            return j
    return 0


def next_prompt_index(lines: list[str], idx: int) -> int:
    for j in range(idx + 1, len(lines)):
        if PROMPT_RE.match(lines[j].lstrip()):
            return j
    return len(lines)


def previous_summary_index(lines: list[str], idx: int, lower_bound: int = 0) -> int | None:
    for j in range(idx, lower_bound - 1, -1):
        if lines[j].strip() == "Summary":
            return j
    return None


def theorem_summary_end(lines: list[str], summary_idx: int, theorem_name: str) -> int:
    for j in range(summary_idx + 1, len(lines)):
        stripped = lines[j].strip()
        if stripped == theorem_name:
            return j + 1
        if PROMPT_RE.match(lines[j].lstrip()):
            return j
    return len(lines)


def theorem_excerpt(
    lines: list[str],
    matches: list[tuple[int, str]],
    match_idx: int,
) -> list[str]:
    form_idx, theorem_name = matches[match_idx]
    prompt_start = previous_prompt_index(lines, form_idx)
    summary_idx = previous_summary_index(lines, form_idx, prompt_start)
    if summary_idx is None:
        summary_idx = form_idx

    start = prompt_start
    if match_idx > 0:
        prev_form_idx, prev_theorem_name = matches[match_idx - 1]
        prev_prompt_start = previous_prompt_index(lines, prev_form_idx)
        prev_summary_idx = previous_summary_index(lines, prev_form_idx, prev_prompt_start)
        if prev_summary_idx is not None:
            start = max(start, theorem_summary_end(lines, prev_summary_idx, prev_theorem_name))

    end = theorem_summary_end(lines, summary_idx, theorem_name)
    return [line.rstrip("\n") for line in lines[start:end]]


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
                blocks.append({"kind": "key-checkpoint", "label": first, "text": body})
            i = j
        i += 1
    return blocks


def collect_trace_checkpoints(lines: list[str], known_labels: set[str]) -> list[dict[str, str]]:
    checkpoints: list[dict[str, str]] = []
    seen = set(known_labels)
    for raw_line in lines:
        line = raw_line.strip()
        if not line or line == "Summary":
            continue
        kind: str | None = None
        if GOAL_LINE_RE.fullmatch(line):
            kind = "goal"
        elif SUBGOAL_LINE_RE.fullmatch(line):
            kind = "subgoal"
        else:
            continue
        if line in seen:
            continue
        seen.add(line)
        checkpoints.append({"kind": kind, "label": line, "text": line})
    return checkpoints


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


def detect_acl2_failure(lines: list[str]) -> str | None:
    for line in lines:
        stripped = line.strip()
        if ACL2_ERROR_RE.match(stripped):
            return stripped
        if FAILED_MARKER in stripped:
            return FAILED_MARKER
    return None


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
        if line.strip() == theorem_name or PROMPT_RE.match(line.lstrip()):
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
    all_matches: list[tuple[int, str]] = []
    for idx, line in enumerate(lines):
        match = THEOREM_FORM_RE.search(line)
        if match:
            all_matches.append((idx, match.group(1)))

    target_match_idx: int | None = None
    for i, (_, theorem_name) in enumerate(all_matches):
        if normalize_name(theorem_name) == theorem_norm:
            target_match_idx = i
            break

    if target_match_idx is None:
        failure = detect_acl2_failure(lines)
        return {
            "status": "failed" if failure else "not-found",
            "requested_theorem": theorem,
            "theorem_name": theorem,
            "summary_form": failure or "",
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
            "raw_excerpt": [line.rstrip("\n") for line in lines[-80:]],
        }

    idx, theorem_name = all_matches[target_match_idx]
    excerpt = theorem_excerpt(lines, all_matches, target_match_idx)
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
        "checkpoints": (
            lambda explicit: explicit + collect_trace_checkpoints(
                excerpt, {checkpoint["label"] for checkpoint in explicit}
            )
        )(collect_checkpoint_blocks(excerpt)),
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
    best_artifact: dict[str, object] | None = None
    best_rank = -1

    status_rank = {"proved": 3, "not-found": 2, "failed": 1}

    for plan in resolve_load_plans(book):
        proc = run_acl2(plan)
        stdout_lines = proc.stdout.splitlines()
        artifact = theorem_section(stdout_lines, args.theorem)
        artifact["book"] = book
        artifact["resolved_book"] = str(plan.book)
        artifact["load_steps"] = plan.load_steps()
        artifact["load_note"] = plan.note
        artifact["exit_code"] = proc.returncode
        artifact["stderr"] = proc.stderr.strip()

        rank = status_rank.get(str(artifact["status"]), 0)
        if rank > best_rank:
            best_artifact = artifact
            best_rank = rank
        if artifact["status"] == "proved":
            break

    if best_artifact is None:
        raise RuntimeError("expected at least one ACL2 load plan")

    json.dump(best_artifact, sys.stdout, indent=2)
    sys.stdout.write("\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
