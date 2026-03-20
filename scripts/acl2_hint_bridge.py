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
PROMPT_PREFIX_RE = re.compile(r"^([^()\s]+\s+!>+)(.*)$")
HINT_EVENT_RE = re.compile(r"^\(\s*:([A-Z0-9-]+)\s+(.+?)\)$", re.IGNORECASE)
RULE_RUNE_RE = re.compile(r"^\(\s*:([A-Z0-9-]+)\s+(.+?)\s*\)$", re.IGNORECASE)
DISABLE_HINT_RE = re.compile(
    r"consider disabling\s+(\(.*?\))\s+in the hint provided for\s+([^.]+)\.",
    re.IGNORECASE,
)
SUBSUME_NEW_OVER_OLD_RE = re.compile(
    r"generated from\s+([^\s,]+)\s+probably subsumes the previously added\s+:REWRITE rule\s+([^\s,]+)",
    re.IGNORECASE,
)
SUBSUME_OLD_OVER_NEW_RE = re.compile(
    r"previously added rule\s+([^\s,]+)\s+subsumes a newly proposed\s+:REWRITE rule generated from\s+([^\s,]+)",
    re.IGNORECASE,
)
INDUCTION_TERM_RE = re.compile(
    r"We will induct according to a scheme suggested by\s+(.+?)\.",
    re.IGNORECASE,
)
INDUCTION_RULE_RE = re.compile(r":induction rule\s+([^\s.]+)", re.IGNORECASE)
TYPED_TERM_RE = re.compile(
    r"Our heuristics choose\s+(.+?)\s+as the\s+:TYPED-TERM\.",
    re.IGNORECASE,
)
INDUCTION_PUSH_RE = re.compile(
    r"^(\*[^\s]+)\s+\((.+?)\)\s+is pushed for proof by induction\.$",
    re.IGNORECASE,
)
SUBPROOF_COMPLETE_RE = re.compile(r"^(\*[^\s]+)\s+is COMPLETED!$", re.IGNORECASE)
CHECKPOINT_COMPLETE_RE = re.compile(
    r"^Thus key checkpoint\s+(.+?)\s+is COMPLETED!$",
    re.IGNORECASE,
)
NONREC_WARNING_RE = re.compile(
    r"A\s+:(?P<rule_class>[A-Z0-9-]+)\s+rule generated from\s+(?P<theorem>[^\s]+)\s+"
    r"will be triggered only by terms containing\s+the function symbols?\s+"
    r"(?P<functions>.+?),\s+which\s+(?:has|have)\s+(?:a\s+)?non-\s*recursive definitions?\.",
    re.IGNORECASE,
)
FREE_WARNING_RE = re.compile(
    r"A\s+:(?P<rule_class>[A-Z0-9-]+)\s+rule generated from\s+(?P<theorem>[^\s]+)\s+"
    r"contains the free variable\s+(?P<variable>[^\s.]+)\.\s+This variable will be chosen by "
    r"searching for an instance of\s+(?P<hypothesis>.+?)\s+in the context of the term being rewritten\.",
    re.IGNORECASE,
)
FREE_WARNING_WITH_TRIGGER_RE = re.compile(
    r"A\s+:(?P<rule_class>[A-Z0-9-]+)\s+rule generated from\s+(?P<theorem>[^\s]+)\s+"
    r"will be triggered by the term\s+(?P<trigger>.+?)\.\s+When\s+[^\s]+\s+is triggered by\s+.+?\s+"
    r"the variable\s+(?P<variable>[^\s.]+)\s+will be chosen by searching for an instance of\s+"
    r"(?P<hypothesis>.+?)\s+among the hypotheses of the conjecture being rewritten\.",
    re.IGNORECASE,
)
FORWARD_CHAINING_NONREC_WARNING_RE = re.compile(
    r"The term\s+(?P<trigger>.+?)\s+contains the function symbol\s+(?P<function>[^\s,]+),\s+"
    r"which has a non-\s*recursive definition\.\s+Unless this definition is disabled,\s+"
    r"(?P=trigger)\s+is unlikely ever to occur as a trigger for\s+(?P<theorem>[^\s.]+)\.",
    re.IGNORECASE,
)
SPLITTER_RULE_RE = re.compile(r"^\s*([^:]+):\s*(.+?)\s*$")
SPLITTER_ENTRY_RE = re.compile(r"^[^(\s:][^:]*:\s*.+$")
SPLITTER_NOTE_TARGET_RE = re.compile(
    r"^Splitter note .* for\s+(.+?)\s+\(\d+\s+subgoals?\)\.$",
    re.IGNORECASE,
)


def normalize_name(name: str) -> str:
    return name.strip().lower()


def inline_text(text: str) -> str:
    return " ".join(text.split())


def dedup_strings(items: list[str]) -> list[str]:
    deduped: list[str] = []
    seen: set[str] = set()
    for item in items:
        key = inline_text(item)
        if key in seen:
            continue
        seen.add(key)
        deduped.append(item)
    return deduped


def dedup_goal_events(items: list[tuple[str, str]]) -> list[tuple[str, str]]:
    deduped: list[tuple[str, str]] = []
    seen: set[tuple[str, str]] = set()
    for goal, event in items:
        key = (inline_text(goal), inline_text(event))
        if key in seen:
            continue
        seen.add(key)
        deduped.append((goal, event))
    return deduped


def normalize_transcript_lines(lines: list[str]) -> list[str]:
    normalized: list[str] = []
    for raw_line in lines:
        line = raw_line.rstrip("\n")
        match = PROMPT_PREFIX_RE.match(line)
        if match is None:
            normalized.append(line)
            continue
        prompt, remainder = match.groups()
        normalized.append(prompt)
        remainder = remainder.lstrip()
        if remainder:
            normalized.append(remainder)
    return normalized


def make_action(
    kind: str,
    source: str,
    summary: str,
    detail: str,
    *,
    targets: list[str] | None = None,
    goal_target: str | None = None,
) -> dict[str, object]:
    normalized_goal_target = goal_target.strip() if goal_target else ""
    return {
        "kind": kind,
        "source": source,
        "summary": summary,
        "goal_target": normalized_goal_target or None,
        "targets": targets or [],
        "detail": detail,
    }


def dedup_actions(actions: list[dict[str, object]]) -> list[dict[str, object]]:
    deduped: list[dict[str, object]] = []
    seen: set[tuple[str, str, str, str, tuple[str, ...]]] = set()
    for action in actions:
        targets = tuple(str(target) for target in action.get("targets", []))
        goal_target = str(action.get("goal_target") or "")
        key = (
            str(action.get("kind", "")),
            str(action.get("source", "")),
            str(action.get("summary", "")),
            goal_target,
            targets,
        )
        if key in seen:
            continue
        seen.add(key)
        deduped.append(action)
    return deduped


def split_acl2_symbol_list(text: str) -> list[str]:
    normalized = re.sub(r"\s+and\s+", ",", text.strip(), flags=re.IGNORECASE)
    return [part.strip().strip(".,") for part in normalized.split(",") if part.strip()]


def nonrec_action_summary(rule_class: str, theorem_name: str, definition_rune: str) -> str:
    if rule_class.lower() == "rewrite":
        return f"disable {definition_rune} so rewrite from {theorem_name} can fire"
    return f"disable {definition_rune} so :{rule_class.upper()} from {theorem_name} can fire"


def trigger_nonrec_action_summary(theorem_name: str, definition_rune: str, trigger_term: str) -> str:
    return f"disable {definition_rune} so trigger term {trigger_term} can arise for {theorem_name}"


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

    if requested_posix.endswith("acl2_samples/2009-tri-sq.lisp"):
        maybe_add_plan(
            plans,
            requested_book,
            system_root / "workshops" / "2009" / "cowles-gamboa-triangle-square" / "materials" / "tri-sq.lisp",
            note="canonical upstream book for excerpted 2009 triangle-square sample",
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
        primary_constraints = system_root / "projects" / "apply-model" / "apply-constraints.lisp"
        maybe_add_plan(
            plans,
            requested_book,
            requested_path,
            preludes=(primary_portcullis, primary_constraints),
            note="repo sample loaded with upstream MODAPP portcullis and apply-constraints prelude",
        )
        maybe_add_plan(
            plans,
            requested_book,
            system_root / "projects" / "apply-model" / "apply.lisp",
            preludes=(primary_portcullis, primary_constraints),
            note="canonical upstream apply-model book with MODAPP portcullis and apply-constraints prelude",
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


def collect_progress_entries(lines: list[str]) -> list[dict[str, str]]:
    progress: list[dict[str, str]] = []
    for raw_line in lines:
        line = raw_line.strip()
        if not line:
            continue

        induction_push_match = INDUCTION_PUSH_RE.fullmatch(line)
        if induction_push_match:
            proof_name, checkpoint_label = induction_push_match.groups()
            progress.append(
                {
                    "kind": "induction-push",
                    "label": f"{proof_name} ({checkpoint_label})",
                    "text": line,
                }
            )
            continue

        subproof_complete_match = SUBPROOF_COMPLETE_RE.fullmatch(line)
        if subproof_complete_match:
            progress.append(
                {
                    "kind": "subproof-complete",
                    "label": subproof_complete_match.group(1),
                    "text": line,
                }
            )
            continue

        checkpoint_complete_match = CHECKPOINT_COMPLETE_RE.fullmatch(line)
        if checkpoint_complete_match:
            progress.append(
                {
                    "kind": "checkpoint-complete",
                    "label": checkpoint_complete_match.group(1).strip(),
                    "text": line,
                }
            )

    return progress


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
                j += 1
            blocks.append("\n".join(block).strip())
            i = j
        i += 1
    return blocks


def balanced_paren_delta(text: str) -> int:
    depth = 0
    in_string = False
    escape = False
    for char in text:
        if in_string:
            if escape:
                escape = False
            elif char == "\\":
                escape = True
            elif char == '"':
                in_string = False
            continue

        if char == '"':
            in_string = True
            continue
        if char == "(":
            depth += 1
        elif char == ")":
            depth -= 1
    return depth


def collect_transcript_form(lines: list[str]) -> str | None:
    collected: list[str] = []
    depth = 0
    started = False
    for raw_line in lines:
        line = raw_line.rstrip()
        stripped = line.strip()
        if not started:
            if not stripped or PROMPT_RE.match(stripped):
                continue
            if "(" not in stripped:
                return None
            started = True
        collected.append(line)
        depth += balanced_paren_delta(line)
        if started and depth <= 0:
            form = "\n".join(collected).strip()
            return form or None
    return None


def find_named_defthm_form(form_text: str, theorem_name: str) -> str | None:
    entries = split_top_level_entries(form_text)
    if len(entries) >= 2 and entries[0].lower() == "defthm" and normalize_name(entries[1]) == normalize_name(theorem_name):
        return form_text.strip()

    for entry in entries:
        if not entry.startswith("("):
            continue
        nested = find_named_defthm_form(entry, theorem_name)
        if nested is not None:
            return nested
    return None


def defthm_option_value(form_text: str, theorem_name: str, option_name: str) -> str | None:
    defthm_form = find_named_defthm_form(form_text, theorem_name)
    if defthm_form is None:
        return None

    entries = split_top_level_entries(defthm_form)
    for idx in range(3, len(entries) - 1):
        if entries[idx].lower() == option_name.lower():
            return entries[idx + 1]
    return None


def transcript_hint_events(lines: list[str], theorem_name: str) -> list[str]:
    return [event for _, event in transcript_goal_hint_events(lines, theorem_name)]


def render_goal_target(goal_expr: str) -> str:
    goal = goal_expr.strip()
    if len(goal) >= 2 and goal[0] == '"' and goal[-1] == '"':
        return goal[1:-1].replace('\\"', '"')
    return inline_text(goal)


def transcript_goal_hint_events(lines: list[str], theorem_name: str) -> list[tuple[str, str]]:
    form_text = collect_transcript_form(lines)
    if form_text is None:
        return []

    hints_value = defthm_option_value(form_text, theorem_name, ":hints")
    if hints_value is None:
        return []

    events: list[tuple[str, str]] = []
    for goal_hint in split_top_level_entries(hints_value):
        entries = split_top_level_entries(goal_hint)
        if not entries:
            continue
        goal_target = ""
        start_idx = 0
        if not entries[0].startswith(":"):
            goal_target = render_goal_target(entries[0])
            start_idx = 1
        idx = start_idx
        while idx + 1 < len(entries):
            option = entries[idx]
            if not option.startswith(":"):
                idx += 1
                continue
            payload = entries[idx + 1]
            events.append((goal_target, f"({option.upper()} {payload})"))
            idx += 2
    return dedup_goal_events(events)


def split_use_payload_items(payload: str) -> list[str]:
    stripped = payload.strip()
    if not stripped:
        return []
    if not stripped.startswith("("):
        return [stripped]

    entries = split_top_level_entries(stripped)
    if not entries:
        return [stripped]

    # `:USE` accepts a single hint spec like `(:INSTANCE ...)` as well as a list
    # of theorem names / hint specs. Keep the single-spec form intact, but split
    # list payloads into one replay action per cited theorem or instance.
    if stripped.startswith("(("):
        return entries
    if entries[0].startswith(":"):
        return [stripped]
    return entries


def parse_hint_event_actions(
    event: str,
    *,
    goal_target: str = "",
    source: str = "hint-event",
) -> list[dict[str, object]]:
    event_text = inline_text(event)
    match = HINT_EVENT_RE.match(event_text)
    if match is None:
        summary = event_text if not goal_target else f"{event_text} in {goal_target}"
        targets = [] if not goal_target else [goal_target]
        detail = event if not goal_target else f"{goal_target}: {event}"
        return [make_action("hint-event", source, summary, detail, targets=targets)]

    keyword = match.group(1).lower()
    payload = inline_text(match.group(2))
    detail = event if not goal_target else f"{goal_target}: {event}"

    def with_goal(summary: str) -> str:
        if goal_target:
            return f"{summary} in {goal_target}"
        return summary

    if keyword == "use":
        actions: list[dict[str, object]] = []
        for use_payload in split_use_payload_items(payload):
            targets = [use_payload] if use_payload else []
            if goal_target:
                targets.append(goal_target)
            actions.append(
                make_action(
                    "use",
                    source,
                    with_goal(f"use {use_payload}"),
                    detail,
                    targets=targets,
                    goal_target=goal_target or None,
                )
            )
        return actions

    targets = [payload] if payload else []
    if goal_target:
        targets.append(goal_target)
    if keyword == "in-theory":
        return [
            make_action(
                "in-theory",
                source,
                with_goal(f"adjust theory {payload}"),
                detail,
                targets=targets,
                goal_target=goal_target or None,
            )
        ]
    if keyword == "cases":
        return [
            make_action(
                "cases",
                source,
                with_goal(f"split cases {payload}"),
                detail,
                targets=targets,
                goal_target=goal_target or None,
            )
        ]
    return [
        make_action(
            keyword,
            source,
            with_goal(f"{keyword} {payload}".strip()),
            detail,
            targets=targets,
            goal_target=goal_target or None,
        )
    ]


def extract_observation_actions(observations: list[str]) -> list[dict[str, object]]:
    actions: list[dict[str, object]] = []
    for observation in observations:
        observation_text = inline_text(observation)
        typed_term_match = TYPED_TERM_RE.search(observation_text)
        if typed_term_match:
            term = typed_term_match.group(1).strip()
            actions.append(
                make_action(
                    "typed-term",
                    "observation",
                    f"focus on typed term {term}",
                    observation,
                    targets=[term],
                )
            )
    return actions


def extract_warning_actions(warnings: list[str]) -> list[dict[str, object]]:
    actions: list[dict[str, object]] = []
    for warning in warnings:
        warning_text = inline_text(warning)
        disable_match = DISABLE_HINT_RE.search(warning_text)
        if disable_match:
            rule = disable_match.group(1).strip()
            goal = disable_match.group(2).strip()
            rune_match = RULE_RUNE_RE.match(rule)
            if ":use" in warning_text.lower():
                if rune_match:
                    rule_class = rune_match.group(1).lower()
                    rule_target = rune_match.group(2).strip()
                    if rule_class == "rewrite":
                        use_summary = f"use {rule_target} in {goal}"
                        use_targets = [rule_target, goal]
                    elif rule_class == "definition":
                        use_summary = f"use definition {rule_target} in {goal}"
                        use_targets = [rule_target, goal]
                    else:
                        use_summary = f"use {rule} in {goal}"
                        use_targets = [rule, goal]
                else:
                    use_summary = f"use {rule} in {goal}"
                    use_targets = [rule, goal]
                actions.append(
                    make_action(
                        "use",
                        "warning",
                        use_summary,
                        warning,
                        targets=use_targets,
                        goal_target=goal,
                    )
                )
            actions.append(
                make_action(
                    "disable-rule",
                    "warning",
                    f"disable {rule} in {goal}",
                    warning,
                    targets=[rule, goal],
                    goal_target=goal,
                )
            )

        subsume_match = SUBSUME_NEW_OVER_OLD_RE.search(warning_text)
        if subsume_match:
            theorem_name, rule_name = subsume_match.groups()
            actions.append(
                make_action(
                    "watch-rune-overlap",
                    "warning",
                    f"compare generated rewrite from {theorem_name} with existing rewrite {rule_name}",
                    warning,
                    targets=[theorem_name, rule_name],
                )
            )
            continue

        subsume_match = SUBSUME_OLD_OVER_NEW_RE.search(warning_text)
        if subsume_match:
            rule_name, theorem_name = subsume_match.groups()
            actions.append(
                make_action(
                    "watch-rune-overlap",
                    "warning",
                    f"compare generated rewrite from {theorem_name} with existing rewrite {rule_name}",
                    warning,
                    targets=[theorem_name, rule_name],
                )
            )

        nonrec_match = NONREC_WARNING_RE.search(warning_text)
        if nonrec_match:
            theorem_name = nonrec_match.group("theorem")
            rule_class = nonrec_match.group("rule_class")
            function_names = split_acl2_symbol_list(nonrec_match.group("functions"))
            for function_name in function_names:
                definition_rune = f"(:DEFINITION {function_name})"
                actions.append(
                    make_action(
                        "disable-definition",
                        "warning",
                        nonrec_action_summary(rule_class, theorem_name, definition_rune),
                        warning,
                        targets=[definition_rune, theorem_name],
                    )
                )

        trigger_nonrec_match = FORWARD_CHAINING_NONREC_WARNING_RE.search(warning_text)
        if trigger_nonrec_match:
            theorem_name = trigger_nonrec_match.group("theorem").strip()
            function_name = trigger_nonrec_match.group("function").strip()
            trigger_term = trigger_nonrec_match.group("trigger").strip()
            definition_rune = f"(:DEFINITION {function_name})"
            actions.append(
                make_action(
                    "disable-definition",
                    "warning",
                    trigger_nonrec_action_summary(theorem_name, definition_rune, trigger_term),
                    warning,
                    targets=[definition_rune, theorem_name, trigger_term],
                )
            )

        free_match = FREE_WARNING_WITH_TRIGGER_RE.search(warning_text)
        if free_match is None:
            free_match = FREE_WARNING_RE.search(warning_text)
        if free_match:
            variable = free_match.group("variable").strip()
            hypothesis = free_match.group("hypothesis").strip()
            trigger = free_match.groupdict().get("trigger", "").strip()
            summary = f"bind free variable {variable} using {hypothesis}"
            targets = [variable, hypothesis]
            if trigger:
                summary += f" when rule sees {trigger}"
                targets.append(trigger)
            actions.append(
                make_action(
                    "bind-free-variable",
                    "warning",
                    summary,
                    warning,
                    targets=targets,
                )
            )
    return actions


def collect_splitter_goal_rules(lines: list[str]) -> list[tuple[str, str]]:
    splitter_goal_rules: list[tuple[str, str]] = []
    i = 0
    while i < len(lines):
        target_match = SPLITTER_NOTE_TARGET_RE.match(lines[i].strip())
        if target_match is None:
            i += 1
            continue

        goal_target = target_match.group(1).strip()
        j = i + 1
        block_lines: list[str] = []
        while j < len(lines):
            line = lines[j].rstrip()
            stripped = line.strip()
            if not stripped:
                break
            if stripped == "Summary" or stripped == "Q.E.D.":
                break
            if GOAL_LINE_RE.fullmatch(stripped) or SUBGOAL_LINE_RE.fullmatch(stripped):
                break
            if SPLITTER_NOTE_TARGET_RE.match(stripped) or PROMPT_RE.match(stripped):
                break
            block_lines.append(line)
            j += 1

        if block_lines:
            for entry in normalize_splitter_entries("\n".join(block_lines)):
                splitter_goal_rules.append((goal_target, entry))

        i = j

    return dedup_goal_events(splitter_goal_rules)


def splitter_action(rule: str, goal_target: str = "") -> dict[str, object]:
    rule_text = inline_text(rule)
    match = SPLITTER_RULE_RE.match(rule_text)
    summary_goal = f" in {goal_target}" if goal_target else ""
    if match is None:
        targets = [] if not goal_target else [goal_target]
        return make_action(
            "splitter",
            "splitter",
            f"apply splitter {rule_text}{summary_goal}",
            rule,
            targets=targets,
            goal_target=goal_target or None,
        )

    splitter_name, payload = match.groups()
    targets = [splitter_name.strip(), payload.strip()]
    if goal_target:
        targets.append(goal_target)
    return make_action(
        "split-goal",
        "splitter",
        f"split using {splitter_name.strip()} with {payload.strip()}{summary_goal}",
        rule,
        targets=targets,
        goal_target=goal_target or None,
    )


def extract_splitter_actions(
    splitter_rules: list[str],
    splitter_goal_rules: list[tuple[str, str]],
) -> list[dict[str, object]]:
    actions: list[dict[str, object]] = []
    targeted_rules = {inline_text(rule) for _, rule in splitter_goal_rules}
    for goal_target, rule in splitter_goal_rules:
        actions.append(splitter_action(rule, goal_target))
    for rule in splitter_rules:
        if inline_text(rule) in targeted_rules:
            continue
        actions.append(splitter_action(rule))
    return actions


def extract_induction_actions(inductions: list[str]) -> list[dict[str, object]]:
    actions: list[dict[str, object]] = []
    for induction in inductions:
        induction_text = inline_text(induction)
        term_match = INDUCTION_TERM_RE.search(induction_text)
        rule_match = INDUCTION_RULE_RE.search(induction_text)
        term = term_match.group(1).strip() if term_match else ""
        rule = rule_match.group(1).strip() if rule_match else ""
        targets = [target for target in (term, rule) if target]
        summary = "consider ACL2's induction scheme"
        if term and rule:
            summary = f"induct on {term} using rule {rule}"
        elif term:
            summary = f"induct on {term}"
        elif rule:
            summary = f"induct using rule {rule}"
        actions.append(make_action("induct", "induction", summary, induction, targets=targets))
    return actions


def collect_actions(
    summary_hint_events: list[str],
    transcript_goal_hints: list[tuple[str, str]],
    splitter_rules: list[str],
    splitter_goal_rules: list[tuple[str, str]],
    warnings: list[str],
    inductions: list[str],
    observations: list[str],
) -> list[dict[str, object]]:
    actions: list[dict[str, object]] = []
    for event in summary_hint_events:
        actions.extend(parse_hint_event_actions(event))
    for goal_target, event in transcript_goal_hints:
        actions.extend(parse_hint_event_actions(event, goal_target=goal_target, source="transcript-hint"))
    actions.extend(extract_splitter_actions(splitter_rules, splitter_goal_rules))
    actions.extend(extract_warning_actions(warnings))
    actions.extend(extract_induction_actions(inductions))
    actions.extend(extract_observation_actions(observations))
    return dedup_actions(actions)


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


def unwrap_outer_list(text: str) -> str:
    stripped = text.strip()
    if not stripped.startswith("(") or not stripped.endswith(")"):
        return stripped

    depth = 0
    in_string = False
    escape = False
    for idx, char in enumerate(stripped):
        if in_string:
            if escape:
                escape = False
            elif char == "\\":
                escape = True
            elif char == '"':
                in_string = False
            continue

        if char == '"':
            in_string = True
            continue
        if char == "(":
            depth += 1
        elif char == ")":
            depth -= 1
            if depth == 0 and idx != len(stripped) - 1:
                return stripped

    if depth != 0:
        return stripped
    return stripped[1:-1].strip()


def split_top_level_entries(text: str) -> list[str]:
    stripped = text.strip()
    if not stripped or stripped == "NIL":
        return []

    body = unwrap_outer_list(stripped)
    if not body:
        return []

    entries: list[str] = []
    current: list[str] = []
    depth = 0
    in_string = False
    escape = False

    def flush() -> None:
        entry = "".join(current).strip()
        if entry:
            entry = "\n".join(line.strip() for line in entry.splitlines() if line.strip())
        if entry:
            entries.append(entry)
        current.clear()

    for char in body:
        if depth == 0 and not in_string and char.isspace():
            flush()
            continue

        current.append(char)

        if in_string:
            if escape:
                escape = False
            elif char == "\\":
                escape = True
            elif char == '"':
                in_string = False
            continue

        if char == '"':
            in_string = True
            continue
        if char == "(":
            depth += 1
        elif char == ")":
            depth -= 1
            if depth == 0:
                flush()

    flush()
    return entries


def normalize_summary_entries(text: str) -> list[str]:
    return split_top_level_entries(text)


def normalize_splitter_entries(text: str) -> list[str]:
    stripped = text.strip()
    if not stripped or stripped == "NIL":
        return []

    entries: list[str] = []
    current: list[str] = []
    for raw_line in text.splitlines():
        line = raw_line.rstrip()
        if not line.strip():
            continue
        trimmed = line.strip()
        if current and SPLITTER_ENTRY_RE.match(trimmed):
            entries.append("\n".join(current).strip())
            current = [trimmed]
            continue
        current.append(trimmed)

    if current:
        entries.append("\n".join(current).strip())
    return entries


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
            summary[current_field] = normalize_splitter_entries(text)
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
    lines = normalize_transcript_lines(lines)
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
            "actions": [],
            "checkpoints": [],
            "progress": [],
            "observations": [],
            "warnings": [],
            "inductions": [],
            "raw_excerpt": [line.rstrip("\n") for line in lines[-80:]],
        }

    idx, theorem_name = all_matches[target_match_idx]
    excerpt = theorem_excerpt(lines, all_matches, target_match_idx)
    summary = parse_summary(excerpt, theorem_name)
    transcript_goal_hints = transcript_goal_hint_events(excerpt, theorem_name)
    hint_events = dedup_strings(
        summary["hint_events"] + [event for _, event in transcript_goal_hints]
    )
    observations = collect_prefixed_blocks(excerpt, "ACL2 Observation")
    warnings = collect_prefixed_blocks(excerpt, "ACL2 Warning")
    inductions = collect_induction_blocks(excerpt)
    splitter_goal_rules = collect_splitter_goal_rules(excerpt)
    explicit_checkpoints = collect_checkpoint_blocks(excerpt)
    progress = collect_progress_entries(excerpt)

    return {
        "status": "proved",
        "requested_theorem": theorem,
        "theorem_name": theorem_name,
        "summary_form": summary["summary_form"] or lines[idx].strip(),
        "summary_rules": summary["summary_rules"],
        "hint_events": hint_events,
        "splitter_rules": summary["splitter_rules"],
        "warning_kinds": summary["warning_kinds"],
        "summary_time": summary["summary_time"],
        "prover_steps": summary["prover_steps"],
        "actions": collect_actions(
            summary["hint_events"],
            transcript_goal_hints,
            summary["splitter_rules"],
            splitter_goal_rules,
            warnings,
            inductions,
            observations,
        ),
        "checkpoints": (
            lambda explicit: explicit + collect_trace_checkpoints(
                excerpt, {checkpoint["label"] for checkpoint in explicit}
            )
        )(explicit_checkpoints),
        "progress": progress,
        "observations": observations,
        "warnings": warnings,
        "inductions": inductions,
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
