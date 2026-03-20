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
SPLITTER_RULE_RE = re.compile(r"^\s*([^:]+):\s*(.+?)\s*$")
SPLITTER_ENTRY_RE = re.compile(r"^[^(\s:][^:]*:\s*.+$")


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
) -> dict[str, object]:
    return {
        "kind": kind,
        "source": source,
        "summary": summary,
        "targets": targets or [],
        "detail": detail,
    }


def dedup_actions(actions: list[dict[str, object]]) -> list[dict[str, object]]:
    deduped: list[dict[str, object]] = []
    seen: set[tuple[str, str, str, tuple[str, ...]]] = set()
    for action in actions:
        targets = tuple(str(target) for target in action.get("targets", []))
        key = (
            str(action.get("kind", "")),
            str(action.get("source", "")),
            str(action.get("summary", "")),
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
    form_text = collect_transcript_form(lines)
    if form_text is None:
        return []

    hints_value = defthm_option_value(form_text, theorem_name, ":hints")
    if hints_value is None:
        return []

    events: list[str] = []
    for goal_hint in split_top_level_entries(hints_value):
        entries = split_top_level_entries(goal_hint)
        if not entries:
            continue
        start_idx = 0 if entries[0].startswith(":") else 1
        idx = start_idx
        while idx + 1 < len(entries):
            option = entries[idx]
            if not option.startswith(":"):
                idx += 1
                continue
            payload = entries[idx + 1]
            events.append(f"({option.upper()} {payload})")
            idx += 2
    return dedup_strings(events)


def parse_hint_event_action(event: str) -> dict[str, object]:
    event_text = inline_text(event)
    match = HINT_EVENT_RE.match(event_text)
    if match is None:
        return make_action("hint-event", "hint-event", event_text, event)

    keyword = match.group(1).lower()
    payload = inline_text(match.group(2))
    targets = [payload] if payload else []
    if keyword == "use":
        return make_action("use", "hint-event", f"use {payload}", event, targets=targets)
    if keyword == "in-theory":
        return make_action("in-theory", "hint-event", f"adjust theory {payload}", event, targets=targets)
    if keyword == "cases":
        return make_action("cases", "hint-event", f"split cases {payload}", event, targets=targets)
    return make_action(keyword, "hint-event", f"{keyword} {payload}".strip(), event, targets=targets)


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
            actions.append(
                make_action(
                    "disable-rule",
                    "warning",
                    f"disable {rule} in {goal}",
                    warning,
                    targets=[rule, goal],
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


def extract_splitter_actions(splitter_rules: list[str]) -> list[dict[str, object]]:
    actions: list[dict[str, object]] = []
    for rule in splitter_rules:
        rule_text = inline_text(rule)
        match = SPLITTER_RULE_RE.match(rule_text)
        if match is None:
            actions.append(make_action("splitter", "splitter", f"apply splitter {rule_text}", rule))
            continue
        splitter_name, payload = match.groups()
        actions.append(
            make_action(
                "split-goal",
                "splitter",
                f"split using {splitter_name.strip()} with {payload.strip()}",
                rule,
                targets=[splitter_name.strip(), payload.strip()],
            )
        )
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
    hint_events: list[str],
    splitter_rules: list[str],
    warnings: list[str],
    inductions: list[str],
    observations: list[str],
) -> list[dict[str, object]]:
    actions = [parse_hint_event_action(event) for event in hint_events]
    actions.extend(extract_splitter_actions(splitter_rules))
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
    hint_events = dedup_strings(summary["hint_events"] + transcript_hint_events(excerpt, theorem_name))
    observations = collect_prefixed_blocks(excerpt, "ACL2 Observation")
    warnings = collect_prefixed_blocks(excerpt, "ACL2 Warning")
    inductions = collect_induction_blocks(excerpt)
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
            hint_events,
            summary["splitter_rules"],
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
