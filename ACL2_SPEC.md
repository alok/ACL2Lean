# ACL2 EDSL Notes

## Sample Corpus Coverage
- Sources: `acl2_samples/` pulls from ACL2 community books (workshops 2009+, projects `apply-model`, `die-hard`, `concurrent-programs`).
- Event mix after parsing (`#eval reportSamples`):
  - `defun`: 113 occurrences
  - `defthm`: 73 occurrences
  - `defmacro`: 5 occurrences
  - `include-book`: 11 occurrences
  - `in-package`: 8 occurrences
  - `skip`: primarily guard declarations, `in-theory`, raw hints (164 occurrences)

## Syntax Representation
- `ACL2Lean.Syntax` defines:
  - `Symbol` with package/name split (`ACL2::CAR` → `{ package := "ACL2", name := "CAR" }`).
  - `Atom` variants: symbol, keyword, string, boolean, `Number` (integer, rational, decimal placeholder).
  - `SExpr` for proper lists + atoms; helper views `ofList`, `toList?`, `headSymbol?`.
  - `TheoremInfo`, `GoalHint`, `ProofInstruction`, `RuleClass`, and `TheoryExpr` preserve proof-relevant `defthm` options such as `:hints`, `:instructions`, `:rule-classes`, and `:in-theory` in structured form.
  - `TheoryExpr` now decomposes nested ACL2 theory combinators such as `union-theories`, `set-difference-theories`, `current-theory`, `function-theory`, quoted literal rune sets, and `cons`-built theory sets instead of collapsing them to opaque raw s-expressions.
  - `Event` discriminates core ACL2 events used in the sample set (`inPackage`, `includeBook`, `defun`, `defthm`, `defmacro`, `inTheory`, `skip`).
  - `World` stores installed definitions, theorem metadata, and replay-order theory events.

## Parsing Pipeline
- `ACL2Lean.Parser` implements a partial s-expression reader over ASCII streams.
  - Supports comments (`; ...`), quoting (`'`, ``` ` ```, `,@`), keywords, booleans, numerals, character literals (`#\A`).
  - Unknown atoms remain symbols so future elaboration can reinterpret them.
- `ACL2Lean.Event.classify` lifts raw expressions into core event constructors and unwraps lightweight event wrappers such as `with-output`.
- `ACL2Lean.Event.generatedEvents` and `ACL2Lean.Event.flattenList` recover statically visible `make-event` expansions by dequasiquoting event skeletons without executing ACL2.
- Unsupported or dynamic forms still fall back to `skip`.

## Tooling Hooks
- `ACL2Lean.Import.loadEventsFromFile`: `IO` wrapper returning `Except String (List Event)`.
- `lake exe acl2lean metadata <file> [theorem]`: prints extracted theorem metadata and top-level `in-theory` events for quick replay-oriented inspection.
- `lake exe acl2lean metadata <file> [theorem]` and `lake exe acl2lean translate <file>` now see nested events surfaced through statically recoverable `make-event` expansions.
- `lake exe acl2lean metadata <file> [theorem]` and `lake exe acl2lean translate <file>` now render structured proof-builder steps from `:instructions`, which is the first replay-oriented import path for ACL2 proof scripts.
- Those metadata/translation views now also expand nested theory combinators into readable trees, so imported rune context from books like `apply-model-apply-prim.lisp` is inspectable without rereading the raw ACL2 form.
- `#acl_imported_panel "<file>" "<theorem>"` renders a ProofWidgets snapshot from imported `TheoremInfo` plus the preceding top-level `in-theory` context, so proof-mode can display real ACL2 theorem metadata instead of only the static demo snapshot.
- `scripts/acl2_hint_bridge.py`, `ACL2Lean/HintBridge.lean`, and `lake exe acl2lean hints <file> <theorem>` now lift lightweight ACL2 `Goal'` / `Subgoal ...` trace lines into structured dynamic checkpoints, capture lifecycle/progress lines such as induction-push and checkpoint/subproof completion notices, normalize prompt-adjacent markers such as `ACL2 !>>Goal'`, keep multiline splitter/hint payloads grouped instead of splitting them into fake entries, trim transcript slices to the target theorem's own summary block, preserve full induction summaries through the emitted subgoal-count line, recover theorem-local `:HINTS` directives from ACL2-emitted `DEFTHM` transcript forms when summary `Hint-events:` are absent, preserve the original ACL2 goal target for transcript-recovered hint actions, preserve checkpoint-local targets on splitter-note actions such as `Splitter note ... for Goal''`, split multi-item ACL2 `:USE` payloads into one replay action per cited theorem or instance, and extract typed replay actions from dynamic `:USE`, `:IN-THEORY`, `:EXPAND`, `:DO-NOT-INDUCT`, `:CLAUSE-PROCESSOR`, splitter notes, `:TYPED-TERM` observations, free-variable warnings, disable warnings, non-recursive-definition warnings (including plural definition lists, free-variable-search/non-rec combinations, non-`:REWRITE` rule classes, and forward-chaining trigger-term warnings), rewrite subsumption warnings (including quoted ACL2 rune names and plural prior-rule lists), goal-targeted `:USE` guidance inferred from ACL2 `[Use]` warnings, and induction summaries. Lean-side consumers now parse dynamic `:IN-THEORY` action payloads back into `TheoryExpr`, reparse dynamic `:EXPAND` / `:DO-NOT-INDUCT` payloads into structured ACL2 terms, and surface dynamic clause-processor plus induction payloads as structured `clause-processor`, `induct-term`, and `induction-rule` items, so the CLI and proof-mode views can inspect emitted replay guidance without re-parsing flat display strings.
- The dynamic bridge's sample-resolution fallback now handles the general-purpose `apply-model/apply` book with the required upstream prelude chain (`portcullis.acl2` plus `apply-constraints.lisp`), not just the narrower `apply-prim` path.
- The same fallback layer now resolves `acl2_samples/2009-tri-sq.lisp` to the canonical upstream workshop book so dynamic hint extraction can run despite the excerpt's missing local `log2.lisp`.
- `ACL2Lean/Imported/Log2Replay.lean` is the first checked imported-theorem bundle in the repo: it proves ACL2 theorems `natp-clog2`, `posp-clog2`, `clog2-is-correct-lower`, `clog2-is-correct-upper`, `clog2-is-correct`, and `nbr-calls-clog2=1+clog2` from `acl2_samples/2009-log2.lisp` as Lean theorems over the `SExpr` encoding, using a proof-friendly `Nat` mirror for the positive-integer path.
- `ACL2Lean.Workbench.reportSamples`: `#eval` helper that prints event histograms for sanity checking future corpus updates.
- Extend `sampleFiles` to track regressions; `lake build` exercises the pipeline automatically.

## Next Steps
1. Generalize the `Log2Replay` pattern into reusable infrastructure so more imported ACL2 theorem clusters can lower to proof-friendly semantic mirrors instead of being reconstructed one-off.
2. Execute the dynamic replay actions against Lean-side replay state instead of only rendering them, starting with `:USE`, theory-disable suggestions, and induction candidates.
3. Replace the imported widget snapshot's planned checkpoints with actual replay state once proof-mode starts executing the imported `ProofInstruction` / hint data against Lean goals.
