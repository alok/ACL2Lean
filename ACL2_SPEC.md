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
- `scripts/acl2_hint_bridge.py`, `ACL2Lean/HintBridge.lean`, and `lake exe acl2lean hints <file> <theorem>` now lift lightweight ACL2 `Goal'` / `Subgoal ...` trace lines into structured dynamic checkpoints, so theorem-local proof progress is visible even when ACL2 does not emit a full `A key checkpoint` block.
- `ACL2Lean/Imported/Log2Replay.lean` is the first checked imported-theorem bundle in the repo: it proves ACL2 theorems `natp-clog2`, `posp-clog2`, `clog2-is-correct-lower`, `clog2-is-correct-upper`, `clog2-is-correct`, and `nbr-calls-clog2=1+clog2` from `acl2_samples/2009-log2.lisp` as Lean theorems over the `SExpr` encoding, using a proof-friendly `Nat` mirror for the positive-integer path.
- `ACL2Lean.Workbench.reportSamples`: `#eval` helper that prints event histograms for sanity checking future corpus updates.
- Extend `sampleFiles` to track regressions; `lake build` exercises the pipeline automatically.

## Next Steps
1. Generalize the `Log2Replay` pattern into reusable infrastructure so more imported ACL2 theorem clusters can lower to proof-friendly semantic mirrors instead of being reconstructed one-off.
2. Interpret the structured `ProofInstruction` tree for a small replay prototype instead of only printing it, starting with `quiet!`, `:bash`, `:in-theory`, and `:repeat :prove`.
3. Replace the imported widget snapshot's planned checkpoints with actual replay state once proof-mode starts executing the imported `ProofInstruction` / hint data against Lean goals.
