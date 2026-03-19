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
  - `TheoremInfo`, `GoalHint`, `RuleClass`, and `TheoryExpr` preserve proof-relevant `defthm` options such as `:hints`, `:rule-classes`, and `:in-theory` in structured form.
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
- `ACL2Lean.Workbench.reportSamples`: `#eval` helper that prints event histograms for sanity checking future corpus updates.
- Extend `sampleFiles` to track regressions; `lake build` exercises the pipeline automatically.

## Next Steps
1. Parse richer hint subforms such as `:instructions`, `:cases`, and more nested `:in-theory` combinators so replay can target larger books.
2. Extend static recovery beyond direct quasiquote skeletons to common `make-event` result wrappers such as `value`/`er-progn` branches that are still syntactically inspectable.
3. Feed extracted theorem metadata and theory events into proof replay and the ACL proof-mode widget instead of keeping them CLI/translator-only.
