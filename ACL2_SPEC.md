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
- `ACL2Lean.Event.classify` lifts raw expressions into event constructors, defaulting to `skip` for unsupported forms (e.g., `mutual-recursion`, `in-theory`).

## Tooling Hooks
- `ACL2Lean.Import.loadEventsFromFile`: `IO` wrapper returning `Except String (List Event)`.
- `lake exe acl2lean metadata <file> [theorem]`: prints extracted theorem metadata and top-level `in-theory` events for quick replay-oriented inspection.
- `ACL2Lean.Workbench.reportSamples`: `#eval` helper that prints event histograms for sanity checking future corpus updates.
- Extend `sampleFiles` to track regressions; `lake build` exercises the pipeline automatically.

## Next Steps
1. Parse richer hint subforms such as `:instructions`, `:cases`, and more nested `:in-theory` combinators so replay can target larger books.
2. Replace more `skip` bodies by capturing explicit event forms for guard/measure metadata and theorem-local control structure.
3. Feed extracted theorem metadata and theory events into proof replay and the ACL proof-mode widget instead of keeping them CLI/translator-only.
