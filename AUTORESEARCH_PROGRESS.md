# Autoresearch Progress

## 2026-03-19 Baseline

Known-good starting point:

- branch: `autoresearch/mar19-acl2lean`
- theorem-aware ACL infoview panel exists
- `lean-tui` / `LeanPrism` integration exists
- `lake build ACL2Lean.ProofMode ACL2Lean.ProofModeDemo Main` passes
- `uv run python Verify.py` matches ACL2 on the current regression set

Current north star:

- import existing ACL2 proofs and replay them in Lean so Lean's kernel is the checker

Initial backlog:

1. figure out what proof artifacts ACL2 can expose in a replay-friendly form
2. replay one small theorem from `acl2_samples/simple.lisp` or another tiny sample as a Lean theorem
3. build the infrastructure that most increases the chance of scaling replay
4. connect imported/replayed proof state to the ACL proof-mode UI

User direction update:

- the loop should also determine which stable slices belong on `main`
- do not mirror every rough research commit onto `main`
- promote stable, verified batches incrementally while keeping rough work on the research branch

## 2026-03-19 Iteration 1

Completed this iteration:

- normalized parsed ACL2 symbol names to lowercase and package qualifiers to uppercase so imported names match ACL2's case-insensitive reader model more closely
- added `Symbol.isNamed` and used it to make evaluator/translator handling of `quote`, `if`, and `let` case-insensitive even when syntax is constructed outside the parser
- added build-covered mixed-case regressions in `ACL2Lean/Parser.lean`, `ACL2Lean/Translator.lean`, and `ACL2Lean/Evaluator.lean`
- extended `Verify.py` with ACL2-backed mixed-case checks, including imported `FLOG2` / `CLOG2` lookups from `acl2_samples/2009-log2.lisp`

Verification:

- research branch commit `ba78e78`: `lake build`
- research branch commit `ba78e78`: `uv run python Verify.py`
- promoted the stable slice to `main` as `9c78e31`
- on `main`, a stale read-only `.lake/build` artifact blocked the first build; after `lake clean`, both `lake build` and `uv run python Verify.py` passed

Outcome:

- keep
- promoted to `main`

Next best ideas:

1. preserve original ACL2 symbol spellings alongside normalized lookup names so proof extraction can display source-faithful theorem/rune names without reintroducing lookup bugs
2. import more proof-relevant theorem metadata from `defthm` hints and `in-theory` events instead of only storing theorem bodies
3. replay a slightly richer imported theorem with locals/hints and connect that metadata to the proof-mode UI

## 2026-03-19 Iteration 2

Completed this iteration:

- replaced raw `defthm` hint blobs with structured theorem metadata (`TheoremInfo`, `GoalHint`, `RuleClass`, `TheoryExpr`) so imported ACL2 theorems now preserve `:hints`, `:rule-classes`, and `:in-theory` data in a replay-friendly form
- changed `World` to retain theorem metadata plus replay-order top-level theory events instead of only theorem bodies
- taught the translator to emit ACL2 metadata comments and top-level `in-theory` comments in generated Lean output, preserving proof-relevant context next to imported theorems
- added `acl2lean metadata <file> [theorem]` for inspecting extracted theorem metadata directly from sample books
- added parser regression guards for theorem options and `in-theory` parsing, and updated the ACL2 spec / proof-mode notes to reflect the new import surface

Verification:

- research branch commit `fc0f984`: `lake build`
- research branch commit `fc0f984`: `uv run python Verify.py`
- research branch commit `fc0f984`: `./.lake/build/bin/acl2lean metadata acl2_samples/2009-log2.lisp clog2-lemma-a`
- research branch commit `fc0f984`: `./.lake/build/bin/acl2lean metadata acl2_samples/2009-log2.lisp`
- research branch commit `fc0f984`: `./.lake/build/bin/acl2lean translate acl2_samples/2009-log2.lisp | rg -n "ACL2 metadata|ACL2 in-theory|rule-classes"`

Outcome:

- keep
- not promoted to `main` yet

Notes:

- the new metadata path works on top-level theorem-rich books like `acl2_samples/2009-log2.lisp`
- `acl2_samples/apply-model-apply-prim.lisp` still does not surface deeper `encapsulate`-scoped theorem metadata such as `badge-prim-type`, so mainline promotion should wait for better nested-event coverage

Next best ideas:

1. make theorem metadata inspection and translation recurse cleanly through more `encapsulate` / `local` / `make-event` shapes in books like `apply-model-apply-prim.lisp`
2. parse richer hint subforms such as `:instructions`, `:cases`, and nested theory combinators so replay can use more than just `:use` / `:in-theory`
3. connect extracted `GoalHint` and `TheoryExpr` data to `ACL2Lean.ProofMode` so the widget shows imported rune/hint provenance instead of only demo data

## 2026-03-19 Iteration 3

Completed this iteration:

- added best-effort static `make-event` recovery by dequasiquoting generated event skeletons and exposing them through shared `Event.generatedEvents` / `Event.flattenList` helpers
- taught `Event.classify` to unwrap `with-output` wrappers so nested events inside generated books survive classification instead of collapsing to `skip`
- updated `World.step` and the `acl2lean metadata` / `acl2lean translate` CLI paths to consume the shared flattening logic, so recovered generated events participate in replay-oriented inspection
- added build-time regression guards for wrapped `defthm` events and quasiquoted `make-event` encapsulates, and updated `ACL2_SPEC.md` to document the expanded import surface

Verification:

- research branch commit `84ceff5`: `lake build`
- research branch commit `84ceff5`: `uv run python Verify.py`
- research branch commit `84ceff5`: `./.lake/build/bin/acl2lean metadata acl2_samples/apply-model-apply-prim.lisp | sed -n '1,80p'`
- research branch commit `84ceff5`: `./.lake/build/bin/acl2lean metadata acl2_samples/apply-model-apply-prim.lisp 'apply$-prim-meta-fn-correct'`
- research branch commit `84ceff5`: `./.lake/build/bin/acl2lean translate acl2_samples/apply-model-apply-prim.lisp | sed -n '48,80p'`
- promoted the stable metadata batch to `main` as `0a2fa23` + `5a5caf6`
- on `main`, a stale read-only `.lake` artifact broke the first `lake build`; after `lake clean`, both `lake build` and `uv run python Verify.py` passed
- on `main`, `./.lake/build/bin/acl2lean metadata acl2_samples/apply-model-apply-prim.lisp 'apply$-prim-meta-fn-correct'` passed and showed the recovered meta theorem metadata

Outcome:

- keep
- promoted to `main`

Notes:

- `acl2_samples/apply-model-apply-prim.lisp` now surfaces the deeper generated theorems `n-car-cadr-caddr-etc-opener`, `apply$-prim-meta-fn-correct`, and `apply$-primp-implies-symbolp`, which unblocks promotion of the earlier structured-metadata work
- theorem lookup from the shell needs quoting around `$`-bearing ACL2 names, but the CLI lookup path itself works correctly once the shell does not mangle the theorem name

Next best ideas:

1. parse `:instructions`, `:cases`, and richer nested theory expressions into structured metadata instead of only preserving them as raw extra options
2. extend static recovery beyond direct quasiquote skeletons to dynamic-but-still-inspectable `make-event` result shapes such as `value` / `er-progn` branches
3. feed the recovered theorem metadata into `ACL2Lean.ProofMode` so imported books drive the infoview panel instead of the current demo snapshot

## 2026-03-19 Iteration 4

Completed this iteration:

- added a structured `ProofInstruction` tree to theorem metadata import so ACL2 `:instructions` are no longer opaque extra options
- taught the importer to recognize nested proof-builder blocks like `quiet!` / `:repeat` while keeping command arguments available for later replay
- added reusable rendering helpers so `acl2lean metadata` and translated Lean theorem comments now show proof-builder structure for imported theorems such as `apply$-prim-meta-fn-correct`
- added parser regression coverage for a real proof-builder script drawn from `acl2_samples/apply-model-apply-prim.lisp`
- updated the ACL2 spec to treat structured proof-builder instructions as the next replay seam instead of just a future parsing TODO

Verification:

- research branch commit `b3440b8`: `lake build`
- research branch commit `b3440b8`: `uv run python Verify.py`
- research branch commit `b3440b8`: `./.lake/build/bin/acl2lean metadata acl2_samples/apply-model-apply-prim.lisp 'apply$-prim-meta-fn-correct'`
- research branch commit `b3440b8`: `./.lake/build/bin/acl2lean translate acl2_samples/apply-model-apply-prim.lisp | sed -n '48,95p'`
- promoted the stable code slice to `main` as `bcfb1a4`
- on `main`, a stale read-only `.lake` artifact from the older toolchain broke the first build; after `lake clean`, `lake build` passed
- on `main`, `uv run python Verify.py` passed after rebuilding
- on `main`, `./.lake/build/bin/acl2lean metadata acl2_samples/apply-model-apply-prim.lisp 'apply$-prim-meta-fn-correct'` passed and showed the imported proof-builder structure

Outcome:

- keep
- promoted to `main`

Notes:

- the promoted `main` slice excluded `docs/acl-proof-mode.md` because `main` currently does not carry the proof-mode files that exist on the research branch
- this is the first imported ACL2 proof artifact in the repo that is closer to replay than presentation: the metadata path now preserves a navigable script skeleton instead of a raw s-expression blob

Next best ideas:

1. interpret the imported `ProofInstruction` tree for a tiny replay prototype, starting with `quiet!`, `:bash`, `:in-theory`, and `:repeat :prove`
2. parse additional hint metadata such as `:cases` and more nested theory combinators so more ACL2 books import replay-relevant structure cleanly
3. feed the imported instruction tree into `ACL2Lean.ProofMode` so the infoview can show real theorem steps rather than the current demo snapshot

## 2026-03-19 Iteration 5

Completed this iteration:

- taught `ACL2Lean.ProofMode` to derive a real widget `Snapshot` from imported `TheoremInfo` plus the preceding top-level ACL2 `in-theory` context instead of only using the hard-coded demo props
- added `#acl_imported_panel "<book>" "<theorem>"`, which loads an ACL2 book during elaboration and renders an imported-theorem proof-mode panel
- updated `ACL2Lean/ProofModeDemo.lean` to exercise the new path on `acl2_samples/apply-model-apply-prim.lisp` / `apply$-prim-meta-fn-correct`
- updated `README.md`, `ACL2_SPEC.md`, and `docs/acl-proof-mode.md` so the imported-panel path is part of the documented replay/UI seam

Verification:

- research branch commit `77052ac`: `lake build ACL2Lean.ProofMode ACL2Lean.ProofModeDemo Main`
- research branch commit `77052ac`: `lake build`
- research branch commit `77052ac`: `uv run python Verify.py`
- research branch commit `77052ac`: `./.lake/build/bin/acl2lean metadata acl2_samples/apply-model-apply-prim.lisp 'apply$-prim-meta-fn-correct' | sed -n '1,80p'`

Outcome:

- keep
- not promoted to `main` yet

Notes:

- proof-mode now displays imported checkpoints, runes/facts, and next-move suggestions from a real ACL2 theorem instead of only the synthetic `demoSnapshot`
- the imported panel is still a replay plan view, not checked replay state: long `union-theories` / `set-difference-theories` forms still surface as raw summaries, and the steps are not yet being executed against Lean goals

Next best ideas:

1. interpret `:bash`, `:in-theory`, and `:repeat :prove` against real Lean goals so the imported panel can report checked replay progress
2. parse richer nested theory combinators so the rune pane can decompose `union-theories` / `set-difference-theories` / `current-theory` instead of dumping raw expressions
3. connect the imported snapshot path to live tactic-state updates so the panel can mix imported ACL2 provenance with actual Lean checkpoint state

## 2026-03-19 Iteration 6

Completed this iteration:

- extended `TheoryExpr` so imported ACL2 theory metadata now preserves nested theory combinators and theory-set constructors, including quoted literal rune sets, `union-theories`, `set-difference-theories`, `current-theory`, `function-theory`, and `cons`
- added structured rendering helpers for theory trees and hint lines, then threaded them through `ProofInstruction` rendering so imported `:bash` / `:in-theory` steps are inspectable as trees instead of raw ACL2 s-expressions
- updated the `acl2lean metadata` CLI, translated Lean metadata comments, and `ACL2Lean.ProofMode` rune list to surface the decomposed theory context from real books such as `acl2_samples/apply-model-apply-prim.lisp`
- added a parser guard for `set-difference-theories` with `current-theory` / `function-theory` and documented the richer theory-expression coverage in `README.md`, `ACL2_SPEC.md`, and `docs/acl-proof-mode.md`

Verification:

- research branch commit `c9efe09`: `lake build ACL2Lean.Parser ACL2Lean.ProofMode Main`
- research branch commit `c9efe09`: `lake build`
- research branch commit `c9efe09`: `uv run python Verify.py`
- research branch commit `c9efe09`: `./.lake/build/bin/acl2lean metadata acl2_samples/apply-model-apply-prim.lisp 'apply$-prim-meta-fn-correct' | sed -n '1,120p'`
- research branch commit `c9efe09`: `./.lake/build/bin/acl2lean translate acl2_samples/apply-model-apply-prim.lisp | sed -n '48,115p'`

Outcome:

- keep
- not promoted to `main` yet

Notes:

- this is a real replay-facing improvement because the imported theorem path now exposes nested ACL2 theory structure in a form Lean-side tooling can inspect, rather than hiding it behind raw strings
- I did not promote this slice to `main` yet because the proof-mode consumer for the new rendering still depends on the earlier imported-panel batch that remains only on the research branch; promotion should likely bundle those stable UI commits together

Next best ideas:

1. interpret the structured `TheoryExpr` tree into a Lean-side active rune / simp-set model so imported `:in-theory` can affect checked replay instead of only display
2. parse `:cases` and other still-unstructured hint options so more ACL2 proof metadata becomes replay-usable
3. replace the imported panel's planned checkpoints with checked replay state by executing `:bash`, `:in-theory`, and `:repeat :prove` against Lean goals
