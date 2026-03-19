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
