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
