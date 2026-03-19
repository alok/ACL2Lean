# ACL2Lean Autoresearch PRD

## Mission

Use Lean's kernel as the checker for imported ACL2 theorems.

The concrete end-state to optimize toward is:

- take an existing ACL2 book or theorem,
- import enough proof information to replay it in Lean,
- end with a native Lean theorem term, not just an ACL2-side success report,
- keep the result inspectable in both `lean-tui` and the custom ACL infoview panel.

## Current baseline

The repo already has:

- ACL2 parser/import/evaluator/translator scaffolding
- evaluator checks against ACL2 for basic expressions plus `flog2` / `clog2`
- `lean-tui` + `LeanPrism` installed
- a first ProofWidgets infoview panel in `ACL2Lean/ProofMode.lean`
- a theorem-aware `#acl_panel` command
- notes on `Sym` / `grind` extension points in `docs/acl-proof-mode.md`

## Primary objective

Figure out how to import an existing ACL2 proof and replay it in Lean so Lean is the checker.

This likely means some combination of:

1. discovering what ACL2 proof artifact or proof trace can be extracted from the ACL2 binary/source/books,
2. translating that artifact into a Lean proof script or a replay program,
3. using Lean tactics / `Sym` / `grind` / generated lemmas to discharge the steps,
4. producing final Lean theorems in repo code.

## Priority order

1. End-to-end proof replay on a small theorem from a real ACL2 sample.
2. Make the import/replay path reproducible from CLI or checked-in Lean files.
3. Surface replay state in the ACL proof-mode UI.
4. Investigate `Sym` / `grind` integration for ACL normalization and proof step replay.

## Constraints

- Follow repo instructions in `AGENTS.md`.
- Use `uv` for Python workflows.
- Keep working on a branch you control, never on `main`.
- Commit and push useful checkpoints.
- Prefer small, verifiable steps over speculative refactors.
- Do not break the existing evaluator regression flow.

## Deliverables to chase during the loop

- a documented proof-artifact extraction strategy for ACL2
- at least one imported theorem that is checked by Lean
- CLI and/or generated-file workflow for replaying imported proofs
- UI hooks that reflect real imported theorem/proof state instead of static placeholders

## Good first targets

- `acl2_samples/simple.lisp`
- small arithmetic/list lemmas that do not require heavy theory

## Nice-to-have

- use `Lean.Meta.Sym.Grind.Goal` APIs (`mkGoal`, `introN`, `simpIgnoringNoProgress`, `internalizeAll`, `Goal.grind`) to structure replay/checkpointing
- thread ACL rune/hint provenance into the infoview panel
