# ACL Proof Mode Notes

This repo now has the first two UI ingredients for an ACL-oriented proof workflow:

- `lean-tui` in the terminal, backed by `LeanPrism`
- a ProofWidgets infoview panel in `ACL2Lean/ProofMode.lean`

The immediate design split is:

- `lean-tui` should own proof navigation, graph structure, and cursor-following.
- the infoview panel should own ACL-specific metadata that Lean's default UI does not expose well: rune selection, checkpoints, hint provenance, and induction choices.

The importer now preserves structured `defthm` metadata (`:hints`, `:instructions`, `:rule-classes`) plus top-level `in-theory` events, and `#acl_imported_panel "<book>" "<theorem>"` now turns that imported data into a real infoview snapshot. Nested theory combinators such as `union-theories`, `set-difference-theories`, `current-theory`, and `function-theory` are now decomposed into readable structure in the CLI, translated Lean comments, and the proof-mode rune pane instead of surfacing as opaque raw ACL2 text. The panel is still showing replay plans rather than checked replay state, but it is no longer limited to a hand-written demo snapshot.

## Current setup

- `lean-toolchain` was upgraded to `leanprover/lean4:v4.29.0-rc6` to match the fetched UI dependencies.
- `lakefile.toml` now requires:
  - `LeanPrism`
  - `proofwidgets`
- `Justfile` adds:
  - `just tui-install`
  - `just tui`
- `ACL2Lean/ProofModeDemo.lean` is the first co-design sandbox:
  - imports `LeanPrism`
  - contains a small recursive proof that `lean-tui` can track
  - renders both the original `#acl_panel` theorem view and an imported-theorem view via `#acl_imported_panel "acl2_samples/apply-model-apply-prim.lisp" "apply$-prim-meta-fn-correct"`

## Grind / Sym extension seam

The relevant Lean sources on this toolchain are:

- `~/lean4/src/Lean/Meta/Sym/Grind.lean`
- `~/lean4/src/Lean/Meta/Tactic/Grind/Extension.lean`
- `~/lean4/src/Lean/Elab/Tactic/Grind/Main.lean`
- `~/lean4/src/Init/Sym/Lemmas.lean`

The useful `Goal`-level API from `Lean.Meta.Sym.Grind` is:

- `mkGoal : MVarId -> GrindM Goal`
- `Goal.introN`
- `Goal.simp`
- `Goal.simpIgnoringNoProgress`
- `Goal.internalizeAll`
- `Goal.grind`
- `Goal.apply`
- `Goal.assumption`

That API is the clearest path for an ACL-flavored symbolic proof loop because it lets us:

1. start from a metavariable goal,
2. introduce binders,
3. simplify symbolically with `Sym`,
4. internalize hypotheses into `grind`,
5. finish or checkpoint with `grind`.

## Grind attribute hooks

`Lean.Meta.Tactic.Grind.Extension` shows the main extension categories that matter for ACL integration:

- `ext`
- `funCC`
- `cases`
- `ematch`
- `inj`

`Lean.Elab.Tactic.Grind.Main` also exposes:

- `grind_pattern` for custom E-matching patterns
- local/scoped/global registration of patterns
- `init_grind_norm` for normalization theorem registration

That suggests a later ACL integration path:

1. mark ACL bridge lemmas with dedicated `grind` attributes,
2. register ACL-specific normalization theorems,
3. add targeted `grind_pattern` declarations for translated ACL rules,
4. surface the active rune set and chosen `grind` patterns in the infoview panel.

## Sym lemmas and typeclass hints

`Init/Sym/Lemmas.lean` exposes a large collection of canonicalization lemmas for booleans, equality, order relations, casts, and control-flow congruence. This is important for ACL because:

- it gives us a canonical term language to display in the panel,
- it suggests how `Sym` expects conditionals and arithmetic casts to normalize,
- it reduces the amount of ad hoc ACL-side rewriting we need to invent.

The notable short-term takeaway is that later ACL arithmetic work should lean on the existing `Sym`/`grind` normalization pipeline instead of building a parallel custom simplifier from scratch.

## Near-term next steps

1. Replace the imported panel's planned checkpoints with actual replay state, not just imported instructions and hints.
2. Add a compact rune timeline and selected induction variable to the widget.
3. Prototype a small `ACL2.Grind` helper module that wraps `mkGoal`, `simpIgnoringNoProgress`, `internalizeAll`, and `Goal.grind` for ACL-style checkpointed proofs.
4. Revisit evaluator arithmetic with `Sym`/`grind` expectations in mind, especially around rationals and casts.
