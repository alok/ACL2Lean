# ACL Proof Mode Notes

This repo now has the first two UI ingredients for an ACL-oriented proof workflow:

- `lean-tui` in the terminal, backed by `LeanPrism`
- a ProofWidgets infoview panel in `ACL2Lean/ProofMode.lean`

The immediate design split is:

- `lean-tui` should own proof navigation, graph structure, and cursor-following.
- the infoview panel should own ACL-specific metadata that Lean's default UI does not expose well: rune selection, checkpoints, hint provenance, and induction choices.

The importer now preserves structured `defthm` metadata (`:hints`, `:instructions`, `:rule-classes`) plus top-level `in-theory` events, and `#acl_imported_panel "<book>" "<theorem>"` now turns that imported data into a real infoview snapshot. Nested theory combinators such as `union-theories`, `set-difference-theories`, `current-theory`, and `function-theory` are now decomposed into readable structure in the CLI, translated Lean comments, and the proof-mode rune pane instead of surfacing as opaque raw ACL2 text. The panel is still showing replay plans rather than checked replay state, but it is no longer limited to a hand-written demo snapshot.

There is now also a dynamic extraction seam: `scripts/acl2_hint_bridge.py` runs the ACL2 binary on a target book and theorem, recovers theorem-local checkpoints / warnings / induction suggestions from ACL2's own output, and `ACL2Lean/HintBridge.lean` parses that data back into Lean. `#acl_hint_panel "<book>" "<theorem>"` renders those emitted hints in the infoview, and `acl2lean hints <book> <theorem>` exposes the same bridge at the CLI. The bridge now also promotes raw `Goal'` / `Subgoal ...` trace lines into structured checkpoints, captures lifecycle/progress lines such as induction-push and checkpoint/subproof completion notices, normalizes prompt-adjacent markers like `ACL2 !>>Goal'`, keeps multiline splitter/hint payloads grouped as single dynamic guidance entries, trims transcript slices to the target theorem's own summary block so neighboring generated theorems in large `encapsulate` runs stop polluting the panel, preserves induction blocks through ACL2's emitted subgoal-count line, recovers theorem-local `:HINTS` directives from ACL2's echoed `DEFTHM` transcript when summary `Hint-events:` are absent, preserves transcript-echoed theorem-level directives such as `:OTF-FLG` as `transcript-option` actions when ACL2 actually prints them, preserves the original ACL2 goal target for transcript-recovered hint actions, preserves checkpoint-local targets on splitter notes such as `Splitter note ... for Goal''`, splits multi-item ACL2 `:USE` payloads into one replay action per cited theorem or instance, and turns dynamic `:USE`, `:IN-THEORY`, `:EXPAND`, `:DO-NOT-INDUCT`, `:CLAUSE-PROCESSOR`, splitter notes, `:TYPED-TERM` observations, free-variable warnings, disable advice, non-recursive-definition warnings (including plural definition lists, free-variable-search/non-rec combinations, non-`:REWRITE` rule classes, and forward-chaining trigger-term guidance), rewrite-rule overlap warnings (including quoted ACL2 rune names and plural prior-rule lists), goal-targeted `use ... in Subgoal ...` guidance inferred from ACL2 `[Use]` warnings, and induction choices into typed candidate replay actions. Those action records now also carry an explicit goal/subgoal target when ACL2 emitted one, proof-mode attaches checkpoint-local action summaries back onto the matching `Goal` / `Subgoal ...` cards instead of leaving replay targeting implicit in a flat notes list, dynamic `:IN-THEORY` actions are parsed back into the shared Lean `TheoryExpr` model, dynamic `:USE` actions are parsed back into theorem-vs-instance structure with explicit instance bindings, theorem-local source hints can now rehydrate missing `(:INSTANCE ...)` bindings when ACL2’s summary only reports the base theorem name, dynamic `Rules:` summary entries are normalized into structured rule-kind/target data, dynamic `split-goal` and `typed-term` actions now surface dedicated structured payloads in the CLI and proof-mode notes, dynamic `:EXPAND` / `:DO-NOT-INDUCT` actions are reparsed into structured ACL2 terms, dynamic clause-processor, induction, and `otf-flg` actions surface structured items in the CLI and proof-mode notes, and warning-derived actions now do the same for disable-rule, disable-definition, free-variable binding, and rewrite-overlap payloads so the next replay layer can consume data rather than scrape prose. `ACL2.HintBridge.DynamicArtifact.replayState` now folds those parsed actions into an interpreted replay summary with a theory timeline, use timeline, split timeline, typed-term foci, selected induction, and theorem-level search toggles like `do-not-induct` / `otf-flg`, while `ACL2.HintBridge.DynamicArtifact.runeProfile` groups ACL2 `Rules:` summaries and concrete theory enable/disable hints into a compact rune profile with rule-class buckets plus heuristic `lean-simp-candidates` / `lean-grind-candidates`. Proof-mode now surfaces both views, so the rune pane and notes no longer need to treat ACL2 rule usage and theory guidance as unrelated flat strings. The same dynamic path can now load the general-purpose `apply-model/apply` sample by replaying the upstream `MODAPP` portcullis plus `apply-constraints.lisp` before the repo sample, and it now also resolves `acl2_samples/2009-tri-sq.lisp` to the canonical workshop book so `pair-pow-log-is-correct` and related theorems can run through the oracle despite the excerpt's missing local `log2.lisp`.
There is now also one direct checked bridge from that oracle path back into Lean's theorem world: the `ACL2.Imported.Log2Replay` bundle includes `nbr_calls_flog2_upper_bound`, so the dynamic `:USE NBR-CALLS-FLOG2-UPPER-BOUND` guidance emitted for `nbr-calls-flog2-is-logarithmic` now has a matching imported Lean theorem rather than only a parsed action summary. The next step is no longer hypothetical either: `ACL2Lean.Tactics.acl2_use` resolves plain ACL2 theorem names through the imported registry, `acl2_use_instance` applies imported theorems with ACL2-style binding lists such as `((n (+ n 1)))`, `acl2lean hints` now prints replay seeds in both shapes when applicable, and the `Log2Replay` file now checks matching replay-seed theorems with both executors.

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

1. Extend `acl2_use` from exact imported-theorem matches to richer dynamic `:USE` payloads such as `(:INSTANCE ...)` and checkpoint-local theorem bundles.
2. Execute the remaining dynamic replay actions against real Lean goals instead of only surfacing them in the panel and CLI.
3. Replace the imported panel's planned checkpoints with actual replay state, not just imported instructions and hints.
4. Prototype a small `ACL2.Grind` helper module that wraps `mkGoal`, `simpIgnoringNoProgress`, `internalizeAll`, and `Goal.grind` for ACL-style checkpointed proofs.
