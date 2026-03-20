# ACL2 EDSL Bridge for Lean 4

This project provides a bridge between ACL2 and Lean 4, allowing for parsing, evaluating, and translating ACL2 books into Lean 4 code.

## Key Features

- **Robust Parser**: Supports block comments, reader macros, escaped symbols, and complex numeric literals.
- **Semantic Evaluator**: A verified evaluator in Lean that matches ACL2 behavior for core primitives.
- **Automated Translator**: Translates ACL2 `defun` and `defthm` into Lean `def` and `theorem` statements.
- **Proving Support**: Includes `acl2_simp` and `acl2_grind` tactics.
- **Internal SMT Solver**: Leverages Lean's `grind` tactic with linear integer arithmetic (`cutsat`) support for automated proofs of arithmetic properties.
- **Checked Imported Theorem Bundle**: `ACL2.Imported.Log2Replay` now reconstructs a small ACL2 theorem cluster from `acl2_samples/2009-log2.lisp`, including `clog2_is_correct`, `clog2_is_correct_upper`, `clog2_is_correct_lower`, `natp_clog2`, `posp_clog2`, and `nbr_calls_clog2_eq_1_plus_clog2`.

## Getting Started

1.  **Build**: `just build`
2.  **Launch TUI Proof View**: `just tui`
3.  **Open Proof Mode Demo**: inspect `ACL2Lean/ProofModeDemo.lean` in your editor to see the first ACL-oriented infoview panel and a matching proof that `lean-tui` can follow.
4.  **Report Coverage**: `just report`
5.  **Verify Evaluator**: `just verify` (Requires ACL2)
6.  **Translate Book**: `just translate acl2_samples/2009-log2.lisp`

## ACL Proof Mode UI

The repo now carries two early UI integration paths for co-designing an ACL-flavored proof workflow:

- **`lean-tui` + `LeanPrism`**: a terminal infoview that follows the active proof/function from your editor.
- **ProofWidgets infoview panel**: `ACL2Lean/ProofMode.lean` and `ACL2Lean/ProofModeDemo.lean` provide the first ACL-specific panel layout for checkpoints, rune/fact lists, and next moves.
- **Dynamic ACL2 hint bridge**: `scripts/acl2_hint_bridge.py`, `ACL2Lean/HintBridge.lean`, `acl2lean hints ...`, and `#acl_hint_panel ...` expose theorem-local ACL2-emitted checkpoints, warnings, and induction summaries inside Lean-side tooling, even when multiple `DEFTHM` summaries share a single ACL2 prompt inside larger `encapsulate` output.
- **Dynamic rule/hint summary capture**: the same bridge now also preserves ACL2 summary rules, hint-events, warning categories, and prover-step counts, and it can recover theorem-local `:HINTS` directives from ACL2’s echoed `DEFTHM` transcript when the summary omits `Hint-events:`; transcript-recovered hint actions now also keep their ACL2 goal target, so Lean can distinguish `Goal`-level guidance from `Goal'''` or `Subgoal ...`-specific advice instead of flattening everything into goal-less actions.
- **Structured replay actions**: the dynamic bridge now turns `:USE` hint-events, including multi-item `:USE` lists that ACL2 emits as theorem/instance bundles, splitter notes, warning-driven disable advice, free-variable warnings, non-recursive-definition warnings (including plural definition lists, free-variable-search/non-rec combinations, non-`:REWRITE` rule classes, and forward-chaining trigger-term guidance), rewrite-rule subsumption warnings (including quoted ACL2 rune names and plural prior-rule lists), `:TYPED-TERM` observations, and ACL2 induction choices into typed candidate replay actions that both the CLI and proof-mode panel can surface.
- **Dynamic payload normalization**: Lean-side consumers now parse dynamic ACL2 `:IN-THEORY` action payloads back into the shared `TheoryExpr` model, reparse dynamic `:USE` payloads into theorem-vs-instance structure plus explicit instance bindings, reparse dynamic `:EXPAND` plus `:DO-NOT-INDUCT` payloads into structured ACL2 terms, surface clause-processor plus induction payloads as structured items (`clause-processor`, `induct-term`, `induction-rule`) in the CLI and proof-mode notes/checkpoint views instead of leaving them trapped in flat summaries, preserve transcript-echoed theorem-level `:OTF-FLG` as a first-class `transcript-option` action when ACL2 exposes it, and decode warning-derived replay actions such as disable-rule, disable-definition, free-variable binding, and rewrite-overlap pairs back into structured Lean payloads instead of only positional target lists.
- **Explicit checkpoint targeting**: dynamic actions now carry an explicit ACL2 goal/subgoal target when ACL2 emitted one, including splitter notes such as `Splitter note ... for Goal''`, so Lean-side replay consumers no longer need to infer checkpoint scoping from a flat target list.
- **Goal-targeted `Use` guidance**: when ACL2 warns that a `:USE` hint is relying on an enabled rewrite or definition rule, the dynamic bridge now keeps both pieces of advice: the disable suggestion and a goal-specific `use ... in Subgoal ...` action that preserves which emitted checkpoint the hint was attached to.
- **Raw goal/subgoal trace capture**: when ACL2 emits lightweight `Goal'` / `Subgoal ...` progress lines without a full `A key checkpoint` block, the dynamic bridge now promotes those markers into structured checkpoints instead of leaving them trapped in `raw_excerpt`.
- **Transcript hardening for ACL2 pretty-print quirks**: prompt-adjacent goal markers like `ACL2 !>>Goal'` are now normalized before parsing, and multiline splitter/hint payloads stay grouped as single dynamic guidance entries instead of being shredded into bogus fragments.
- **Complete induction guidance blocks**: ACL2 induction summaries now retain the emitted subgoal-count line, so Lean-side tooling can see how many subgoals ACL2 predicted before the transcript fans out into `Subgoal ...` markers.
- **Lifecycle progress capture**: the dynamic bridge now also preserves ACL2 lifecycle lines such as induction-push markers and checkpoint/subproof completion notices, so the CLI and proof-mode panel can distinguish static checkpoint text from emitted proof progress.
- **Excerpted sample fallback**: when a repo sample is only a local excerpt of a larger ACL2 book, the dynamic hint bridge can now resolve it to the loadable upstream book and required preludes so real ACL2 proof output still reaches Lean, including the `apply-model/apply` path that needs both the `MODAPP` portcullis and the upstream `apply-constraints.lisp` prelude.
- **`tri-sq` dynamic coverage**: the same fallback path now also resolves `acl2_samples/2009-tri-sq.lisp` to the canonical upstream triangle-square workshop book, so the hint bridge can inspect `pair-pow-log-is-correct` and similar theorems instead of failing on the excerpt’s missing local `log2.lisp`.
- **Imported theorem panel**: `#acl_imported_panel "acl2_samples/apply-model-apply-prim.lisp" "apply$-prim-meta-fn-correct"` now renders a proof-mode snapshot from real imported ACL2 metadata instead of only hand-written demo props.
- **Structured theory context**: imported `in-theory` metadata now decomposes nested ACL2 combinators like `union-theories` and `set-difference-theories` in the CLI, translated Lean comments, and proof-mode rune panel.

The intended split is:

- `lean-tui` owns proof navigation and graph structure.
- The infoview panel owns ACL-specific metadata that Lean’s default view does not surface well, such as runes, checkpoints, and hint provenance.

## Imported Theorem Replay

`ACL2Lean/Imported/Log2Replay.lean` now provides the first checked reconstruction of an imported ACL2 theorem cluster in this repo:

- source book: `acl2_samples/2009-log2.lisp`
- Lean theorems:
  - `ACL2.Imported.Log2Replay.natp_clog2`
  - `ACL2.Imported.Log2Replay.posp_clog2`
  - `ACL2.Imported.Log2Replay.clog2_is_correct_lower`
  - `ACL2.Imported.Log2Replay.clog2_is_correct_upper`
  - `ACL2.Imported.Log2Replay.clog2_is_correct`
  - `ACL2.Imported.Log2Replay.nbr_calls_clog2_eq_1_plus_clog2`

The current replay strategy lowers the positive-integer execution path of the imported ACL2 functions into a small `Nat` semantic mirror, proves the central `clog2` bounds there, and lifts those facts back to the ACL2 `SExpr` encoding. This is not yet a generic replay engine, but it is a real kernel-checked imported theorem bundle rather than another metadata-only placeholder.

## Automated Proving with `grind`

The `acl2_grind` tactic is specifically designed to handle ACL2 proof obligations by combining congruence closure with powerful theory solvers like linear arithmetic.

Example of a proven theorem:
```lean
theorem plus_comm (x y : SExpr) : 
  Logic.toBool (integerp x) = true → 
  Logic.toBool (integerp y) = true → 
  Logic.toBool (Logic.equal (Logic.plus x y) (Logic.plus y x)) = true := by
  acl2_grind
```
This is proven automatically by Lean's `grind` tactic!
