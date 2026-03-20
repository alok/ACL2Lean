# ACL2 EDSL Bridge for Lean 4

This project provides a bridge between ACL2 and Lean 4, allowing for parsing, evaluating, and translating ACL2 books into Lean 4 code.

## Key Features

- **Robust Parser**: Supports block comments, reader macros, escaped symbols, and complex numeric literals.
- **Semantic Evaluator**: A verified evaluator in Lean that matches ACL2 behavior for core primitives.
- **Automated Translator**: Translates ACL2 `defun` and `defthm` into Lean `def` and `theorem` statements.
- **Proving Support**: Includes `acl2_simp` and `acl2_grind` tactics.
- **Internal SMT Solver**: Leverages Lean's `grind` tactic with linear integer arithmetic (`cutsat`) support for automated proofs of arithmetic properties.

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
- **Imported theorem panel**: `#acl_imported_panel "acl2_samples/apply-model-apply-prim.lisp" "apply$-prim-meta-fn-correct"` now renders a proof-mode snapshot from real imported ACL2 metadata instead of only hand-written demo props.
- **Structured theory context**: imported `in-theory` metadata now decomposes nested ACL2 combinators like `union-theories` and `set-difference-theories` in the CLI, translated Lean comments, and proof-mode rune panel.

The intended split is:

- `lean-tui` owns proof navigation and graph structure.
- The infoview panel owns ACL-specific metadata that Lean’s default view does not surface well, such as runes, checkpoints, and hint provenance.

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
