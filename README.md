# ACL2 EDSL Bridge for Lean 4

This project provides a bridge between ACL2 and Lean 4, allowing for parsing, evaluating, and translating ACL2 books into Lean 4 code.

## Key Features

- **Robust Parser**: Supports block comments, reader macros, escaped symbols, and complex numeric literals.
- **Semantic Evaluator**: A verified evaluator in Lean that matches ACL2 behavior for core primitives.
- **Automated Translator**: Translates ACL2 `defun` and `defthm` into Lean `def` and `theorem` statements.
- **Proving Support**: Includes `acl2_simp` and `acl2_grind` tactics.
- **Internal SMT Solver**: Leverages Lean's `grind` tactic with linear integer arithmetic (`cutsat`) support for automated proofs of arithmetic properties.
- **Checked Imported Theorem**: `ACL2.Imported.Log2Replay.nbr_calls_clog2_eq_1_plus_clog2` reconstructs an ACL2 theorem from `acl2_samples/2009-log2.lisp` as a native Lean theorem.

## Getting Started

1.  **Build**: `just build`
2.  **Report Coverage**: `just report`
3.  **Verify Evaluator**: `just verify` (Requires ACL2)
4.  **Translate Book**: `just translate acl2_samples/2009-log2.lisp`

## Imported Theorem Replay

`ACL2Lean/Imported/Log2Replay.lean` now provides the first checked reconstruction of an imported ACL2 theorem in this repo:

- source theorem: `nbr-calls-clog2=1+clog2`
- source book: `acl2_samples/2009-log2.lisp`
- Lean theorem: `ACL2.Imported.Log2Replay.nbr_calls_clog2_eq_1_plus_clog2`

The current replay strategy lowers the positive-integer execution path of the imported ACL2 functions into a small `Nat` semantic mirror, proves the theorem there, and lifts it back to the ACL2 `SExpr` encoding. This is not yet a generic replay engine, but it is a real kernel-checked imported theorem rather than another metadata-only placeholder.

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
