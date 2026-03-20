import ACL2Lean.Logic

open ACL2 ACL2.Logic

namespace ACL2
namespace Imported
namespace Log2Replay

private def intExpr (z : Int) : SExpr :=
  .atom (.number (.int z))

private def natExpr (n : Nat) : SExpr :=
  intExpr (Int.ofNat n)

/--
A proof-friendly semantic mirror of the imported ACL2 `clog2`, restricted to
the positive-integer case that matters for theorem replay.
-/
private def clog2Nat (n : Nat) : Nat :=
  if n ≤ 1 then 0 else (n - 1).log2 + 1

private def nbrCallsClog2Nat (n : Nat) : Nat :=
  if n = 0 then 1 else clog2Nat n + 1

/-- Imported from `acl2_samples/2009-log2.lisp`, normalized through `Nat`. -/
def clog2 : SExpr → SExpr
  | .atom (.number (.int z)) =>
      if 0 < z then natExpr (clog2Nat z.toNat) else intExpr (-1)
  | _ => intExpr (-1)

/-- Imported from `acl2_samples/2009-log2.lisp`, normalized through `Nat`. -/
def nbrCallsClog2 : SExpr → SExpr
  | .atom (.number (.int z)) =>
      if 0 < z then natExpr (nbrCallsClog2Nat z.toNat) else intExpr 1
  | _ => intExpr 1

private theorem nbrCallsClog2Nat_eq_1_plus_clog2Nat {n : Nat} (h : 0 < n) :
    nbrCallsClog2Nat n = clog2Nat n + 1 := by
  simp [nbrCallsClog2Nat, Nat.ne_of_gt h]

/--
Reconstruction of ACL2 theorem `nbr-calls-clog2=1+clog2` from
`acl2_samples/2009-log2.lisp`.
-/
theorem nbr_calls_clog2_eq_1_plus_clog2 (n : SExpr) :
    Logic.toBool
      (Logic.implies (Logic.posp n)
        (Logic.equal (nbrCallsClog2 n) (Logic.plus (intExpr 1) (clog2 n)))) = true := by
  cases n with
  | nil =>
      simp [Logic.implies, Logic.posp]
  | cons a d =>
      simp [Logic.implies, Logic.posp]
  | atom a =>
      cases a with
      | number value =>
          cases value with
          | int z =>
              by_cases hz : 0 < z
              · have hz' : 0 ≤ z := by
                  omega
                have hzNatInt : (0 : Int) < z.toNat := by
                  simpa [Int.toNat_of_nonneg hz'] using hz
                have hNat : 0 < z.toNat :=
                  Int.ofNat_lt.mp hzNatInt
                have hEq : nbrCallsClog2 (intExpr z) = Logic.plus (intExpr 1) (clog2 (intExpr z)) := by
                  simp [nbrCallsClog2, clog2, intExpr, natExpr, hz, Logic.plus,
                    nbrCallsClog2Nat_eq_1_plus_clog2Nat hNat]
                  omega
                change
                  Logic.toBool
                    (Logic.implies (Logic.posp (intExpr z))
                      (Logic.equal (nbrCallsClog2 (intExpr z))
                        (Logic.plus (intExpr 1) (clog2 (intExpr z))))) = true
                rw [show Logic.posp (intExpr z) = .atom (.bool true) by
                  simp [intExpr, Logic.posp, hz]]
                rw [show Logic.equal (nbrCallsClog2 (intExpr z)) (Logic.plus (intExpr 1) (clog2 (intExpr z))) =
                    .atom (.bool true) by
                  simp [hEq]]
                rfl
              · simp [hz, Logic.implies, Logic.posp]
          | _ =>
              simp [Logic.implies, Logic.posp]
      | _ =>
          simp [Logic.implies, Logic.posp]

#guard clog2 (intExpr 1) = intExpr 0
#guard clog2 (intExpr 10) = intExpr 4
#guard nbrCallsClog2 (intExpr 10) = intExpr 5
#guard nbrCallsClog2 (intExpr 17) = intExpr 6

end Log2Replay
end Imported
end ACL2
