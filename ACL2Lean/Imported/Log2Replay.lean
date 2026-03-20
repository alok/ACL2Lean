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

private theorem int_toNat_pos {z : Int} (h : 0 < z) : 0 < z.toNat := by
  exact Int.ofNat_lt.mp <| by
    have hz : 0 ≤ z := by omega
    simpa [Int.toNat_of_nonneg hz] using h

private theorem int_toNat_gt_one {z : Int} (h : 1 < z) : 1 < z.toNat := by
  exact Int.ofNat_lt.mp <| by
    have hz : 0 ≤ z := by omega
    simpa [Int.toNat_of_nonneg hz] using h

private theorem clog2Nat_pos {n : Nat} (h : 1 < n) : 0 < clog2Nat n := by
  simp [clog2Nat, Nat.not_le.mpr h]

private theorem self_le_two_pow_clog2Nat (n : Nat) : n ≤ 2 ^ clog2Nat n := by
  by_cases h : n ≤ 1
  · simp [clog2Nat, h]
  · have hn : 1 < n := Nat.lt_of_not_ge h
    have hpow : n ≤ 2 ^ ((n - 1).log2 + 1) := by
      simpa [Nat.sub_add_cancel (Nat.le_of_lt hn)] using
        (Nat.succ_le_of_lt (Nat.lt_log2_self (n := n - 1)))
    simpa [clog2Nat, Nat.not_le.mpr hn] using hpow

private theorem two_pow_pred_clog2Nat_lt_self {n : Nat} (h : 1 < n) :
    2 ^ (clog2Nat n - 1) < n := by
  have hpow : 2 ^ ((n - 1).log2) ≤ n - 1 :=
    Nat.log2_self_le (Nat.sub_ne_zero_of_lt h)
  have hlt : 2 ^ ((n - 1).log2) < n := by
    have hsub : n - 1 < n := by omega
    omega
  simpa [clog2Nat, Nat.not_le.mpr h] using hlt

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

private theorem clog2_eq_natExpr_of_pos {z : Int} (hz : 0 < z) :
    clog2 (intExpr z) = natExpr (clog2Nat z.toNat) := by
  simp [clog2, intExpr, natExpr, hz]

private theorem expt_two_clog2_eq_natExpr_of_pos {z : Int} (hz : 0 < z) :
    Logic.expt (intExpr 2) (clog2 (intExpr z)) = natExpr (2 ^ clog2Nat z.toNat) := by
  simp [Logic.expt, clog2, intExpr, natExpr, hz]
  intro hneg
  omega

private theorem expt_two_pred_clog2_eq_natExpr_of_gt_one {z : Int} (hz : 1 < z) :
    Logic.expt (intExpr 2) (Logic.plus (intExpr (-1)) (clog2 (intExpr z))) =
      natExpr (2 ^ (clog2Nat z.toNat - 1)) := by
  have hz0 : 0 < z := by omega
  have hclog : 0 < clog2Nat z.toNat := clog2Nat_pos (int_toNat_gt_one hz)
  have hnonneg : ¬ (-1 + Int.ofNat (clog2Nat z.toNat) < 0) := by
    have : (1 : Int) ≤ Int.ofNat (clog2Nat z.toNat) :=
      Int.ofNat_le.mpr (Nat.succ_le_of_lt hclog)
    omega
  simp [Logic.expt, Logic.plus, clog2, intExpr, natExpr, hz0]
  have htoNat : (-1 + (clog2Nat z.toNat : Int)).toNat = clog2Nat z.toNat - 1 := by
    calc
      (-1 + (clog2Nat z.toNat : Int)).toNat = (((clog2Nat z.toNat : Nat) : Int) - 1).toNat := by
        omega
      _ = clog2Nat z.toNat - 1 := by
        simp
  change
    (if -1 + (clog2Nat z.toNat : Int) < 0 then intExpr 0
      else intExpr (2 ^ ((-1 + (clog2Nat z.toNat : Int)).toNat))) =
      intExpr (2 ^ (clog2Nat z.toNat - 1))
  have hIf :
      (if -1 + (clog2Nat z.toNat : Int) < 0 then intExpr 0
        else intExpr (2 ^ ((-1 + (clog2Nat z.toNat : Int)).toNat))) =
        intExpr (2 ^ ((-1 + (clog2Nat z.toNat : Int)).toNat)) := by
    exact if_neg hnonneg
  rw [hIf, htoNat]

private theorem nbrCallsClog2Nat_eq_1_plus_clog2Nat {n : Nat} (h : 0 < n) :
    nbrCallsClog2Nat n = clog2Nat n + 1 := by
  simp [nbrCallsClog2Nat, Nat.ne_of_gt h]

/--
Reconstruction of ACL2 theorem `natp-clog2` from
`acl2_samples/2009-log2.lisp`.
-/
theorem natp_clog2 (n : SExpr) :
    Logic.toBool
      (Logic.implies (Logic.and (Logic.integerp n) (Logic.gt n (intExpr 0)))
        (Logic.ge (clog2 n) (intExpr 0))) = true := by
  cases n with
  | nil =>
      simp [Logic.implies, Logic.integerp]
  | cons a d =>
      simp [Logic.implies, Logic.integerp]
  | atom a =>
      cases a with
      | number value =>
          cases value with
          | int z =>
              by_cases hz : 0 < z
              · have hGe : Logic.ge (clog2 (intExpr z)) (intExpr 0) = .atom (.bool true) := by
                  rw [clog2_eq_natExpr_of_pos hz]
                  simp [Logic.ge, intExpr, natExpr]
                change
                  Logic.toBool
                    (Logic.implies
                      (Logic.and (Logic.integerp (intExpr z)) (Logic.gt (intExpr z) (intExpr 0)))
                      (Logic.ge (clog2 (intExpr z)) (intExpr 0))) = true
                rw [show Logic.and (Logic.integerp (intExpr z)) (Logic.gt (intExpr z) (intExpr 0)) =
                    .atom (.bool true) by
                  simp [Logic.and, Logic.integerp, Logic.gt, intExpr, hz]]
                rw [hGe]
                rfl
              · simp [Logic.implies, Logic.and, Logic.integerp, Logic.gt, intExpr, hz]
          | _ =>
              simp [Logic.implies, Logic.integerp]
      | _ =>
          simp [Logic.implies, Logic.integerp]

/--
Reconstruction of ACL2 theorem `posp-clog2` from
`acl2_samples/2009-log2.lisp`.
-/
theorem posp_clog2 (n : SExpr) :
    Logic.toBool
      (Logic.implies (Logic.and (Logic.integerp n) (Logic.gt n (intExpr 1)))
        (Logic.gt (clog2 n) (intExpr 0))) = true := by
  cases n with
  | nil =>
      simp [Logic.implies, Logic.integerp]
  | cons a d =>
      simp [Logic.implies, Logic.integerp]
  | atom a =>
      cases a with
      | number value =>
          cases value with
          | int z =>
              by_cases hz : 1 < z
              · have hz0 : 0 < z := by omega
                have hGt : Logic.gt (clog2 (intExpr z)) (intExpr 0) = .atom (.bool true) := by
                  rw [clog2_eq_natExpr_of_pos hz0]
                  simp [Logic.gt, intExpr, natExpr, clog2Nat_pos (int_toNat_gt_one hz)]
                change
                  Logic.toBool
                    (Logic.implies
                      (Logic.and (Logic.integerp (intExpr z)) (Logic.gt (intExpr z) (intExpr 1)))
                      (Logic.gt (clog2 (intExpr z)) (intExpr 0))) = true
                rw [show Logic.and (Logic.integerp (intExpr z)) (Logic.gt (intExpr z) (intExpr 1)) =
                    .atom (.bool true) by
                  simp [Logic.and, Logic.integerp, Logic.gt, intExpr, hz]]
                rw [hGt]
                rfl
              · simp [Logic.implies, Logic.and, Logic.integerp, Logic.gt, intExpr, hz]
          | _ =>
              simp [Logic.implies, Logic.integerp]
      | _ =>
          simp [Logic.implies, Logic.integerp]

/--
Reconstruction of ACL2 theorem `clog2-is-correct-lower` from
`acl2_samples/2009-log2.lisp`.
-/
theorem clog2_is_correct_lower (n : SExpr) :
    Logic.toBool
      (Logic.implies (Logic.posp n)
        (Logic.lt (Logic.expt (intExpr 2) (Logic.plus (intExpr (-1)) (clog2 n))) n)) = true := by
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
              · by_cases h1 : z = 1
                · subst h1
                  have hLt :
                      Logic.lt (Logic.expt (intExpr 2) (Logic.plus (intExpr (-1)) (clog2 (intExpr 1))))
                        (intExpr 1) = .atom (.bool true) := by
                    decide
                  change
                    Logic.toBool
                      (Logic.implies (Logic.posp (intExpr 1))
                        (Logic.lt (Logic.expt (intExpr 2) (Logic.plus (intExpr (-1)) (clog2 (intExpr 1))))
                          (intExpr 1))) = true
                  rw [show Logic.posp (intExpr 1) = .atom (.bool true) by
                    simp [Logic.posp, intExpr]]
                  rw [hLt]
                  rfl
                · have hzNat : 0 < z.toNat := int_toNat_pos hz
                  have hzNat1 : 1 < z.toNat := by
                    have : 1 < z := by omega
                    exact int_toNat_gt_one this
                  have hNat : 2 ^ (clog2Nat z.toNat - 1) < z.toNat :=
                    two_pow_pred_clog2Nat_lt_self hzNat1
                  have hzNonneg : 0 ≤ z := by omega
                  have hInt : (2 ^ (clog2Nat z.toNat - 1) : Int) < z := by
                    simpa [Int.toNat_of_nonneg hzNonneg] using (Int.ofNat_lt.mpr hNat)
                  have hLt :
                      Logic.lt (Logic.expt (intExpr 2) (Logic.plus (intExpr (-1)) (clog2 (intExpr z))))
                        (intExpr z) = .atom (.bool true) := by
                    rw [expt_two_pred_clog2_eq_natExpr_of_gt_one (by omega : 1 < z)]
                    simpa [Logic.lt, intExpr, natExpr] using hInt
                  change
                    Logic.toBool
                      (Logic.implies (Logic.posp (intExpr z))
                        (Logic.lt (Logic.expt (intExpr 2) (Logic.plus (intExpr (-1)) (clog2 (intExpr z))))
                          (intExpr z))) = true
                  rw [show Logic.posp (intExpr z) = .atom (.bool true) by
                    simp [Logic.posp, intExpr, hz]]
                  rw [hLt]
                  rfl
              · simp [Logic.implies, Logic.posp, hz]
          | _ =>
              simp [Logic.implies, Logic.posp]
      | _ =>
          simp [Logic.implies, Logic.posp]

/--
Reconstruction of ACL2 theorem `clog2-is-correct-upper` from
`acl2_samples/2009-log2.lisp`.
-/
theorem clog2_is_correct_upper (n : SExpr) :
    Logic.toBool
      (Logic.implies (Logic.natp n)
        (Logic.le n (Logic.expt (intExpr 2) (clog2 n)))) = true := by
  cases n with
  | nil =>
      simp [Logic.implies, Logic.natp]
  | cons a d =>
      simp [Logic.implies, Logic.natp]
  | atom a =>
      cases a with
      | number value =>
          cases value with
          | int z =>
              by_cases hz : 0 < z
              · have hNat : z.toNat ≤ 2 ^ clog2Nat z.toNat :=
                  self_le_two_pow_clog2Nat z.toNat
                have hzNonneg : 0 ≤ z := by omega
                have hInt : z ≤ Int.ofNat (2 ^ clog2Nat z.toNat) := by
                  simpa [Int.toNat_of_nonneg hzNonneg] using (Int.ofNat_le.mpr hNat)
                have hLe : Logic.le (intExpr z) (Logic.expt (intExpr 2) (clog2 (intExpr z))) =
                    .atom (.bool true) := by
                  rw [expt_two_clog2_eq_natExpr_of_pos hz]
                  simpa [Logic.le, intExpr, natExpr] using hInt
                change
                  Logic.toBool
                    (Logic.implies (Logic.natp (intExpr z))
                      (Logic.le (intExpr z) (Logic.expt (intExpr 2) (clog2 (intExpr z))))) = true
                rw [show Logic.natp (intExpr z) = .atom (.bool true) by
                  simp [Logic.natp, intExpr, hzNonneg]]
                rw [hLe]
                rfl
              · by_cases hz0 : z = 0
                · subst hz0
                  have hLe : Logic.le (intExpr 0) (Logic.expt (intExpr 2) (clog2 (intExpr 0))) =
                      .atom (.bool true) := by
                    decide
                  change
                    Logic.toBool
                      (Logic.implies (Logic.natp (intExpr 0))
                        (Logic.le (intExpr 0) (Logic.expt (intExpr 2) (clog2 (intExpr 0))))) = true
                  rw [show Logic.natp (intExpr 0) = .atom (.bool true) by
                    simp [Logic.natp, intExpr]]
                  rw [hLe]
                  rfl
                · have hneg : ¬ 0 ≤ z := by omega
                  simp [Logic.implies, Logic.natp, hneg]
          | _ =>
              simp [Logic.implies, Logic.natp]
      | _ =>
          simp [Logic.implies, Logic.natp]

/--
Reconstruction of ACL2 theorem `clog2-is-correct` from
`acl2_samples/2009-log2.lisp`.
-/
theorem clog2_is_correct (n : SExpr) :
    Logic.toBool
      (Logic.implies (Logic.posp n)
        (Logic.and
          (Logic.lt (Logic.expt (intExpr 2) (Logic.plus (intExpr (-1)) (clog2 n))) n)
          (Logic.le n (Logic.expt (intExpr 2) (clog2 n))))) = true := by
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
              · by_cases h1 : z = 1
                · subst h1
                  have hLt :
                      Logic.lt (Logic.expt (intExpr 2) (Logic.plus (intExpr (-1)) (clog2 (intExpr 1))))
                        (intExpr 1) = .atom (.bool true) := by
                    decide
                  have hLe :
                      Logic.le (intExpr 1) (Logic.expt (intExpr 2) (clog2 (intExpr 1))) =
                        .atom (.bool true) := by
                    decide
                  change
                    Logic.toBool
                      (Logic.implies (Logic.posp (intExpr 1))
                        (Logic.and
                          (Logic.lt (Logic.expt (intExpr 2) (Logic.plus (intExpr (-1)) (clog2 (intExpr 1))))
                            (intExpr 1))
                          (Logic.le (intExpr 1) (Logic.expt (intExpr 2) (clog2 (intExpr 1)))))) = true
                  rw [show Logic.posp (intExpr 1) = .atom (.bool true) by
                    simp [Logic.posp, intExpr]]
                  rw [show
                    Logic.and
                      (Logic.lt (Logic.expt (intExpr 2) (Logic.plus (intExpr (-1)) (clog2 (intExpr 1))))
                        (intExpr 1))
                      (Logic.le (intExpr 1) (Logic.expt (intExpr 2) (clog2 (intExpr 1)))) =
                    .atom (.bool true) by
                    rw [hLt, hLe]
                    rfl]
                  rfl
                · have hzNat : 0 < z.toNat := int_toNat_pos hz
                  have hzNat1 : 1 < z.toNat := by
                    have : 1 < z := by omega
                    exact int_toNat_gt_one this
                  have hLowerNat : 2 ^ (clog2Nat z.toNat - 1) < z.toNat :=
                    two_pow_pred_clog2Nat_lt_self hzNat1
                  have hUpperNat : z.toNat ≤ 2 ^ clog2Nat z.toNat :=
                    self_le_two_pow_clog2Nat z.toNat
                  have hzNonneg : 0 ≤ z := by omega
                  have hLowerInt : (2 ^ (clog2Nat z.toNat - 1) : Int) < z := by
                    simpa [Int.toNat_of_nonneg hzNonneg] using (Int.ofNat_lt.mpr hLowerNat)
                  have hUpperInt : z ≤ Int.ofNat (2 ^ clog2Nat z.toNat) := by
                    simpa [Int.toNat_of_nonneg hzNonneg] using (Int.ofNat_le.mpr hUpperNat)
                  have hLt :
                      Logic.lt (Logic.expt (intExpr 2) (Logic.plus (intExpr (-1)) (clog2 (intExpr z))))
                        (intExpr z) = .atom (.bool true) := by
                    rw [expt_two_pred_clog2_eq_natExpr_of_gt_one (by omega : 1 < z)]
                    simpa [Logic.lt, intExpr, natExpr] using hLowerInt
                  have hLe :
                      Logic.le (intExpr z) (Logic.expt (intExpr 2) (clog2 (intExpr z))) =
                        .atom (.bool true) := by
                    rw [expt_two_clog2_eq_natExpr_of_pos hz]
                    simpa [Logic.le, intExpr, natExpr] using hUpperInt
                  change
                    Logic.toBool
                      (Logic.implies (Logic.posp (intExpr z))
                        (Logic.and
                          (Logic.lt (Logic.expt (intExpr 2) (Logic.plus (intExpr (-1)) (clog2 (intExpr z))))
                            (intExpr z))
                          (Logic.le (intExpr z) (Logic.expt (intExpr 2) (clog2 (intExpr z)))))) = true
                  rw [show Logic.posp (intExpr z) = .atom (.bool true) by
                    simp [Logic.posp, intExpr, hz]]
                  rw [show
                    Logic.and
                      (Logic.lt (Logic.expt (intExpr 2) (Logic.plus (intExpr (-1)) (clog2 (intExpr z))))
                        (intExpr z))
                      (Logic.le (intExpr z) (Logic.expt (intExpr 2) (clog2 (intExpr z)))) =
                    .atom (.bool true) by
                    rw [hLt, hLe]
                    rfl]
                  rfl
              · simp [Logic.implies, Logic.posp, hz]
          | _ =>
              simp [Logic.implies, Logic.posp]
      | _ =>
          simp [Logic.implies, Logic.posp]

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
