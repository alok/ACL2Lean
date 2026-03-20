import ACL2Lean.Logic
import ACL2Lean.ImportedRegistry
import ACL2Lean.Tactics

open ACL2 ACL2.Logic

namespace ACL2
namespace Imported
namespace TriSqReplay

private def intExpr (z : Int) : SExpr :=
  .atom (.number (.int z))

private def natExpr (n : Nat) : SExpr :=
  intExpr (Int.ofNat n)

private abbrev PellPair := Nat × Nat

private def pellOne : PellPair := (1, 0)
private def pellUnit : PellPair := (3, 2)

private def pellMul (p q : PellPair) : PellPair :=
  (p.1 * q.1 + 2 * p.2 * q.2, p.1 * q.2 + p.2 * q.1)

private def encodePair (p : PellPair) : SExpr :=
  Logic.list [natExpr p.1, natExpr p.2]

private theorem crossTermTwice (x y : Nat) : x * y + y * x = 2 * x * y := by
  rw [Nat.mul_comm y x]
  calc
    x * y + x * y = 2 * (x * y) := by
      simp [Nat.two_mul]
    _ = 2 * x * y := by
      simp [Nat.mul_assoc]

private theorem pellMul_assoc (a b c : PellPair) :
    pellMul (pellMul a b) c = pellMul a (pellMul b c) := by
  cases a
  cases b
  cases c
  simp [pellMul, Nat.mul_add, Nat.add_mul, Nat.mul_assoc, Nat.add_assoc,
    Nat.add_comm, Nat.add_left_comm, Nat.mul_comm, Nat.mul_left_comm]

private theorem pellMul_one_right (a : PellPair) : pellMul a pellOne = a := by
  cases a
  simp [pellMul, pellOne]

private theorem pellSquare (p : PellPair) :
    pellMul p p = (p.1 * p.1 + 2 * p.2 * p.2, 2 * p.1 * p.2) := by
  cases p
  simp [pellMul, crossTermTwice]

private theorem pellSquareTimesUnit (p : PellPair) :
    pellMul (pellMul p p) pellUnit =
      (3 * p.1 * p.1 + 8 * p.1 * p.2 + 6 * p.2 * p.2,
        2 * p.1 * p.1 + 6 * p.1 * p.2 + 4 * p.2 * p.2) := by
  cases p with
  | mk x y =>
      simp [pellMul, pellUnit, Nat.add_mul, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      constructor
      · have h :
            2 * (x * (y * 2) + x * (y * 2)) = x * (y * 8) := by
          calc
            2 * (x * (y * 2) + x * (y * 2)) = 2 * (2 * (x * (y * 2))) := by
              simp [Nat.two_mul]
            _ = x * (y * 8) := by
              simp [Nat.mul_left_comm]
        rw [h]
        ac_rfl
      · have h₁ :
            2 * (x * x + y * (y * 2)) = x * (x * 2) + y * (y * 4) := by
          simp [Nat.mul_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
        have h₂ :
            x * (y * 3) + x * (y * 3) = x * (y * 6) := by
          calc
            x * (y * 3) + x * (y * 3) = 2 * (x * (y * 3)) := by
              simp [Nat.two_mul]
            _ = x * (y * 6) := by
              simp [Nat.mul_left_comm]
        rw [h₁, h₂]
        ac_rfl

private def pellPow : Nat → PellPair
  | 0 => pellOne
  | n + 1 => pellMul (pellPow n) pellUnit

private theorem pellPow_add (m n : Nat) : pellPow (m + n) = pellMul (pellPow m) (pellPow n) := by
  induction n with
  | zero =>
      simp [pellPow, pellMul_one_right]
  | succ n ih =>
      simp [pellPow, ih]
      exact pellMul_assoc (pellPow m) (pellPow n) pellUnit

private theorem intToNatTwice {z : Int} (hz : 0 < z) : (2 * z).toNat = 2 * z.toNat := by
  apply Int.ofNat.inj
  have hzNonneg : 0 ≤ z := by
    omega
  have h2zNonneg : 0 ≤ 2 * z := by
    omega
  have hzEq : z = Int.ofNat z.toNat := by
    simpa using (Int.toNat_of_nonneg hzNonneg).symm
  calc
    Int.ofNat ((2 * z).toNat) = 2 * z := by
      simpa using (Int.toNat_of_nonneg h2zNonneg)
    _ = 2 * Int.ofNat z.toNat := by
      rw [hzEq]
      simp
    _ = Int.ofNat (2 * z.toNat) := by
      simp

private theorem intToNatTwiceAddOne {z : Int} (hz : 0 < z) :
    (1 + 2 * z).toNat = 2 * z.toNat + 1 := by
  apply Int.ofNat.inj
  have hzNonneg : 0 ≤ z := by
    omega
  have h2z1Nonneg : 0 ≤ 1 + 2 * z := by
    omega
  have hzEq : z = Int.ofNat z.toNat := by
    simpa using (Int.toNat_of_nonneg hzNonneg).symm
  calc
    Int.ofNat ((1 + 2 * z).toNat) = 1 + 2 * z := by
      simpa using (Int.toNat_of_nonneg h2z1Nonneg)
    _ = 1 + 2 * Int.ofNat z.toNat := by
      rw [hzEq]
      simp
    _ = Int.ofNat (2 * z.toNat + 1) := by
      simp [Nat.add_comm]

private theorem pellPow_twice (n : Nat) :
    pellPow (2 * n) = pellMul (pellPow n) (pellPow n) := by
  simpa [Nat.two_mul] using (pellPow_add n n)

private theorem pellPow_twiceAddOne (n : Nat) :
    pellPow (2 * n + 1) = pellMul (pellMul (pellPow n) (pellPow n)) pellUnit := by
  simp [pellPow, pellPow_twice]

/--
Proof-friendly imported version of ACL2 `pair-pow`.
-/
def pair_pow : SExpr → SExpr
  | .atom (.number (.int z)) =>
      if 0 < z then encodePair (pellPow z.toNat) else encodePair pellUnit
  | _ => encodePair pellUnit

private theorem pairPow_eq_encode_of_pos {z : Int} (hz : 0 < z) :
    pair_pow (intExpr z) = encodePair (pellPow z.toNat) := by
  simp [pair_pow, intExpr, hz]

private theorem first_encodePair (p : PellPair) : Logic.first (encodePair p) = natExpr p.1 := by
  cases p
  rfl

private theorem second_encodePair (p : PellPair) : Logic.second (encodePair p) = natExpr p.2 := by
  cases p
  rfl

private theorem pairPow_even_of_pos {z : Int} (hz : 0 < z) :
    pair_pow (Logic.times (intExpr 2) (intExpr z)) =
      Logic.list
        [natExpr ((pellPow z.toNat).1 * (pellPow z.toNat).1 + 2 * (pellPow z.toNat).2 * (pellPow z.toNat).2)
        , natExpr (2 * (pellPow z.toNat).1 * (pellPow z.toNat).2)
        ] := by
  have h2z : 0 < 2 * z := by
    omega
  simp [Logic.times, intExpr]
  have hPair :
      pair_pow (SExpr.atom (.number (.int (2 * z)))) =
        encodePair (pellPow (2 * z).toNat) := by
    simpa [intExpr] using (pairPow_eq_encode_of_pos h2z)
  rw [hPair]
  simp [encodePair, Logic.list, natExpr, intExpr, intToNatTwice hz, pellPow_twice, pellSquare]

private theorem pairPow_odd_of_pos {z : Int} (hz : 0 < z) :
    pair_pow (Logic.plus (intExpr 1) (Logic.times (intExpr 2) (intExpr z))) =
      Logic.list
        [natExpr (3 * (pellPow z.toNat).1 * (pellPow z.toNat).1 +
            8 * (pellPow z.toNat).1 * (pellPow z.toNat).2 +
            6 * (pellPow z.toNat).2 * (pellPow z.toNat).2)
        , natExpr (2 * (pellPow z.toNat).1 * (pellPow z.toNat).1 +
            6 * (pellPow z.toNat).1 * (pellPow z.toNat).2 +
            4 * (pellPow z.toNat).2 * (pellPow z.toNat).2)
        ] := by
  have h2z1 : 0 < 1 + 2 * z := by
    omega
  simp [Logic.plus, Logic.times, intExpr]
  have hPair :
      pair_pow (SExpr.atom (.number (.int (1 + 2 * z)))) =
        encodePair (pellPow (1 + 2 * z).toNat) := by
    simpa [intExpr] using (pairPow_eq_encode_of_pos h2z1)
  rw [hPair]
  simp [encodePair, Logic.list, natExpr, intExpr, intToNatTwiceAddOne hz,
    pellPow_twiceAddOne, pellSquareTimesUnit]

private def pairSquareFrom (pair : SExpr) : SExpr :=
  Logic.list
    [Logic.plus (Logic.times (Logic.first pair) (Logic.first pair))
      (Logic.times (intExpr 2) (Logic.times (Logic.second pair) (Logic.second pair)))
    , Logic.times (intExpr 2) (Logic.times (Logic.first pair) (Logic.second pair))
    ]

private def pairOddFrom (pair : SExpr) : SExpr :=
  Logic.list
    [Logic.plus
      (Logic.times (intExpr 3) (Logic.times (Logic.first pair) (Logic.first pair)))
      (Logic.plus
        (Logic.times (intExpr 8) (Logic.times (Logic.first pair) (Logic.second pair)))
        (Logic.times (intExpr 6) (Logic.times (Logic.second pair) (Logic.second pair))))
    , Logic.plus
      (Logic.times (intExpr 2) (Logic.times (Logic.first pair) (Logic.first pair)))
      (Logic.plus
        (Logic.times (intExpr 6) (Logic.times (Logic.first pair) (Logic.second pair)))
        (Logic.times (intExpr 4) (Logic.times (Logic.second pair) (Logic.second pair))))
    ]

/--
Proof-friendly reconstruction of ACL2 theorem `pair-pow-2n-2n+1` from
`acl2_samples/2009-tri-sq.lisp`.
-/
theorem pair_pow_2n_2n_plus_1 (n : SExpr) :
    Logic.posp n = .atom (.bool true) →
      pair_pow (Logic.times (intExpr 2) n) = pairSquareFrom (pair_pow n) ∧
      pair_pow (Logic.plus (intExpr 1) (Logic.times (intExpr 2) n)) = pairOddFrom (pair_pow n) := by
  cases n with
  | nil =>
      simp [Logic.posp]
  | cons a d =>
      simp [Logic.posp]
  | atom a =>
      cases a with
      | bool b =>
          simp [Logic.posp]
      | string s =>
          simp [Logic.posp]
      | keyword k =>
          simp [Logic.posp]
      | symbol sym =>
          simp [Logic.posp]
      | number num =>
          cases num with
          | int z =>
              by_cases hz : 0 < z
              · intro hPos
                have hPair :
                    pair_pow (SExpr.atom (.number (.int z))) =
                      encodePair (pellPow z.toNat) := by
                  simpa [intExpr] using (pairPow_eq_encode_of_pos hz)
                have hEven :
                    pair_pow (Logic.times (intExpr 2) (SExpr.atom (.number (.int z)))) =
                      Logic.list
                        [natExpr ((pellPow z.toNat).1 * (pellPow z.toNat).1 +
                            2 * (pellPow z.toNat).2 * (pellPow z.toNat).2)
                        , natExpr (2 * (pellPow z.toNat).1 * (pellPow z.toNat).2)
                        ] := by
                  simpa [intExpr] using (pairPow_even_of_pos hz)
                have hOdd :
                    pair_pow (Logic.plus (intExpr 1) (Logic.times (intExpr 2) (SExpr.atom (.number (.int z))))) =
                      Logic.list
                        [natExpr (3 * (pellPow z.toNat).1 * (pellPow z.toNat).1 +
                            8 * (pellPow z.toNat).1 * (pellPow z.toNat).2 +
                            6 * (pellPow z.toNat).2 * (pellPow z.toNat).2)
                        , natExpr (2 * (pellPow z.toNat).1 * (pellPow z.toNat).1 +
                            6 * (pellPow z.toNat).1 * (pellPow z.toNat).2 +
                            4 * (pellPow z.toNat).2 * (pellPow z.toNat).2)
                        ] := by
                  simpa [intExpr] using (pairPow_odd_of_pos hz)
                constructor
                · unfold pairSquareFrom
                  rw [hEven, hPair]
                  rw [first_encodePair (pellPow z.toNat), second_encodePair (pellPow z.toNat)]
                  simp [natExpr, intExpr, Logic.plus, Logic.times]
                  constructor
                  · simp [Int.mul_assoc]
                  · simp [Int.mul_assoc]
                · unfold pairOddFrom
                  rw [hOdd, hPair]
                  rw [first_encodePair (pellPow z.toNat), second_encodePair (pellPow z.toNat)]
                  simp [natExpr, intExpr, Logic.plus, Logic.times]
                  constructor
                  · ac_rfl
                  · ac_rfl
              · simp [Logic.posp, hz]
          | rational num den =>
              simp [Logic.posp]
          | decimal mantissa exponent =>
              simp [Logic.posp]

acl2_imported "pair-pow-2n-2n+1" pair_pow_2n_2n_plus_1

/--
Smoke theorem that validates the instance-capable replay executor on the
real `pair-pow-log-is-correct` instance payload shape from `tri-sq`.
-/
private theorem replay_seed_pair_pow_instance_half (n : SExpr) :
    Logic.posp (Logic.div n (intExpr 2)) = .atom (.bool true) →
      pair_pow (Logic.times (intExpr 2) (Logic.div n (intExpr 2))) =
          pairSquareFrom (pair_pow (Logic.div n (intExpr 2))) ∧
        pair_pow (Logic.plus (intExpr 1) (Logic.times (intExpr 2) (Logic.div n (intExpr 2)))) =
          pairOddFrom (pair_pow (Logic.div n (intExpr 2))) := by
  acl2_use_instance "pair-pow-2n-2n+1" with "((n (/ n 2)))"

/--
Second smoke theorem for the odd predecessor instance shape emitted by ACL2.
-/
private theorem replay_seed_pair_pow_instance_pred_half (n : SExpr) :
    Logic.posp (Logic.div (Logic.plus n (intExpr (-1))) (intExpr 2)) = .atom (.bool true) →
      pair_pow
          (Logic.times (intExpr 2)
            (Logic.div (Logic.plus n (intExpr (-1))) (intExpr 2))) =
        pairSquareFrom
          (pair_pow (Logic.div (Logic.plus n (intExpr (-1))) (intExpr 2))) ∧
        pair_pow
            (Logic.plus (intExpr 1)
              (Logic.times (intExpr 2)
                (Logic.div (Logic.plus n (intExpr (-1))) (intExpr 2)))) =
          pairOddFrom
            (pair_pow (Logic.div (Logic.plus n (intExpr (-1))) (intExpr 2))) := by
  acl2_use_instance "pair-pow-2n-2n+1" with "((n (/ (+ n -1) 2)))"

end TriSqReplay
end Imported
end ACL2
