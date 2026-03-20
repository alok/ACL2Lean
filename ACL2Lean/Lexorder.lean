import ACL2Lean.Logic

namespace ACL2

open Logic

/-- Ordering among Atom kinds: number < keyword < string < symbol.
    Follows ACL2's ordering convention. -/
def atomKind : Atom → Nat
  | .number _ => 0
  | .keyword _ => 1
  | .string _ => 2
  | .symbol _ => 3

/-- `lexorder x y` — total ordering on SExpr values.
    nil is smallest, atoms ordered by kind then value, conses are largest
    and compared lexicographically (car then cdr). -/
def lexorder (x y : SExpr) : SExpr :=
  match x, y with
  | .nil, _ => .t          -- nil ≤ everything
  | _, .nil => .nil                         -- nothing > nil except nil
  | .atom a, .atom b =>
    if atomKind a < atomKind b then .t
    else if atomKind a > atomKind b then .nil
    else -- same kind
      match a, b with
      | .number (.int m), .number (.int n) => if m ≤ n then .t else .nil
      | .keyword k1, .keyword k2 => if k1 ≤ k2 then .t else .nil
      | .string s1, .string s2 => if s1 ≤ s2 then .t else .nil
      | .symbol s1, .symbol s2 =>
        if s1.name < s2.name then .t
        else if s1.name = s2.name then
          if s1.package ≤ s2.package then .t else .nil
        else .nil
      -- Mixed number subtypes (int vs rational vs decimal)
      | .number (.int _), .number _ => .t
      | .number _, .number (.int _) => .nil
      | .number (.rational n1 d1), .number (.rational n2 d2) =>
        if n1 * ↑d2 ≤ n2 * ↑d1 then .t else .nil
      | .number (.rational _ _), .number (.decimal _ _) => .t
      | .number (.decimal _ _), .number (.rational _ _) => .nil
      | .number (.decimal m1 e1), .number (.decimal m2 e2) =>
        if e1 < e2 then .t
        else if e1 = e2 then if m1 ≤ m2 then .t else .nil
        else .nil
      | _, _ => .nil -- unreachable (same kind guarantees same constructor)
  | .atom _, .cons _ _ => .t  -- atoms before conses
  | .cons _ _, .atom _ => .nil
  | .cons a1 b1, .cons a2 b2 =>
    if a1 == a2 then lexorder b1 b2
    else lexorder a1 a2

@[simp] theorem lexorder_nil (y : SExpr) : lexorder .nil y = .t := by
  cases y <;> rfl

/-- `lexorder x x = t` for all x (reflexivity). -/
theorem lexorder_refl (x : SExpr) : lexorder x x = .t := by
  induction x with
  | nil => rfl
  | atom a =>
    simp only [lexorder, show ¬(atomKind a < atomKind a) from Nat.lt_irrefl _, ite_false,
               show ¬(atomKind a > atomKind a) from Nat.lt_irrefl _, ite_false]
    cases a with
    | number n =>
      cases n with
      | int k => simp
      | rational n d => simp
      | decimal m e => simp
    | keyword k => simp
    | string s => simp
    | symbol s => simp [show ¬(s.name < s.name) from String.lt_irrefl _]
  | cons a b _ ihb => simp only [lexorder, beq_self_eq_true, ite_true]; exact ihb

set_option maxHeartbeats 400000 in
/-- `lexorder x y = t ∨ lexorder y x = t` for all x, y (totality). -/
theorem lexorder_total (x y : SExpr) :
    Logic.toBool (lexorder x y) = true ∨ Logic.toBool (lexorder y x) = true := by
  induction x, y using lexorder.induct with
  -- nil ≤ everything
  | case1 y => left; simp [lexorder, Logic.toBool]
  -- x ≠ nil, nil → right (nil ≤ x)
  | case2 t _ => right; simp [lexorder, Logic.toBool]
  -- atom a, atom b with kind a < kind b → left
  | case3 a b hlt => left; simp [lexorder, hlt, Logic.toBool]
  -- atom a, atom b with kind a > kind b → right (kind b < kind a)
  | case4 a b _ hgt => right; simp [lexorder, Logic.toBool, show atomKind b < atomKind a from hgt]
  -- int m ≤ n → left
  | case5 m n hle _ _ => left; simp [lexorder, atomKind, Logic.toBool, hle]
  -- int ¬(m ≤ n) → right (n ≤ m)
  | case6 m n hnle _ _ =>
    right; simp [lexorder, atomKind, Logic.toBool, show n ≤ m from Int.le_of_lt (Int.not_le.mp hnle)]
  -- keyword k1 ≤ k2 → left
  | case7 k1 k2 hle _ _ => left; simp [lexorder, atomKind, Logic.toBool, hle]
  -- keyword ¬(k1 ≤ k2) → right (k2 ≤ k1)
  | case8 k1 k2 hnle _ _ =>
    right; simp [lexorder, atomKind, Logic.toBool,
      show k2 ≤ k1 from fun h => String.lt_asymm (String.not_le.mp hnle) h]
  -- string s1 ≤ s2 → left
  | case9 s1 s2 hle _ _ => left; simp [lexorder, atomKind, Logic.toBool, hle]
  -- string ¬(s1 ≤ s2) → right (s2 ≤ s1)
  | case10 s1 s2 hnle _ _ =>
    right; simp [lexorder, atomKind, Logic.toBool,
      show s2 ≤ s1 from fun h => String.lt_asymm (String.not_le.mp hnle) h]
  -- symbol s1.name < s2.name → left
  | case11 s1 s2 hlt _ _ => left; simp [lexorder, atomKind, Logic.toBool, hlt]
  -- symbol name equal, package ≤ → left
  | case12 s1 s2 _ heq hle _ _ => left; simp [lexorder, atomKind, Logic.toBool, heq, hle]
  -- symbol name equal, ¬(package ≤) → right (reverse package ≤)
  | case13 s1 s2 _ heq hnle _ _ =>
    right; simp [lexorder, atomKind, Logic.toBool, heq.symm,
      show s2.package ≤ s1.package from fun h => String.lt_asymm (String.not_le.mp hnle) h]
  -- symbol ¬(name <), ¬(name =) → right (reverse name <)
  | case14 s1 s2 hnlt hneq _ _ =>
    have hlt2 : s2.name < s1.name := by
      rw [show (s2.name < s1.name) ↔ ¬(s1.name ≤ s2.name) from String.not_le.symm]
      intro hle; exact hneq (String.le_antisymm hle (fun h => hnlt h))
    right; simp [lexorder, atomKind, Logic.toBool, hlt2]
  -- int _, number _ (not int) → left
  | case15 _ _ _ _ _ => left; simp [lexorder, atomKind, Logic.toBool]
  -- number _ (not int), int _ → right
  | case16 _ _ _ _ _ => right; simp [lexorder, atomKind, Logic.toBool]
  -- rational, n1*d2 ≤ n2*d1 → left
  | case17 n1 d1 n2 d2 hle _ _ => left; simp [lexorder, atomKind, Logic.toBool, hle]
  -- rational, ¬(n1*d2 ≤ n2*d1) → right
  | case18 n1 d1 n2 d2 hnle _ _ =>
    right; simp [lexorder, atomKind, Logic.toBool,
      show n2 * ↑d1 ≤ n1 * ↑d2 from Int.le_of_lt (Int.not_le.mp hnle)]
  -- rational, decimal → left
  | case19 _ _ _ _ _ _ => left; simp [lexorder, atomKind, Logic.toBool]
  -- decimal, rational → right
  | case20 _ _ _ _ _ _ => right; simp [lexorder, atomKind, Logic.toBool]
  -- decimal e1 < e2 → left
  | case21 _ _ _ _ hlt _ _ => left; simp [lexorder, atomKind, Logic.toBool, hlt]
  -- decimal e1 = e2, m1 ≤ m2 → left
  | case22 _ _ _ hle _ _ _ => left; simp [lexorder, atomKind, Logic.toBool, hle]
  -- decimal e1 = e2, ¬(m1 ≤ m2) → right (m2 ≤ m1)
  | case23 m1 m2 _ hnle _ _ _ =>
    right; simp [lexorder, atomKind, Logic.toBool,
      show m2 ≤ m1 from Int.le_of_lt (Int.not_le.mp hnle)]
  -- decimal ¬(e1 < e2), ¬(e1 = e2) → right (e2 < e1)
  | case24 _ e1 _ e2 hnlt hneq _ _ =>
    right; simp [lexorder, atomKind, Logic.toBool, show e2 < e1 from by omega]
  -- catch-all: same kind but no specific pair matches → contradiction
  | case25 a b hka1 hka2 _ h_kw h_str h_sym h_int_num h_num_int h_rat_rat h_rat_dec h_dec_rat h_dec_dec =>
    exfalso
    have hkeq : atomKind a = atomKind b := Nat.le_antisymm (Nat.not_lt.mp hka2) (Nat.not_lt.mp hka1)
    cases a with
    | number n1 =>
      cases b with
      | number n2 =>
        cases n1 with
        | int v1 => exact h_int_num v1 n2 rfl rfl
        | rational num1 den1 =>
          cases n2 with
          | int v2 => exact h_num_int (.rational num1 den1) v2 rfl rfl
          | rational num2 den2 => exact h_rat_rat num1 den1 num2 den2 rfl rfl
          | decimal m2 e2 => exact h_rat_dec num1 den1 m2 e2 rfl rfl
        | decimal m1 e1 =>
          cases n2 with
          | int v2 => exact h_num_int (.decimal m1 e1) v2 rfl rfl
          | rational num2 den2 => exact h_dec_rat m1 e1 num2 den2 rfl rfl
          | decimal m2 e2 => exact h_dec_dec m1 e1 m2 e2 rfl rfl
      | keyword _ => simp [atomKind] at hkeq
      | string _ => simp [atomKind] at hkeq
      | symbol _ => simp [atomKind] at hkeq
    | keyword k1 =>
      cases b with
      | keyword k2 => exact h_kw k1 k2 rfl rfl
      | _ => simp [atomKind] at hkeq
    | string s1 =>
      cases b with
      | string s2 => exact h_str s1 s2 rfl rfl
      | _ => simp [atomKind] at hkeq
    | symbol s1 =>
      cases b with
      | symbol s2 => exact h_sym s1 s2 rfl rfl
      | _ => simp [atomKind] at hkeq
  -- atom vs cons → left
  | case26 _ _ _ => left; simp [lexorder, Logic.toBool]
  -- cons vs atom → right
  | case27 _ _ _ => right; simp [lexorder, Logic.toBool]
  -- cons a1 b1, cons a2 b2 with a1 == a2 → IH on b1, b2
  | case28 a1 b1 a2 b2 heq ih =>
    simp only [lexorder, heq]
    have : (a2 == a1) = true := by simp [beq_iff_eq] at heq ⊢; exact heq.symm
    simp only [this, ite_true]
    exact ih
  -- cons a1 b1, cons a2 b2 with ¬(a1 == a2) → IH on a1, a2
  | case29 a1 b1 a2 b2 hne ih =>
    simp only [lexorder, hne]
    have : ¬(a2 == a1) = true := by simp only [beq_iff_eq] at hne ⊢; exact fun h => hne h.symm
    simp only [this]
    exact ih

/-- Antisymmetry restricted to integers. Fully proved. -/
theorem lexorder_antisym_int (m n : Int)
    (hxy : Logic.toBool (lexorder (.atom (.number (.int m))) (.atom (.number (.int n)))) = true)
    (hyx : Logic.toBool (lexorder (.atom (.number (.int n))) (.atom (.number (.int m)))) = true) :
    SExpr.atom (.number (.int m)) = SExpr.atom (.number (.int n)) := by
  simp only [lexorder, atomKind, Nat.lt_irrefl, ite_false, Logic.toBool] at hxy hyx
  split at hxy <;> split at hyx <;> simp_all
  congr; omega

/-- Antisymmetry (general case sorry'd). -/
theorem lexorder_antisym (x y : SExpr)
    (hxy : Logic.toBool (lexorder x y) = true)
    (hyx : Logic.toBool (lexorder y x) = true) :
    x = y := by
  sorry

/-- Transitivity restricted to integers. Fully proved. -/
theorem lexorder_trans_int (a b c : Int)
    (hab : Logic.toBool (lexorder (.atom (.number (.int a))) (.atom (.number (.int b)))) = true)
    (hbc : Logic.toBool (lexorder (.atom (.number (.int b))) (.atom (.number (.int c)))) = true) :
    Logic.toBool (lexorder (.atom (.number (.int a))) (.atom (.number (.int c)))) = true := by
  simp only [lexorder, atomKind, Nat.lt_irrefl, ite_false, Logic.toBool] at *
  split at hab <;> split at hbc <;> simp_all
  simp [show a ≤ c by omega]

/-- Transitivity (general case sorry'd). -/
theorem lexorder_trans (x y z : SExpr)
    (hxy : Logic.toBool (lexorder x y) = true)
    (hyz : Logic.toBool (lexorder y z) = true) :
    Logic.toBool (lexorder x z) = true := by
  sorry

end ACL2
