import ACL2Lean.Logic

namespace ACL2

open Logic

/-- Ordering among Atom kinds: number < bool < keyword < string < symbol.
    Follows ACL2's ordering convention. -/
private def atomKind : Atom → Nat
  | .number _ => 0
  | .bool _ => 1
  | .keyword _ => 2
  | .string _ => 3
  | .symbol _ => 4

/-- `lexorder x y` — total ordering on SExpr values.
    nil is smallest, atoms ordered by kind then value, conses are largest
    and compared lexicographically (car then cdr). -/
def lexorder (x y : SExpr) : SExpr :=
  match x, y with
  | .nil, _ => .atom (.bool true)          -- nil ≤ everything
  | _, .nil => .nil                         -- nothing > nil except nil
  | .atom a, .atom b =>
    if atomKind a < atomKind b then .atom (.bool true)
    else if atomKind a > atomKind b then .nil
    else -- same kind
      match a, b with
      | .number (.int m), .number (.int n) => if m ≤ n then .atom (.bool true) else .nil
      | .bool b1, .bool b2 => if (!b1 || b2) then .atom (.bool true) else .nil
      | .keyword k1, .keyword k2 => if k1 ≤ k2 then .atom (.bool true) else .nil
      | .string s1, .string s2 => if s1 ≤ s2 then .atom (.bool true) else .nil
      | .symbol s1, .symbol s2 =>
        if s1.name < s2.name then .atom (.bool true)
        else if s1.name = s2.name then
          if s1.package ≤ s2.package then .atom (.bool true) else .nil
        else .nil
      -- Mixed number subtypes (int vs rational vs decimal)
      | .number (.int _), .number _ => .atom (.bool true)
      | .number _, .number (.int _) => .nil
      | .number (.rational n1 d1), .number (.rational n2 d2) =>
        if n1 * ↑d2 ≤ n2 * ↑d1 then .atom (.bool true) else .nil
      | .number (.rational _ _), .number (.decimal _ _) => .atom (.bool true)
      | .number (.decimal _ _), .number (.rational _ _) => .nil
      | .number (.decimal m1 e1), .number (.decimal m2 e2) =>
        if e1 < e2 then .atom (.bool true)
        else if e1 = e2 then if m1 ≤ m2 then .atom (.bool true) else .nil
        else .nil
      | _, _ => .nil -- unreachable (same kind guarantees same constructor)
  | .atom _, .cons _ _ => .atom (.bool true)  -- atoms before conses
  | .cons _ _, .atom _ => .nil
  | .cons a1 b1, .cons a2 b2 =>
    if a1 == a2 then lexorder b1 b2
    else lexorder a1 a2

@[simp] theorem lexorder_nil (y : SExpr) : lexorder .nil y = .atom (.bool true) := by
  cases y <;> rfl

/-- `lexorder x x = t` for all x (reflexivity). -/
theorem lexorder_refl (x : SExpr) : lexorder x x = .atom (.bool true) := by
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
    | bool b => cases b <;> simp
    | keyword k => simp
    | string s => simp
    | symbol s => simp [show ¬(s.name < s.name) from String.lt_irrefl _]
  | cons a b _ ihb => simp only [lexorder, beq_self_eq_true, ite_true]; exact ihb

/-- `lexorder x y = t ∨ lexorder y x = t` for all x, y (totality).
    The original prototype proved this using functional induction (`lexorder.induct`).
    For SExpr, Lean uses structural recursion which does not generate the `.induct`
    principle, making the proof significantly harder. Sorry'd for now. -/
theorem lexorder_total (x y : SExpr) :
    Logic.toBool (lexorder x y) = true ∨ Logic.toBool (lexorder y x) = true := by
  sorry

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
