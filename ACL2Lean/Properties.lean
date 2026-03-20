import ACL2Lean.Logic

namespace ACL2
namespace Properties

open Logic

/-- consp is boolean-valued: returns t or nil. -/
theorem consp_bool_valued (x : SExpr) :
    consp x = .atom (.bool true) ∨ consp x = .nil := by
  cases x with
  | nil => right; rfl
  | atom _ => right; rfl
  | cons _ _ => left; rfl

/-- atom is boolean-valued: returns t or nil. -/
theorem atom_bool_valued (x : SExpr) :
    Logic.atom x = .atom (.bool true) ∨ Logic.atom x = .nil := by
  cases x with
  | nil => left; rfl
  | atom _ => left; rfl
  | cons _ _ => right; rfl

/-- consp and atom are complements. -/
theorem consp_atom_complement (x : SExpr) :
    Logic.toBool (consp x) = true ↔ Logic.toBool (Logic.atom x) = false := by
  cases x <;> simp [consp, Logic.atom, Logic.toBool]

/-- equal is boolean-valued: returns t or nil. -/
theorem equal_bool_valued (x y : SExpr) :
    equal x y = .atom (.bool true) ∨ equal x y = .nil := by
  unfold equal; split
  · left; rfl
  · right; rfl

/-- zp is boolean-valued: returns t or nil. -/
theorem zp_bool_valued (x : SExpr) :
    zp x = .atom (.bool true) ∨ zp x = .nil := by
  simp only [zp]; split
  · left; rfl
  · right; rfl

/-- integerp is boolean-valued: returns t or nil. -/
theorem integerp_bool_valued (x : SExpr) :
    integerp x = .atom (.bool true) ∨ integerp x = .nil := by
  cases x with
  | nil => right; rfl
  | cons _ _ => right; rfl
  | atom a =>
    cases a with
    | symbol _ | keyword _ | string _ | bool _ => right; rfl
    | number n =>
      cases n with
      | int _ => left; rfl
      | rational _ _ => right; rfl
      | decimal _ _ => right; rfl

/-- natp is boolean-valued: returns t or nil. -/
theorem natp_bool_valued (x : SExpr) :
    natp x = .atom (.bool true) ∨ natp x = .nil := by
  cases x with
  | nil => right; rfl
  | cons _ _ => right; rfl
  | atom a =>
    cases a with
    | symbol _ | keyword _ | string _ | bool _ => right; rfl
    | number n =>
      cases n with
      | int k => simp only [natp]; split
                 · left; rfl
                 · right; rfl
      | rational _ _ => right; rfl
      | decimal _ _ => right; rfl

/-- endp is boolean-valued: returns t or nil. -/
theorem endp_bool_valued (x : SExpr) :
    endp x = .atom (.bool true) ∨ endp x = .nil := by
  cases x with
  | nil => left; rfl
  | atom _ => left; rfl
  | cons _ _ => right; rfl

/-- cons is injective. -/
theorem cons_injective {a b c d : SExpr}
    (h : SExpr.cons a b = SExpr.cons c d) : a = c ∧ b = d := by
  cases h; exact ⟨rfl, rfl⟩

theorem cons_inj_left {a b c d : SExpr}
    (h : SExpr.cons a b = SExpr.cons c d) : a = c :=
  (cons_injective h).1

theorem cons_inj_right {a b c d : SExpr}
    (h : SExpr.cons a b = SExpr.cons c d) : b = d :=
  (cons_injective h).2

/-- equal returns t iff arguments are equal. -/
theorem equal_t_iff (x y : SExpr) :
    equal x y = .atom (.bool true) ↔ x = y := by
  unfold equal; split <;> simp_all

/-- equal returns nil iff arguments differ. -/
theorem equal_nil_iff (x y : SExpr) :
    equal x y = .nil ↔ x ≠ y := by
  unfold equal; split <;> simp_all

/-- equal is reflexive. -/
theorem equal_refl (x : SExpr) : equal x x = .atom (.bool true) := by
  simp [equal]

/-- equal is symmetric. -/
theorem equal_symm (x y : SExpr) : equal x y = equal y x := by
  simp only [equal]; split <;> split <;> simp_all

/-- append is associative. -/
theorem append_assoc (x y z : SExpr) :
    append (append x y) z = append x (append y z) := by
  induction x with
  | nil => simp [append]
  | atom _ => simp [append]
  | cons _ b _ ih_cdr => simp [append, ih_cdr]

end Properties
end ACL2
