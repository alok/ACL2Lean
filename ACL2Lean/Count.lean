import ACL2Lean.Logic

namespace ACL2

open Logic hiding toBool

/-- ACL2-count structural size measure for termination proofs.
    Returns 0 for nil and atoms, and `1 + car.acl2Count + cdr.acl2Count` for cons cells. -/
def SExpr.acl2Count : SExpr → Nat
  | .nil => 0
  | .atom _ => 0
  | .cons a b => 1 + a.acl2Count + b.acl2Count

@[simp] theorem acl2Count_nil : SExpr.nil.acl2Count = 0 := rfl

@[simp] theorem acl2Count_atom (a : Atom) : (SExpr.atom a).acl2Count = 0 := rfl

@[simp] theorem acl2Count_cons (a b : SExpr) :
    (SExpr.cons a b).acl2Count = 1 + a.acl2Count + b.acl2Count := rfl

/-- car of a cons has strictly smaller acl2Count. -/
theorem acl2Count_car_lt (a b : SExpr) :
    a.acl2Count < (SExpr.cons a b).acl2Count := by
  simp [SExpr.acl2Count]; omega

/-- cdr of a cons has strictly smaller acl2Count. -/
theorem acl2Count_cdr_lt (a b : SExpr) :
    b.acl2Count < (SExpr.cons a b).acl2Count := by
  simp [SExpr.acl2Count]; omega

/-- acl2Count of car decreases for consp values. -/
theorem acl2Count_car_lt_of_consp {x : SExpr}
    (h : Logic.toBool (consp x) = true) :
    (car x).acl2Count < x.acl2Count := by
  cases x with
  | nil => simp [consp, Logic.toBool] at h
  | atom _ => simp [consp, Logic.toBool] at h
  | cons a b => simp [car, SExpr.acl2Count]; omega

/-- acl2Count of cdr decreases for consp values. -/
theorem acl2Count_cdr_lt_of_consp {x : SExpr}
    (h : Logic.toBool (consp x) = true) :
    (cdr x).acl2Count < x.acl2Count := by
  cases x with
  | nil => simp [consp, Logic.toBool] at h
  | atom _ => simp [consp, Logic.toBool] at h
  | cons a b => simp [cdr, SExpr.acl2Count]; omega

/-- acl2Count of cdr decreases when endp is false (not at end of list). -/
theorem acl2Count_cdr_lt_of_not_endp {x : SExpr}
    (h : Logic.toBool (endp x) = false) :
    (cdr x).acl2Count < x.acl2Count := by
  cases x with
  | nil => simp [endp, Logic.toBool] at h
  | atom _ => simp [endp, Logic.toBool] at h
  | cons a b => simp [cdr, SExpr.acl2Count]; omega

end ACL2
