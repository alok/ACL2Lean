import ACL2Lean.Syntax

namespace ACL2
namespace Logic

open ACL2

/-- ACL2 truthiness: everything except `nil` and `false` is true. -/
def toBool (s : SExpr) : Bool :=
  match s with
  | .nil => false
  | .atom (.bool false) => false
  | _ => true

/-- ACL2 `if` lazy evaluation. -/
def if_ (c t e : SExpr) : SExpr :=
  if toBool c then t else e

/-- Coerce an S-expression to an integer if possible, else 0. -/
def toInt (s : SExpr) : Int :=
  match s with
  | .atom (.number (.int n)) => n
  | _ => 0

/-- ACL2 `zp`: true if `n` is not a positive integer. -/
def zp (n : SExpr) : SExpr :=
  let val := toInt n
  if val <= 0 then .atom (.bool true) else .nil

/-- ACL2 `plus`. -/
def plus (a b : SExpr) : SExpr :=
  .atom (.number (.int (toInt a + toInt b)))

/-- ACL2 `minus`. -/
def minus (a b : SExpr) : SExpr :=
  .atom (.number (.int (toInt a - toInt b)))

/-- ACL2 `times`. -/
def times (a b : SExpr) : SExpr :=
  .atom (.number (.int (toInt a * toInt b)))

/-- ACL2 `div`. -/
def div (a b : SExpr) : SExpr :=
  let x := toInt a
  let y := toInt b
  if y == 0 then .atom (.number (.int 0))
  else if x % y == 0 then .atom (.number (.int (x / y)))
  else .atom (.number (.rational x y.toNat))

/-- ACL2 `lt`. -/
def lt (a b : SExpr) : SExpr :=
  if toInt a < toInt b then .atom (.bool true) else .nil

/-- ACL2 `eq`. -/
def eq (a b : SExpr) : SExpr :=
  if a == b then .atom (.bool true) else .nil

/-- ACL2 `equal`. -/
def equal (a b : SExpr) : SExpr :=
  if a == b then .atom (.bool true) else .nil

/-- ACL2 `consp`. -/
def consp (s : SExpr) : SExpr :=
  match s with
  | .cons _ _ => .atom (.bool true)
  | _ => .nil

/-- ACL2 `atom`. -/
def atom (s : SExpr) : SExpr :=
  match s with
  | .cons _ _ => .nil
  | _ => .atom (.bool true)

/-- ACL2 `car`. -/
def car (s : SExpr) : SExpr :=
  match s with
  | .cons a _ => a
  | _ => .nil

/-- ACL2 `cdr`. -/
def cdr (s : SExpr) : SExpr :=
  match s with
  | .cons _ d => d
  | _ => .nil

/-- ACL2 `cons`. -/
def cons (a d : SExpr) : SExpr :=
  .cons a d

/-- ACL2 `list`. -/
def list (args : List SExpr) : SExpr :=
  SExpr.ofList args

/-- ACL2 `implies`. -/
def implies (p q : SExpr) : SExpr :=
  if toBool p then
    if toBool q then .atom (.bool true) else .nil
  else .atom (.bool true)

/-- ACL2 `and`. -/
def and (a b : SExpr) : SExpr :=
  if toBool a then b else .nil

/-- ACL2 `or`. -/
def or (a b : SExpr) : SExpr :=
  if toBool a then a else b

/-- ACL2 `not`. -/
def not (a : SExpr) : SExpr :=
  if toBool a then .nil else .atom (.bool true)

/-- ACL2 `integerp`. -/
def integerp (s : SExpr) : SExpr :=
  match s with
  | .atom (.number (.int _)) => .atom (.bool true)
  | _ => .nil

/-- ACL2 `posp`. -/
def posp (s : SExpr) : SExpr :=
  match s with
  | .atom (.number (.int n)) => if n > 0 then .atom (.bool true) else .nil
  | _ => .nil

/-- ACL2 `natp`. -/
def natp (s : SExpr) : SExpr :=
  match s with
  | .atom (.number (.int n)) => if n >= 0 then .atom (.bool true) else .nil
  | _ => .nil

/-- ACL2 `evenp`. -/
def evenp (s : SExpr) : SExpr :=
  match s with
  | .atom (.number (.int n)) => if n % 2 == 0 then .atom (.bool true) else .nil
  | _ => .nil

/-- ACL2 `oddp`. -/
def oddp (s : SExpr) : SExpr :=
  match s with
  | .atom (.number (.int n)) => if n % 2 != 0 then .atom (.bool true) else .nil
  | _ => .nil

/-- ACL2 `quote`. -/
def quote_ (s : SExpr) : SExpr := s

/-- ACL2 `expt`. -/
def expt (a b : SExpr) : SExpr :=
  let x := toInt a
  let y := toInt b
  if y < 0 then .atom (.number (.int 0)) -- Placeholder
  else .atom (.number (.int (x ^ y.toNat)))

/-- ACL2 `le` (<=). -/
def le (a b : SExpr) : SExpr :=
  if toInt a <= toInt b then .atom (.bool true) else .nil

/-- ACL2 `ge` (>=). -/
def ge (a b : SExpr) : SExpr :=
  if toInt a >= toInt b then .atom (.bool true) else .nil

/-- ACL2 `gt` (>). -/
def gt (a b : SExpr) : SExpr :=
  if toInt a > toInt b then .atom (.bool true) else .nil

def rational (n : Int) (d : Nat) : SExpr :=
  .atom (.number (.rational n d))

def decimal (m : Int) (e : Int) : SExpr :=
  .atom (.number (.decimal m e))

-- Basic Axioms / Lemmas for proofs

@[simp] theorem car_cons (a d : SExpr) : car (cons a d) = a := rfl

@[simp] theorem cdr_cons (a d : SExpr) : cdr (cons a d) = d := rfl

@[simp] theorem toBool_true : toBool (.atom (.bool true)) = true := rfl

@[simp] theorem toBool_nil : toBool .nil = false := rfl

@[simp] theorem if_true (t e : SExpr) : if_ (.atom (.bool true)) t e = t := rfl

@[simp] theorem if_nil (t e : SExpr) : if_ .nil t e = e := rfl

theorem equal_self (x : SExpr) : equal x x = .atom (.bool true) := by
  simp [equal]

@[simp] theorem toInt_plus (a b : SExpr) : toInt (plus a b) = toInt a + toInt b := by
  simp [plus, toInt]

@[simp] theorem toInt_int (n : Int) : toInt (.atom (.number (.int n))) = n := rfl

@[simp] theorem toInt_nil : toInt .nil = 0 := rfl

@[simp] theorem toInt_cons (a d : SExpr) : toInt (.cons a d) = 0 := rfl

@[simp] theorem plus_def (a b : SExpr) : plus a b = .atom (.number (.int (toInt a + toInt b))) := rfl

@[simp] theorem minus_def (a b : SExpr) : minus a b = .atom (.number (.int (toInt a - toInt b))) := rfl

@[simp] theorem times_def (a b : SExpr) : times a b = .atom (.number (.int (toInt a * toInt b))) := rfl

@[simp] theorem lt_def (a b : SExpr) : lt a b = if toInt a < toInt b then .atom (.bool true) else .nil := rfl

@[simp] theorem equal_atom_int (n m : Int) : equal (.atom (.number (.int n))) (.atom (.number (.int m))) = (if n = m then .atom (.bool true) else .nil) := by
  simp [equal]

theorem toBool_equal (a b : SExpr) : toBool (equal a b) = true ↔ a = b := by
  sorry

theorem toBool_eq (a b : SExpr) : toBool (eq a b) = true ↔ a = b := by
  sorry

theorem equal_toInt (x : SExpr) : toBool (integerp x) = true → equal x (.atom (.number (.int (toInt x)))) = .atom (.bool true) := by
  sorry

theorem integerp_toInt (x : SExpr) : toBool (integerp x) = true → x = .atom (.number (.int (toInt x))) := by
  sorry

@[simp] theorem toInt_minus (a b : SExpr) : toInt (minus a b) = toInt a - toInt b := by
  simp [minus, toInt]

@[simp] theorem toInt_times (a b : SExpr) : toInt (times a b) = toInt a * toInt b := by
  simp [times, toInt]

@[simp] theorem consp_cons (a d : SExpr) : consp (cons a d) = .atom (.bool true) := rfl

@[simp] theorem consp_nil : consp .nil = .nil := rfl

@[simp] theorem car_nil : car .nil = .nil := rfl

@[simp] theorem cdr_nil : cdr .nil = .nil := rfl

theorem toBool_consp (s : SExpr) : toBool (consp s) = true ↔ ∃ a d, s = cons a d := by
  sorry

theorem toBool_integerp (s : SExpr) : toBool (integerp s) = true ↔ ∃ n, s = .atom (.number (.int n)) := by
  sorry

end Logic
end ACL2
