import ACL2Lean.Syntax

namespace ACL2
namespace Logic

open ACL2

/-- ACL2 truthiness: everything except `nil` and `false` is true. -/
@[inline, simp] def toBool (s : SExpr) : Bool :=
  match s with
  | .nil => false
  | .atom (.bool false) => false
  | _ => true

/-- ACL2 `if` lazy evaluation. -/
@[inline, simp] def if_ (c t e : SExpr) : SExpr :=
  if toBool c then t else e

/-- Coerce an S-expression to an integer if possible, else 0. -/
@[inline, simp] def toInt (s : SExpr) : Int :=
  match s with
  | .atom (.number (.int n)) => n
  | _ => 0

/-- Coerce an S-expression to a natural number for termination measures. -/
@[inline, simp] def toNat (s : SExpr) : Nat :=
  (toInt s).toNat

/-- ACL2 `zp`: true if `n` is not a positive integer. -/
@[inline, simp] def zp (n : SExpr) : SExpr :=
  if toInt n <= 0 then .atom (.bool true) else .nil

/-- ACL2 `plus`. -/
@[inline, simp] def plus (a b : SExpr) : SExpr :=
  .atom (.number (.int (toInt a + toInt b)))

/-- ACL2 `minus`. -/
@[inline, simp] def minus (a b : SExpr) : SExpr :=
  .atom (.number (.int (toInt a - toInt b)))

/-- ACL2 `times`. -/
@[inline, simp] def times (a b : SExpr) : SExpr :=
  .atom (.number (.int (toInt a * toInt b)))

/-- ACL2 `div`. -/
@[inline, simp] def div (a b : SExpr) : SExpr :=
  let x := toInt a
  let y := toInt b
  if y == 0 then .atom (.number (.int 0))
  else if x % y == 0 then .atom (.number (.int (x / y)))
  else .atom (.number (.rational x y.toNat))

/-- ACL2 `lt`. -/
@[inline, simp] def lt (a b : SExpr) : SExpr :=
  if toInt a < toInt b then .atom (.bool true) else .nil

/-- ACL2 `eq`. -/
@[inline, simp] def eq (a b : SExpr) : SExpr :=
  if a == b then .atom (.bool true) else .nil

/-- ACL2 `equal`. -/
@[inline, simp] def equal (a b : SExpr) : SExpr :=
  if a == b then .atom (.bool true) else .nil

/-- ACL2 `consp`. -/
@[inline, simp] def consp (s : SExpr) : SExpr :=
  match s with
  | .cons _ _ => .atom (.bool true)
  | _ => .nil

/-- ACL2 `atom`. -/
@[inline, simp] def atom (s : SExpr) : SExpr :=
  match s with
  | .cons _ _ => .nil
  | _ => .atom (.bool true)

/-- ACL2 `car`. -/
@[inline, simp] def car (s : SExpr) : SExpr :=
  match s with
  | .cons a _ => a
  | _ => .nil

/-- ACL2 `cdr`. -/
@[inline, simp] def cdr (s : SExpr) : SExpr :=
  match s with
  | .cons _ d => d
  | _ => .nil

/-- ACL2 `cons`. -/
@[inline, simp] def cons (a d : SExpr) : SExpr :=
  .cons a d

/-- ACL2 `list`. -/
@[inline, simp] def list (args : List SExpr) : SExpr :=
  SExpr.ofList args

/-- ACL2 `implies`. -/
@[inline, simp] def implies (p q : SExpr) : SExpr :=
  if toBool p then
    if toBool q then .atom (.bool true) else .nil
  else .atom (.bool true)

/-- ACL2 `and`. -/
@[inline, simp] def and (a b : SExpr) : SExpr :=
  if toBool a then b else .nil

/-- ACL2 `or`. -/
@[inline, simp] def or (a b : SExpr) : SExpr :=
  if toBool a then a else b

/-- ACL2 `not`. -/
@[inline, simp] def not (a : SExpr) : SExpr :=
  if toBool a then .nil else .atom (.bool true)

/-- ACL2 `integerp`. -/
@[inline, simp] def integerp (s : SExpr) : SExpr :=
  match s with
  | .atom (.number (.int _)) => .atom (.bool true)
  | _ => .nil

/-- ACL2 `posp`. -/
@[inline, simp] def posp (s : SExpr) : SExpr :=
  match s with
  | .atom (.number (.int n)) => if n > 0 then .atom (.bool true) else .nil
  | _ => .nil

/-- ACL2 `natp`. -/
@[inline, simp] def natp (s : SExpr) : SExpr :=
  match s with
  | .atom (.number (.int n)) => if n >= 0 then .atom (.bool true) else .nil
  | _ => .nil

/-- ACL2 `evenp`. -/
@[inline, simp] def evenp (s : SExpr) : SExpr :=
  match s with
  | .atom (.number (.int n)) => if n % 2 == 0 then .atom (.bool true) else .nil
  | _ => .nil

/-- ACL2 `oddp`. -/
@[inline, simp] def oddp (s : SExpr) : SExpr :=
  match s with
  | .atom (.number (.int n)) => if n % 2 != 0 then .atom (.bool true) else .nil
  | _ => .nil

/-- ACL2 `quote`. -/
@[inline, simp] def quote_ (s : SExpr) : SExpr := s

/-- ACL2 `expt`. -/
@[inline, simp] def expt (a b : SExpr) : SExpr :=
  let x := toInt a
  let y := toInt b
  if y < 0 then .atom (.number (.int 0)) -- Placeholder
  else .atom (.number (.int (x ^ y.toNat)))

/-- ACL2 `le` (<=). -/
@[inline, simp] def le (a b : SExpr) : SExpr :=
  if toInt a <= toInt b then .atom (.bool true) else .nil

/-- ACL2 `ge` (>=). -/
@[inline, simp] def ge (a b : SExpr) : SExpr :=
  if toInt a >= toInt b then .atom (.bool true) else .nil

/-- ACL2 `gt` (>). -/
@[inline, simp] def gt (a b : SExpr) : SExpr :=
  if toInt a > toInt b then .atom (.bool true) else .nil

@[inline, simp] def rational (n : Int) (d : Nat) : SExpr :=
  .atom (.number (.rational n d))

@[inline, simp] def decimal (m : Int) (e : Int) : SExpr :=
  .atom (.number (.decimal m e))

/-- ACL2 `first`. -/
@[inline, simp] def first (s : SExpr) : SExpr := car s

/-- ACL2 `second`. -/
@[inline, simp] def second (s : SExpr) : SExpr := car (cdr s)

/-- ACL2 `endp`. -/
@[inline, simp] def endp (s : SExpr) : SExpr :=
  match s with
  | .cons _ _ => .nil
  | _ => .atom (.bool true)

/-- ACL2 `stringp`. -/
@[inline, simp] def stringp (s : SExpr) : SExpr :=
  match s with
  | .atom (.string _) => .atom (.bool true)
  | _ => .nil

/-- ACL2 `string-append`. -/
@[inline, simp] def string_append (a b : SExpr) : SExpr :=
  match a, b with
  | .atom (.string s1), .atom (.string s2) => .atom (.string (s1 ++ s2))
  | _, _ => .nil

/-- ACL2 `logand`. -/
@[inline, simp] def logand (a b : SExpr) : SExpr :=
  .atom (.number (.int (Nat.land (toInt a).toNat (toInt b).toNat)))

/-- ACL2 `logor`. -/
@[inline, simp] def logor (a b : SExpr) : SExpr :=
  .atom (.number (.int (Nat.lor (toInt a).toNat (toInt b).toNat)))

/-- ACL2 `logxor`. -/
@[inline, simp] def logxor (a b : SExpr) : SExpr :=
  .atom (.number (.int (Nat.xor (toInt a).toNat (toInt b).toNat)))

/-- ACL2 `lognot`. -/
@[inline, simp] def lognot (a : SExpr) : SExpr :=
  .atom (.number (.int (-(toInt a) - 1)))

/-- ACL2 `ash` (arithmetic shift). -/
@[inline, simp] def ash (n i : SExpr) : SExpr :=
  let val := toInt n
  let count := toInt i
  if count >= 0 then
    .atom (.number (.int (val <<< count.toNat)))
  else
    .atom (.number (.int (val >>> (-count).toNat)))

instance : OfNat SExpr n where
  ofNat := .atom (.number (.int n))

-- Basic Axioms / Lemmas for proofs

@[simp] theorem toNat_minus_one (n : SExpr) (h : toBool (zp n) = false) :
  toNat (minus n (SExpr.atom (Atom.number (Number.int 1)))) < toNat n := by
  sorry

@[simp, grind] theorem car_cons (a d : SExpr) : car (cons a d) = a := rfl

@[simp, grind] theorem cdr_cons (a d : SExpr) : cdr (cons a d) = d := rfl

@[simp, grind] theorem toBool_true : toBool (.atom (.bool true)) = true := rfl

@[simp, grind] theorem toBool_nil : toBool .nil = false := rfl

@[simp, grind] theorem if_true (t e : SExpr) : if_ (.atom (.bool true)) t e = t := rfl

@[simp, grind] theorem if_nil (t e : SExpr) : if_ .nil t e = e := rfl

@[grind] theorem equal_self (x : SExpr) : equal x x = .atom (.bool true) := by
  simp [equal]

@[simp, grind] theorem toInt_plus (a b : SExpr) : toInt (plus a b) = toInt a + toInt b := by
  simp [plus, toInt]

@[simp, grind] theorem toInt_int (n : Int) : toInt (.atom (.number (.int n))) = n := rfl

@[simp, grind] theorem toInt_nil : toInt .nil = 0 := rfl

@[simp, grind] theorem toInt_cons (a d : SExpr) : toInt (.cons a d) = 0 := rfl

@[simp, grind] theorem plus_def (a b : SExpr) : plus a b = .atom (.number (.int (toInt a + toInt b))) := rfl

@[simp, grind] theorem minus_def (a b : SExpr) : minus a b = .atom (.number (.int (toInt a - toInt b))) := rfl

@[simp, grind] theorem times_def (a b : SExpr) : times a b = .atom (.number (.int (toInt a * toInt b))) := rfl

@[simp, grind] theorem lt_def (a b : SExpr) : lt a b = if toInt a < toInt b then .atom (.bool true) else .nil := rfl

@[simp, grind] theorem equal_atom_int (n m : Int) : equal (.atom (.number (.int n))) (.atom (.number (.int m))) = (if n = m then .atom (.bool true) else .nil) := by
  simp [equal]

@[grind] theorem toBool_equal (a b : SExpr) : toBool (equal a b) = true ↔ a = b := by
  sorry

@[grind] theorem toBool_eq (a b : SExpr) : toBool (eq a b) = true ↔ a = b := by
  sorry

@[grind] theorem equal_toInt (x : SExpr) : toBool (integerp x) = true → equal x (.atom (.number (.int (toInt x)))) = .atom (.bool true) := by
  sorry

@[grind] theorem integerp_toInt (x : SExpr) : toBool (integerp x) = true → x = .atom (.number (.int (toInt x))) := by
  sorry

@[simp] theorem toInt_minus (a b : SExpr) : toInt (minus a b) = toInt a - toInt b := by
  simp [minus, toInt]

@[simp] theorem toInt_times (a b : SExpr) : toInt (times a b) = toInt a * toInt b := by
  simp [times, toInt]

@[simp, grind] theorem consp_cons (a d : SExpr) : consp (cons a d) = .atom (.bool true) := rfl

@[simp, grind] theorem consp_nil : consp .nil = .nil := rfl

@[simp, grind] theorem car_nil : car .nil = .nil := rfl

@[simp, grind] theorem cdr_nil : cdr .nil = .nil := rfl

@[simp, grind] theorem toBool_consp (s : SExpr) : toBool (consp s) = true ↔ ∃ a d, s = cons a d := by
  sorry

@[simp, grind] theorem toBool_integerp (s : SExpr) : toBool (integerp s) = true ↔ ∃ n, s = .atom (.number (.int n)) := by
  sorry

/-- ACL2 `append` — concatenate two lists. Non-cons first arg returns second. -/
def append (x y : SExpr) : SExpr :=
  match x with
  | .cons a b => .cons a (append b y)
  | _ => y

/-- ACL2 `len` — length of a list as an ACL2 integer. -/
def len (x : SExpr) : SExpr :=
  match x with
  | .cons _ b => .atom (.number (.int (toInt (len b) + 1)))
  | _ => .atom (.number (.int 0))

/-- ACL2 `true-listp` — returns t if nil-terminated cons chain, nil otherwise. -/
def trueListp (x : SExpr) : SExpr :=
  match x with
  | .cons _ b => trueListp b
  | .nil => .atom (.bool true)
  | _ => .nil

@[simp] theorem append_nil (y : SExpr) : append .nil y = y := rfl

@[simp] theorem append_cons (a b y : SExpr) :
    append (.cons a b) y = .cons a (append b y) := rfl

@[simp] theorem append_atom (at_ : Atom) (y : SExpr) :
    append (.atom at_) y = y := rfl

@[simp] theorem len_nil : len .nil = .atom (.number (.int 0)) := rfl

@[simp] theorem len_cons (a b : SExpr) :
    len (.cons a b) = .atom (.number (.int (toInt (len b) + 1))) := rfl

@[simp] theorem trueListp_nil : trueListp .nil = .atom (.bool true) := rfl

@[simp] theorem trueListp_cons (a b : SExpr) :
    trueListp (.cons a b) = trueListp b := rfl

end Logic
end ACL2
