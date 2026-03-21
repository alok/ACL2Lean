import ACL2Lean.Evaluator

open ACL2

private def evalStr (input : String) : Option SExpr :=
  match Parse.parseSExpr input.toList with
  | .ok (sx, rest) =>
    if (Parse.skipWS rest).isEmpty then
      match Evaluator.eval World.empty {} sx with
      | .ok v => some v
      | .error _ => none
    else none
  | .error _ => none

private def evalFails (input : String) : Bool :=
  match Parse.parseSExpr input.toList with
  | .ok (sx, rest) =>
    if (Parse.skipWS rest).isEmpty then
      match Evaluator.eval World.empty {} sx with
      | .ok _ => false
      | .error _ => true
    else true
  | .error _ => true

private def evalInWorld (src expr : String) : Option SExpr := do
  let raw ← (Parse.parseAll src).toOption
  let w := World.replay (raw.map Event.classify)
  let (sx, rest) ← (Parse.parseSExpr expr.toList).toOption
  if (Parse.skipWS rest).isEmpty then
    (Evaluator.eval w {} sx).toOption
  else none

-- === IF ===

#guard evalStr "(IF NIL 1 2)" = some (.atom (.number (.int 2)))
#guard evalStr "(IF T 1 2)" = some (.atom (.number (.int 1)))
-- Non-nil is truthy
#guard evalStr "(IF 42 1 2)" = some (.atom (.number (.int 1)))

-- === EQUAL / QUOTE ===

#guard evalStr "(EQUAL 'LT 'LT)" = some SExpr.t
#guard evalStr "(EQUAL 'A 'B)" = some SExpr.nil
#guard evalStr "(EQUAL 1 1)" = some SExpr.t
#guard evalStr "(EQUAL NIL NIL)" = some SExpr.t

-- === CONS / CAR / CDR ===

#guard evalStr "(CONS 1 2)" = some (.cons (.atom (.number (.int 1))) (.atom (.number (.int 2))))
#guard evalStr "(CAR (CONS 1 2))" = some (.atom (.number (.int 1)))
#guard evalStr "(CDR (CONS 1 2))" = some (.atom (.number (.int 2)))
#guard evalStr "(CAR NIL)" = some .nil
#guard evalStr "(CDR NIL)" = some .nil

-- === NOT / CONSP / ATOM ===

#guard evalStr "(NOT T)" = some SExpr.nil
#guard evalStr "(NOT NIL)" = some SExpr.t
#guard evalStr "(CONSP (CONS 1 2))" = some SExpr.t
#guard evalStr "(CONSP NIL)" = some SExpr.nil
#guard evalStr "(ATOM NIL)" = some SExpr.t
#guard evalStr "(ATOM (CONS 1 2))" = some SExpr.nil

-- === LIST / APPEND ===

#guard evalStr "(LIST 1 2 3)" = some (SExpr.ofList
  [.atom (.number (.int 1)), .atom (.number (.int 2)), .atom (.number (.int 3))])
#guard evalStr "(APPEND (LIST 1) (LIST 2))" = some (SExpr.ofList
  [.atom (.number (.int 1)), .atom (.number (.int 2))])

-- === Arithmetic ===

#guard evalStr "(+ 3 4)" = some (.atom (.number (.int 7)))
#guard evalStr "(- 10 3)" = some (.atom (.number (.int 7)))
#guard evalStr "(* 6 7)" = some (.atom (.number (.int 42)))
#guard evalStr "(< 1 2)" = some SExpr.t
#guard evalStr "(< 2 1)" = some SExpr.nil

-- === Predicates ===

#guard evalStr "(INTEGERP 42)" = some SExpr.t
#guard evalStr "(INTEGERP NIL)" = some SExpr.nil
#guard evalStr "(NATP 0)" = some SExpr.t
#guard evalStr "(NATP -1)" = some SExpr.nil
#guard evalStr "(SYMBOLP 'X)" = some SExpr.t
#guard evalStr "(SYMBOLP 42)" = some SExpr.nil
#guard evalStr "(STRINGP \"hello\")" = some SExpr.t
#guard evalStr "(ZP 0)" = some SExpr.t
#guard evalStr "(ZP 5)" = some SExpr.nil

-- === LET ===

#guard evalStr "(LET ((X 5)) (+ X 10))" = some (.atom (.number (.int 15)))
#guard evalStr "(LET ((X 1) (Y 2)) (+ X Y))" = some (.atom (.number (.int 3)))

-- === QUOTE ===

#guard evalStr "'(1 2 3)" = some (SExpr.ofList
  [.atom (.number (.int 1)), .atom (.number (.int 2)), .atom (.number (.int 3))])
#guard evalStr "'NIL" = some SExpr.nil

-- === User-defined functions ===

#guard evalInWorld "(DEFUN FOO (X) (+ X 1))" "(FOO 4)" = some (.atom (.number (.int 5)))
#guard evalInWorld "(DEFUN DBL (X) (* X 2))" "(DBL 21)" = some (.atom (.number (.int 42)))

-- Multiple definitions
#guard evalInWorld
  "(DEFUN INC (X) (+ X 1)) (DEFUN DEC (X) (- X 1))"
  "(+ (INC 5) (DEC 5))" = some (.atom (.number (.int 10)))

-- === Error cases ===

#guard evalFails "(UNKNOWN-FN 1)"
#guard evalFails "(+ 1 2 3)"

-- Wrong arity on builtins
#guard evalFails "(CAR)"
#guard evalFails "(CAR 1 2)"
#guard evalFails "(CONS 1)"

-- Unbound variable
#guard evalFails "X"

-- === Nested expressions ===

#guard evalStr "(IF (CONSP (CONS 1 2)) (CAR (CONS 10 20)) 0)" = some (.atom (.number (.int 10)))
#guard evalStr "(EQUAL (+ 2 3) 5)" = some SExpr.t

-- === TRUE-LISTP / SYMBOLP in eval ===

#guard evalStr "(TRUE-LISTP (LIST 1 2))" = some SExpr.t
#guard evalStr "(TRUE-LISTP (CONS 1 2))" = some SExpr.nil
#guard evalStr "(SYMBOLP NIL)" = some SExpr.t

-- === Division producing rational ===

#guard evalStr "(/ 5 2)" = some (.atom (.number (.rational 5 2)))

-- === EVENP / ODDP ===

#guard evalStr "(EVENP 4)" = some SExpr.t
#guard evalStr "(EVENP 3)" = some SExpr.nil
#guard evalStr "(ODDP 3)" = some SExpr.t
