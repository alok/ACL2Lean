import ACL2Lean.DSL
import ACL2Lean.Logic

open ACL2.Logic

#acl {
  (defun my-plus (x y) (+ x y))

  -- Factorial with termination measure
  (defun factorial (n)
    (if (zp n)
        1
      (* n (factorial (- n 1)))))
    termination_by toNat n
    decreasing_by sorry

  -- defstobj test
  (defstobj my-st
    fld1
    (fld2 :init 42))

  -- Simplified test without let
  (defun test-stobj (my-st)
    (declare (xargs :stobjs my-st))
    (update-fld1 100 my-st))

  -- String and Bitvector tests
  (defun test-logic (s x y)
    (if (stringp s)
        (string-append s "!")
      (logand x (logor y 1))))
}

#check my_st
#check fld1
#check update_fld1
#check test_stobj
#check factorial
#check test_logic

-- Initial state
def start_st : my_st := { fld1 := .nil, fld2 := 42 }

-- Pure functional test
#eval test_stobj start_st
#eval factorial 5
#eval test_logic (.atom (.string "hello")) 0 0
#eval test_logic 0 15 7

-- Monadic test
def stobj_action : my_stM ACL2.SExpr := do
  update_fld1M 1000
  fld1M

#eval stobj_action.run start_st
