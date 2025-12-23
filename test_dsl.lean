import ACL2Lean.DSL

set_option profiler true

open ACL2 ACL2.Logic ACL2.Tactics

#acl {
  (defun my-plus (x y) (+ x y))

  -- defstobj test
  (defstobj my-st
    fld1
    (fld2 :init 42))

  -- Simplified test without let
  (defun test-stobj (my-st)
    (declare (xargs :stobjs my-st))
    (update-fld1 100 my-st))
}

#check my_st
#check fld1
#check update_fld1

-- Initial state
def start_st : my_st := { fld1 := .nil, fld2 := .atom (.number (.int 42)) }

-- Pure functional test
#eval test_stobj start_st
