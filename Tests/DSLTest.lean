import ACL2Lean

open ACL2 ACL2.Logic ACL2.Tactics

#acl {
  (defun my-plus (x y) (+ x y))

  (defun factorial (n)
    (if (zp n)
        1
      (* n (factorial (- n 1)))))

  -- Test placeholders in a theorem
  (defthm factorial-5 (equal (factorial 5) _) : by
    acl2_simp
    native_decide)

  (defun test-list ()
    (quote (1 2 3)))

  (defthm plus-comm (equal (+ x y) (+ y x)) : by
    acl2_simp
    sorry)

  (defconst myconst 42)
}

#check my_plus
#check factorial
#check factorial_5
#check test_list
#check plus_comm
#check myconst

#eval! factorial (SExpr.atom (.number (.int 5)))
#eval! test_list
#eval! myconst
