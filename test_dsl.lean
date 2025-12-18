import ACL2Lean.DSL

open ACL2 ACL2.Logic ACL2.Tactics

#acl {
  (defun my-plus (x y) (+ x y))

  (defun factorial (n)
    (if (zp n)
        1
      (* n (factorial (- n 1)))))

  (defthm factorial-5 (equal (factorial 5) 120))

  (defun test-list ()
    (quote (1 2 3)))

  (defthm plus-comm (equal (+ x y) (+ y x)))
}

#check my_plus
#check factorial
#check factorial_5
#check test_list
#check plus_comm

#eval factorial (SExpr.atom (.number (.int 5)))
#eval test_list

-- factorial_5 is already a theorem proven by sorry or grind in the #acl block
#check factorial_5

-- plus_comm is also already a theorem
#check plus_comm

-- We can prove it manually if we want to override or check
theorem plus_comm_manual (x y : SExpr) : Logic.toBool (Logic.equal (Logic.plus x y) (Logic.plus y x)) = true := by
  acl2_grind

