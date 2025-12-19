import ACL2Lean.DSL
set_option profiler true
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
  (defconst myconst 42)
}
#eval! factorial (SExpr.atom (.number (.int 5)))
#eval! test_list
#eval! myconst
