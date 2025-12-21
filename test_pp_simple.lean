import ACL2Lean

open ACL2 ACL2.Logic

-- If unexpanders work, this should show (+ 1 2) or similar
#check Logic.plus (SExpr.atom (.number (.int 1))) (SExpr.atom (.number (.int 2)))







