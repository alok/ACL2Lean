import Lean

open Lean

namespace ACL2

declare_syntax_cat acl2_id
syntax ident : acl2_id
syntax num : acl2_id
syntax "-" : acl2_id
syntax "+" : acl2_id
syntax "*" : acl2_id
syntax "/" : acl2_id
syntax "<" : acl2_id
syntax ">" : acl2_id
syntax "=" : acl2_id
syntax "!" : acl2_id
syntax "?" : acl2_id
syntax "if" : acl2_id
syntax "quote" : acl2_id
syntax "let" : acl2_id
syntax "declare" : acl2_id
-- Support for IDs with hyphens
syntax ident "-" acl2_id : acl2_id

declare_syntax_cat acl2_sexpr
syntax acl2_id : acl2_sexpr
syntax num : acl2_sexpr
syntax str : acl2_sexpr
syntax "(" acl2_sexpr* ")" : acl2_sexpr
syntax ":" acl2_id : acl2_sexpr

declare_syntax_cat acl2_event
syntax "(" "defun" acl2_id "(" acl2_id* ")" acl2_sexpr* ")" ("termination_by" term)? ("decreasing_by" tacticSeq)? : acl2_event
syntax "(" "defthm" acl2_id acl2_sexpr ")" (":" term)? : acl2_event
syntax "(" "defmacro" acl2_id "(" acl2_id* ")" acl2_sexpr ")" : acl2_event
syntax "(" "defconst" acl2_id acl2_sexpr ")" : acl2_event
syntax "(" "defrec" acl2_id "(" acl2_id* ")" acl2_sexpr ")" : acl2_event
syntax "(" "defstobj" acl2_id acl2_sexpr* ")" : acl2_event
syntax "(" "in-package" str ")" : acl2_event
syntax "(" "include-book" str ")" : acl2_event

end ACL2
