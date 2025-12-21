import ACL2Lean.Logic
import Lean

namespace ACL2
namespace Tactics

open Logic Lean Elab Tactic

macro "acl2_simp" : tactic =>
  `(tactic| simp [Logic.toBool, Logic.if_, Logic.plus, Logic.minus, Logic.times, Logic.div,
                 Logic.lt, Logic.eq, Logic.equal, Logic.consp, Logic.atom, Logic.car,
                 Logic.cdr, Logic.cons, Logic.list, Logic.zp, Logic.evenp, Logic.oddp,
                 Logic.integerp, Logic.posp, Logic.natp, Logic.implies, Logic.and,
                 Logic.or, Logic.not, Logic.expt, Logic.le, Logic.ge, Logic.gt,
                 Logic.first, Logic.second, Logic.endp])

macro "acl2_grind" : tactic =>
  `(tactic| (acl2_simp; try grind))

/--
`acl2_induct f x y ...` applies the induction principle for the function `f`
with the given arguments.
Marked as incremental for performance.
-/
syntax (name := aclInduct) "acl2_induct " ident term* : tactic

@[tactic aclInduct, incremental]
def evalAclInduct : Tactic := fun stx => do
  let f := stx[1]
  let args := stx[2].getArgs
  let fName := f.getId
  let inductName := fName ++ `induct
  let inductTerm := mkIdent inductName

  -- Manually construct the induction tactic call
  let mut cmd := mkNode ``Lean.Parser.Tactic.induction #[
    mkAtom "induction",
    mkNode `null args,
    mkAtom "using",
    inductTerm
  ]
  evalTactic cmd

end Tactics
end ACL2
