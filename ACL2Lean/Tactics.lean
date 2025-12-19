import ACL2Lean.Logic

namespace ACL2
namespace Tactics

open Logic

macro "acl2_simp" : tactic => 
  `(tactic| simp [Logic.toBool, Logic.if_, Logic.plus, Logic.minus, Logic.times, Logic.div, 
                 Logic.lt, Logic.eq, Logic.equal, Logic.consp, Logic.atom, Logic.car, 
                 Logic.cdr, Logic.cons, Logic.list, Logic.zp, Logic.evenp, Logic.oddp, 
                 Logic.integerp, Logic.posp, Logic.natp, Logic.implies, Logic.and, 
                 Logic.or, Logic.not, Logic.expt, Logic.le, Logic.ge, Logic.gt,
                 Logic.first, Logic.second, Logic.endp])

macro "acl2_grind" : tactic =>
  `(tactic| acl2_simp)

end Tactics
end ACL2
