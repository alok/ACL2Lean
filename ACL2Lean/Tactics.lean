import ACL2Lean.Logic

namespace ACL2
namespace Tactics

open Logic

macro "acl2_simp" : tactic =>
  `(tactic| simp [Logic.toBool, Logic.if_, Logic.plus, Logic.minus, Logic.times, Logic.div,
                 Logic.lt, Logic.eq, Logic.equal, Logic.consp, Logic.atom, Logic.car,
                 Logic.cdr, Logic.cons, Logic.list, Logic.zp, Logic.evenp, Logic.oddp,
                 Logic.integerp, Logic.posp, Logic.natp, Logic.implies, Logic.and,
                 Logic.or, Logic.not, Logic.expt, Logic.le, Logic.ge, Logic.gt])

macro "acl2_grind" : tactic =>
  `(tactic| grind [Logic.toBool, Logic.if_, Logic.plus, Logic.minus, Logic.times, Logic.div,
                  Logic.lt, Logic.eq, Logic.equal, Logic.consp, Logic.atom, Logic.car,
                  Logic.cdr, Logic.cons, Logic.list, Logic.zp, Logic.evenp, Logic.oddp,
                  Logic.integerp, Logic.posp, Logic.natp, Logic.implies, Logic.and,
                  Logic.or, Logic.not, Logic.expt, Logic.le, Logic.ge, Logic.gt,
                  Logic.car_cons, Logic.cdr_cons, Logic.toBool_true, Logic.toBool_nil,
                  Logic.if_true, Logic.if_nil, Logic.equal_self, Logic.toInt_plus,
                  Logic.toInt_int, Logic.toInt_nil, Logic.toInt_cons, Logic.plus_def,
                  Logic.minus_def, Logic.times_def, Logic.lt_def, Logic.equal_atom_int,
                  Logic.toBool_equal, Logic.toBool_eq, Logic.equal_toInt, Logic.integerp_toInt,
                  Logic.toInt_minus, Logic.toInt_times, Logic.toBool_lt, Logic.toBool_le,
                  Logic.toBool_ge, Logic.toBool_gt, Logic.toBool_zp, Logic.toBool_and,
                  Logic.toBool_or, Logic.toBool_not, Logic.toBool_implies,
                  Logic.consp_cons, Logic.consp_nil, Logic.toBool_consp,
                  Logic.car_nil, Logic.cdr_nil, Logic.toBool_integerp])

end Tactics
end ACL2
