import LeanPrism
import ACL2Lean.Logic
import ACL2Lean.Tactics
import ACL2Lean.ProofMode
import ProofWidgets.Component.HtmlDisplay

open ACL2
open ACL2.Logic
open ACL2.Tactics

namespace ACL2
namespace ProofModeDemo

def demoLen : SExpr → Nat
  | .cons _ d => demoLen d + 1
  | _ => 0

def demoLenS (x : SExpr) : SExpr :=
  .atom (.number (.int (Int.ofNat (demoLen x))))

def demoAppend : SExpr → SExpr → SExpr
  | .cons a d, y => cons a (demoAppend d y)
  | _, y => y

theorem demoLenAppend (x y : SExpr) :
    demoLen (demoAppend x y) = demoLen x + demoLen y := by
  induction x with
  | nil =>
      simp [demoLen, demoAppend]
  | atom a =>
      simp [demoLen, demoAppend]
  | cons a d ihA ihD =>
      simp [demoLen, demoAppend, ihD]
      omega

theorem demoLenAppendAcl (x y : SExpr) :
    toBool (equal (demoLenS (demoAppend x y)) (plus (demoLenS x) (demoLenS y))) = true := by
  simp [demoLenS, Logic.toBool, Logic.equal, Logic.plus, Logic.toInt, demoLenAppend, Int.natCast_add]

#acl_panel demoLenAppendAcl

end ProofModeDemo
end ACL2
