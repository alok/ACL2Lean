import Lean
import ACL2Lean.Syntax
import ACL2Lean.Logic

open Lean PrettyPrinter

namespace ACL2

@[app_unexpander SExpr.nil]
def unexpandSExprNil : Lean.PrettyPrinter.Unexpander := fun _ =>
  `(nil)

@[app_unexpander SExpr.atom]
def unexpandSExprAtom : Lean.PrettyPrinter.Unexpander := fun stx =>
  match stx with
  | `($_ $a) => pure a
  | _ => throw ()

@[app_unexpander Atom.bool]
def unexpandAtomBool : Lean.PrettyPrinter.Unexpander := fun stx =>
  match stx with
  | `($_ true) => `(t)
  | `($_ false) => `(nil)
  | _ => throw ()

@[app_unexpander Atom.number]
def unexpandAtomNumber : Lean.PrettyPrinter.Unexpander := fun stx =>
  match stx with
  | `($_ $n) => pure n
  | _ => throw ()

@[app_unexpander Number.int]
def unexpandNumberInt : Lean.PrettyPrinter.Unexpander := fun stx =>
  match stx with
  | `($_ $n) => pure n
  | _ => throw ()

@[app_unexpander Atom.symbol]
def unexpandAtomSymbol : Lean.PrettyPrinter.Unexpander := fun stx =>
  match stx with
  | `($_ { package := $_, name := $name }) =>
    match name.raw.isStrLit? with
    | some s => pure (Lean.mkIdent (Name.mkSimple s))
    | none => throw ()
  | _ => throw ()

@[app_unexpander Atom.string]
def unexpandAtomString : Lean.PrettyPrinter.Unexpander := fun stx =>
  match stx with
  | `($_ $s) => pure s
  | _ => throw ()

@[app_unexpander SExpr.cons]
def unexpandSExprCons : Lean.PrettyPrinter.Unexpander := fun stx =>
  match stx with
  | `($_ $car $cdr) =>
    match cdr with
    | `(nil) => `(($car))
    | _ => `(($car . $cdr))
  | _ => throw ()

@[app_unexpander Logic.plus]
def unexpandPlus : Lean.PrettyPrinter.Unexpander := fun stx =>
  match stx with
  | `($_ $a $b) => `(plus $a $b)
  | _ => throw ()

@[app_unexpander Logic.equal]
def unexpandEqual : Lean.PrettyPrinter.Unexpander := fun stx =>
  match stx with
  | `($_ $a $b) => `(equal $a $b)
  | _ => throw ()

@[app_unexpander Logic.toBool]
def unexpandToBool : Lean.PrettyPrinter.Unexpander := fun stx =>
  match stx with
  | `($_ $a) => pure a
  | _ => throw ()

end ACL2
