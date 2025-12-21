import Lean
import ACL2Lean.DSL.SyntaxCategories
import ACL2Lean.Logic
import ACL2Lean.Tactics

open Lean Elab Command Term Meta

namespace ACL2

/-- Sanitize ACL2 symbol names for Lean. -/
def sanitize (s : String) : Name :=
  let s' := s.trimAscii.toString
  let s' := s'.replace "-" "_"
  let s' := s'.replace "!" "_bang"
  let s' := s'.replace "?" "_p"
  let s' := s'.replace "+" "plus"
  let s' := if s' == "*" then "times" else s'.replace "*" "star"
  let s' := s'.replace "/" "div"
  let s' := s'.replace "<" "lt"
  let s' := s'.replace ">" "gt"
  let s' := s'.replace "=" "eq"
  let s' := if s' == "if" then "if_" else s'
  let s' := if s'.startsWith "_" then "v" ++ s' else s'
  Name.mkSimple s'

def getIdStr (stx : Syntax) : String :=
  match stx.reprint with
  | some s => s.trimAscii.toString
  | none => ""

/-- Map ACL2 built-ins to Lean Logic functions as Syntax. -/
def mapBuiltinStx (s : String) : Ident :=
  let name := match s.trimAscii.toString with
    | "+" => `_root_.ACL2.Logic.plus
    | "-" => `_root_.ACL2.Logic.minus
    | "*" => `_root_.ACL2.Logic.times
    | "/" => `_root_.ACL2.Logic.div
    | "<" => `_root_.ACL2.Logic.lt
    | "=" => `_root_.ACL2.Logic.eq
    | ">" => `_root_.ACL2.Logic.gt
    | "<=" => `_root_.ACL2.Logic.le
    | ">=" => `_root_.ACL2.Logic.ge
    | "zp" => `_root_.ACL2.Logic.zp
    | "evenp" => `_root_.ACL2.Logic.evenp
    | "equal" => `_root_.ACL2.Logic.equal
    | "consp" => `_root_.ACL2.Logic.consp
    | "atom" => `_root_.ACL2.Logic.atom
    | "car" => `_root_.ACL2.Logic.car
    | "cdr" => `_root_.ACL2.Logic.cdr
    | "cons" => `_root_.ACL2.Logic.cons
    | "not" => `_root_.ACL2.Logic.not
    | "and" => `_root_.ACL2.Logic.and
    | "or" => `_root_.ACL2.Logic.or
    | "implies" => `_root_.ACL2.Logic.implies
    | "if" => `if_
    | s' => sanitize s'
  mkIdent name

/-- Detect built-ins to avoid collecting them as variables. -/
def isBuiltin (s : String) : Bool :=
  ["+", "-", "*", "/", "<", ">", "=", "<=", ">=", "if", "zp", "evenp", "equal", "consp", "atom", "car", "cdr", "cons", "not", "and", "or", "implies", "t", "nil", "quote"].contains s

/-- Translate ACL2 S-expression to a raw SExpr value in Lean. -/
partial def translateSExprValue (stx : Syntax) : MacroM (TSyntax `term) := do
  match stx with
  | `(acl2_sexpr| $i:acl2_id) =>
      let name := getIdStr i.raw
      if name == "t" then return (← `(_root_.ACL2.SExpr.atom (_root_.ACL2.Atom.bool true)))
      else if name == "nil" then return (← `(_root_.ACL2.SExpr.nil))
      else if let some n := i.raw.isNatLit? then
        return (← `(_root_.ACL2.SExpr.atom (_root_.ACL2.Atom.number (_root_.ACL2.Number.int (Int.ofNat $(Lean.quote n))))))
      else
        let nameLit := Lean.quote name
        return (← `(_root_.ACL2.SExpr.atom (_root_.ACL2.Atom.symbol { package := "ACL2", name := $nameLit })))
  | `(acl2_sexpr| $n:num) =>
      return (← `(_root_.ACL2.SExpr.atom (_root_.ACL2.Atom.number (_root_.ACL2.Number.int (Int.ofNat $n)))))
  | `(acl2_sexpr| $s:str) =>
      return (← `(_root_.ACL2.SExpr.atom (_root_.ACL2.Atom.string $s)))
  | `(acl2_sexpr| ($ss*)) =>
      let mut res ← `(_root_.ACL2.SExpr.nil)
      for s in ss.reverse do
        let s' ← translateSExprValue s
        res ← `(_root_.ACL2.SExpr.cons $s' $res)
      return res
  | _ => return (← `(_root_.ACL2.SExpr.nil))

/-- Collect free variables. -/
partial def collectFreeVars (stx : Syntax) : MacroM (List Ident) := do
  match stx with
  | `(acl2_sexpr| $i:acl2_id) =>
      let name := getIdStr i.raw
      if isBuiltin name || name.toNat?.isSome then return []
      else return [mkIdent (sanitize name)]
  | `(acl2_sexpr| ($ss*)) =>
      if ss.isEmpty then return []
      let first := ss[0]!
      let fnName := getIdStr first.raw
      if fnName == "quote" then return []
      let mut vars : List Ident := []
      for i in [1:ss.size] do
        let avars ← collectFreeVars ss[i]!
        vars := vars ++ avars
      return vars
  | _ => return []

/-- Translate ACL2 S-expression to Lean code. -/
partial def translateSExpr (stx : Syntax) : MacroM (TSyntax `term) := do
  match stx with
  | `(acl2_sexpr| $i:acl2_id) =>
      let name := getIdStr i.raw
      if name == "t" then return (← `(_root_.ACL2.SExpr.atom (_root_.ACL2.Atom.bool true)))
      else if name == "nil" then return (← `(_root_.ACL2.SExpr.nil))
      else return mkIdent (sanitize name)
  | `(acl2_sexpr| $n:num) =>
      return (← `(_root_.ACL2.SExpr.atom (_root_.ACL2.Atom.number (ACL2.Number.int (Int.ofNat $n)))))
  | `(acl2_sexpr| $s:str) =>
      return (← `(_root_.ACL2.SExpr.atom (ACL2.Atom.string $s)))
  | `(acl2_sexpr| ($ss*)) =>
      if ss.isEmpty then return (← `(_root_.ACL2.SExpr.nil))
      let first := ss[0]!
      let fnName := getIdStr first.raw
      if fnName == "if" then
        if ss.size == 4 then
          let c ← translateSExpr ss[1]!
          let t ← translateSExpr ss[2]!
          let e ← translateSExpr ss[3]!
          return (← `(if _root_.ACL2.Logic.toBool $c then $t else $e))
        else
          Macro.throwError "if requires 3 arguments"
      else if fnName == "quote" then
        if ss.size == 2 then
          translateSExprValue ss[1]!
        else
          Macro.throwError "quote requires 1 argument"
      else
        let fnIdent := mapBuiltinStx fnName
        let mut tArgs := #[]
        for i in [1:ss.size] do
          let a' ← translateSExpr ss[i]!
          tArgs := tArgs.push a'
        if fnName == "list" then
          return (← `(_root_.ACL2.Logic.list [$tArgs,*]))
        else
          return (← `($fnIdent $tArgs*))
  | _ => return (← `(_root_.ACL2.SExpr.nil))

/-- Individual event elaborator marked as incremental. -/
syntax (name := aclEvent) "#acl_event " acl2_event : command

@[command_elab aclEvent, incremental]
def elabAclEvent : CommandElab := fun stx => do
  match stx with
  | `(#acl_event $ev:acl2_event) =>
    match ev with
    | `(acl2_event| (defun $[$id:acl2_id]* ($[$args:acl2_id]* ) $body:acl2_sexpr)) =>
        let body' ← liftMacroM <| translateSExpr body
        let idArr := id.map (·.raw)
        let nameId := mkIdent (sanitize (getIdStr (mkNullNode idArr)))
        let mut binders := #[]
        for arg in args do
          let argName := getIdStr arg.raw
          binders := binders.push (← `(bracketedBinder| ($(mkIdent (sanitize argName)) : _root_.ACL2.SExpr)))
        let cmd ← `(partial def $nameId $[$binders]* : _root_.ACL2.SExpr := $body')
        elabCommand cmd
    | `(acl2_event| (defthm $[$id:acl2_id]* $prop:acl2_sexpr $[: $proof:term]?)) =>
        let prop' ← liftMacroM <| translateSExpr prop
        let vars ← liftMacroM <| collectFreeVars prop
        let idArr := id.map (·.raw)
        let nameId := mkIdent (sanitize (getIdStr (mkNullNode idArr)))
        let mut seen := #[]
        let mut binders := #[]
        for v in vars do
          if !seen.contains v.getId then
            seen := seen.push v.getId
            binders := binders.push (← `(bracketedBinder| ($v : _root_.ACL2.SExpr)))

        if let some p := proof then
          let cmd ← `(set_option maxHeartbeats 1000000 in theorem $nameId $[$binders]* : _root_.ACL2.Logic.toBool $prop' = true := $p)
          elabCommand cmd
        else
          let cmd ← `(set_option maxHeartbeats 1000000 in theorem $nameId $[$binders]* : _root_.ACL2.Logic.toBool $prop' = true := by
            first | acl2_grind | sorry)
          elabCommand cmd
    | `(acl2_event| (defconst $id:acl2_id $val:acl2_sexpr)) =>
        let nameId := mkIdent (sanitize (getIdStr id.raw))
        let val' ← liftMacroM <| translateSExprValue val
        let cmd ← `(def $nameId : _root_.ACL2.SExpr := $val')
        elabCommand cmd
    | _ => pure ()
  | _ => throwUnsupportedSyntax

syntax "#acl" "{" acl2_event* "}" : command

/-- The #acl block now expands to individual incremental #acl_event calls. -/
macro_rules
  | `(#acl { $events* }) => do
      let mut res := #[]
      for ev in events do
        res := res.push (← `(#acl_event $ev))
      return mkNullNode res

end ACL2
