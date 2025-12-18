import Lean
import ACL2Lean.Logic
import ACL2Lean.Tactics

open Lean Elab Command Term Meta

namespace ACL2

declare_syntax_cat acl2_sexpr
declare_syntax_cat acl2_event

-- Flexible Identifier Syntax
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

-- S-Expression Syntax
syntax acl2_id : acl2_sexpr
syntax num : acl2_sexpr
syntax str : acl2_sexpr
syntax "(" acl2_sexpr* ")" : acl2_sexpr
syntax ":" acl2_id : acl2_sexpr
syntax "if" : acl2_sexpr

-- Event Syntax
syntax "(" "defun" acl2_id+ "(" acl2_id* ")" acl2_sexpr ")" : acl2_event
syntax "(" "defthm" acl2_id+ acl2_sexpr ")" : acl2_event
syntax "(" "in-package" str ")" : acl2_event

-- Top-level DSL command
syntax "#acl" "{" acl2_event* "}" : command

/-- Sanitize ACL2 symbol names for Lean. -/
def sanitize (s : String) : Name :=
  let s' := s.trimAscii.toString
  let s' := s'.replace "-" "_"
  let s' := s'.replace "!" "_bang"
  let s' := s'.replace "?" "_p"
  let s' := s'.replace "+" "plus"
  let s' := s'.replace "*" "times"
  let s' := s'.replace "/" "div"
  let s' := s'.replace "<" "lt"
  let s' := s'.replace ">" "gt"
  let s' := s'.replace "=" "eq"
  let s' := if s' == "if" then "if_" else s'
  Name.mkSimple s'

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

def getIdStr (stx : Syntax) : String :=
  match stx.reprint with
  | some s => s.trimAscii.toString
  | none => ""

def getIdsStr (stxs : Array Syntax) : String :=
  let parts := stxs.map getIdStr
  "".intercalate parts.toList

/-- Translate ACL2 S-expression to a raw SExpr value in Lean. -/
partial def translateSExprValue (stx : Syntax) : MacroM (TSyntax `term) := do
  match stx with
  | `(acl2_sexpr| $i:acl2_id) =>
      let name := getIdStr i.raw
      if name == "t" then `(_root_.ACL2.SExpr.atom (_root_.ACL2.Atom.bool true))
      else if name == "nil" then `(_root_.ACL2.SExpr.nil)
      else
        let nameLit := Lean.quote name
        `(_root_.ACL2.SExpr.atom (_root_.ACL2.Atom.symbol { package := none, name := $nameLit }))
  | `(acl2_sexpr| $n:num) => `(_root_.ACL2.SExpr.atom (_root_.ACL2.Atom.number (_root_.ACL2.Number.int (Int.ofNat $n))))
  | `(acl2_sexpr| $s:str) => `(_root_.ACL2.SExpr.atom (_root_.ACL2.Atom.string $s))
  | `(acl2_sexpr| ($ss:acl2_sexpr*)) => do
      let mut res ← `(_root_.ACL2.SExpr.nil)
      for s in ss.reverse do
        let s' ← translateSExprValue s
        res ← `(_root_.ACL2.SExpr.cons $s' $res)
      pure res
  | _ => Macro.throwError s!"Unsupported ACL2 value syntax: {stx}"

/-- Detect built-in names to avoid collecting them as variables. -/
def isBuiltin (s : String) : Bool :=
  ["+", "-", "*", "/", "<", ">", "=", "<=", ">=", "if", "zp", "evenp", "equal", "consp", "atom", "car", "cdr", "cons", "not", "and", "or", "implies", "t", "nil", "quote"].contains s

/-- Collect free variables in an ACL2 S-expression. -/
partial def collectFreeVars (stx : Syntax) : MacroM (List Ident) := do
  match stx with
  | `(acl2_sexpr| $i:acl2_id) =>
      let name := getIdStr i.raw
      if isBuiltin name then pure []
      else pure [mkIdent (sanitize name)]
  | `(acl2_sexpr| ($ss:acl2_sexpr*)) => do
      if ss.isEmpty then pure []
      else
        let fnName := getIdStr ss[0]!.raw
        let mut vars := []
        let startIdx := if fnName == "quote" then ss.size else 1
        for a in ss[startIdx:] do
          let avars ← collectFreeVars a
          vars := vars ++ avars
        pure vars
  | _ => pure []

/-- Translate ACL2 S-expression syntax to Lean Syntax (as code). -/
partial def translateSExpr (stx : Syntax) : MacroM (TSyntax `term) := do
  match stx with
  | `(acl2_sexpr| $i:acl2_id) =>
      let name := getIdStr i.raw
      if name == "t" then `(_root_.ACL2.SExpr.atom (_root_.ACL2.Atom.bool true))
      else if name == "nil" then `(_root_.ACL2.SExpr.nil)
      else pure (mkIdent (sanitize name))
  | `(acl2_sexpr| if) => pure (mkIdent (sanitize "if"))
  | `(acl2_sexpr| $n:num) => `(_root_.ACL2.SExpr.atom (_root_.ACL2.Atom.number (_root_.ACL2.Number.int (Int.ofNat $n))))
  | `(acl2_sexpr| $s:str) => `(_root_.ACL2.SExpr.atom (_root_.ACL2.Atom.string $s))
  | `(acl2_sexpr| ($ss:acl2_sexpr*)) => do
      if ss.isEmpty then `(_root_.ACL2.SExpr.nil)
      else
        let fnName := getIdStr ss[0]!.raw
        if fnName == "if" then
          if ss.size == 4 then
            let c ← translateSExpr ss[1]!
            let t ← translateSExpr ss[2]!
            let e ← translateSExpr ss[3]!
            `(if _root_.ACL2.Logic.toBool $c then $t else $e)
          else
            Macro.throwError "if requires 3 arguments"
        else if fnName == "quote" then
          if ss.size == 2 then
            translateSExprValue ss[1]!
          else
            Macro.throwError "quote requires 1 argument"
        else
          let fnIdent := mapBuiltinStx fnName
          let mut args := #[]
          for a in ss[1:] do
            let a' ← translateSExpr a
            args := args.push a'
          `($fnIdent $args*)
  | _ => Macro.throwError s!"Unsupported ACL2 expression syntax: {stx}"

elab_rules : command
  | `(#acl { $events:acl2_event* }) => do
      let mut defNames := #[]
      let mut thmNames := #[]
      for ev in events do
        match ev with
        | `(acl2_event| (defun $[$id:acl2_id]* ($[$args:acl2_id]* ) $body:acl2_sexpr)) =>
            let body' ← liftMacroM <| translateSExpr body
            let mut binders := #[]
            for arg in args do
              let argName := getIdStr arg
              let argId := mkIdent (sanitize argName)
              binders := binders.push argId
            let nameStr := getIdsStr (id.map (·.raw))
            let nameId := mkIdent (sanitize nameStr)
            let cmd ← `(partial def $nameId $[($binders : _root_.ACL2.SExpr)]* : _root_.ACL2.SExpr := $body')
            elabCommand cmd
            defNames := defNames.push nameStr
        | `(acl2_event| (defthm $[$id:acl2_id]* $prop:acl2_sexpr)) =>
            let prop' ← liftMacroM <| translateSExpr prop
            let vars ← liftMacroM <| collectFreeVars prop
            let mut binders := #[]
            let mut seen := #[]
            for v in vars do
              if !seen.contains v.getId then
                binders := binders.push v
                seen := seen.push v.getId
            let nameStr := getIdsStr (id.map (·.raw))
            let nameId := mkIdent (sanitize nameStr)
            let cmd ← `(theorem $nameId $[($binders : _root_.ACL2.SExpr)]* : _root_.ACL2.Logic.toBool $prop' = true := by
              first | acl2_grind | sorry)
            elabCommand cmd
            thmNames := thmNames.push nameStr
        | _ => pure ()

      logInfo s!"#acl World updated:\n  Functions: {defNames.toList}\n  Theorems: {thmNames.toList}"

end ACL2
