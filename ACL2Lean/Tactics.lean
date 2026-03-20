import ACL2Lean.Logic
import ACL2Lean.ImportedRegistry
import ACL2Lean.Parser
import ACL2Lean.Translator
import Lean

namespace ACL2
namespace Tactics

open Logic Lean Elab Tactic Meta

private def mkQualifiedName (segments : List String) : Name :=
  segments.foldl Name.str Name.anonymous

private def identNameOfAcl2String (name : String) : Name :=
  let base :=
    match (name.splitOn "::").reverse with
    | head :: _ => head
    | [] => name
  Name.mkSimple <| Translator.sanitizeName <| Translator.translateSymbol { name := base }

private def builtinTerm? (sym : Symbol) : Option (TSyntax `term) :=
  let translated := Translator.translateSymbol sym
  if translated.startsWith "Logic." then
    some <| mkIdent <| mkQualifiedName ("ACL2" :: translated.splitOn ".")
  else
    none

private def termSyntaxOfString (input : String) : TacticM (TSyntax `term) := do
  match Parser.runParserCategory (← getEnv) `term input with
  | .ok stx => pure ⟨stx⟩
  | .error err => throwError s!"Could not parse generated Lean term `{input}`: {err}"

private partial def rawSExprSyntax : SExpr → TacticM (TSyntax `term)
  | .nil => `(_root_.ACL2.SExpr.nil)
  | .atom (.bool value) => do
      if value then
        `(_root_.ACL2.SExpr.atom (_root_.ACL2.Atom.bool true))
      else
        `(_root_.ACL2.SExpr.atom (_root_.ACL2.Atom.bool false))
  | .atom (.string value) => do
      let value := Lean.quote value
      `(_root_.ACL2.SExpr.atom (_root_.ACL2.Atom.string $value))
  | .atom (.keyword value) => do
      let value := Lean.quote value
      `(_root_.ACL2.SExpr.atom (_root_.ACL2.Atom.keyword $value))
  | .atom (.number (.int value)) => do
      let value ← termSyntaxOfString (toString value)
      `(_root_.ACL2.SExpr.atom (_root_.ACL2.Atom.number (_root_.ACL2.Number.int $value)))
  | .atom (.number (.rational numerator denominator)) => do
      let numerator ← termSyntaxOfString (toString numerator)
      let denominator := Lean.quote denominator
      `(_root_.ACL2.SExpr.atom (_root_.ACL2.Atom.number (_root_.ACL2.Number.rational $numerator $denominator)))
  | .atom (.number (.decimal mantissa exponent)) => do
      let mantissa ← termSyntaxOfString (toString mantissa)
      let exponent ← termSyntaxOfString (toString exponent)
      `(_root_.ACL2.SExpr.atom (_root_.ACL2.Atom.number (_root_.ACL2.Number.decimal $mantissa $exponent)))
  | .atom (.symbol sym) => do
      let pkg := Lean.quote sym.package
      let name := Lean.quote sym.name
      `(_root_.ACL2.SExpr.atom (_root_.ACL2.Atom.symbol { package := $pkg, name := $name }))
  | .cons car cdr => do
      let car ← rawSExprSyntax car
      let cdr ← rawSExprSyntax cdr
      `(_root_.ACL2.SExpr.cons $car $cdr)

private def isFoldedBuiltin (sym : Symbol) : Bool :=
  let translated := Translator.translateSymbol sym
  translated = "Logic.plus" || translated = "Logic.times" ||
    translated = "Logic.and" || translated = "Logic.or"

private partial def acl2TermSyntax : SExpr → TacticM (TSyntax `term)
  | .nil => `(_root_.ACL2.SExpr.nil)
  | .atom (.bool value) => rawSExprSyntax (.atom (.bool value))
  | .atom (.string value) => rawSExprSyntax (.atom (.string value))
  | .atom (.keyword value) => rawSExprSyntax (.atom (.keyword value))
  | .atom (.number value) => rawSExprSyntax (.atom (.number value))
  | .atom (.symbol sym) =>
      match builtinTerm? sym with
      | some builtin => pure builtin
      | none => pure <| mkIdent (identNameOfAcl2String sym.name)
  | .cons (.atom (.symbol sym)) argsExpr =>
      if sym.isNamed "quote" then
        match argsExpr.toList? with
        | some [quoted] => rawSExprSyntax quoted
        | _ => throwError "Malformed ACL2 quote term in instance binding"
      else do
        let fn :=
          match builtinTerm? sym with
          | some builtin => builtin
          | none => mkIdent (identNameOfAcl2String sym.name)
        let args ←
          match argsExpr.toList? with
          | some args => args.mapM acl2TermSyntax
          | none => throwError "Malformed ACL2 application term in instance binding"
        match args with
        | [] => pure fn
        | first :: rest =>
            if isFoldedBuiltin sym && !rest.isEmpty then
              let mut acc := first
              for arg in rest do
                acc ← `($fn $acc $arg)
              pure acc
            else
              let mut app := fn
              for arg in first :: rest do
                app ← `($app $arg)
              pure app
  | _ => throwError "Unsupported ACL2 instance term shape"

private def bindingOfSExpr? : SExpr → Option (String × SExpr)
  | expr => do
      let parts ← expr.toList?
      match parts with
      | [lhs, rhs] =>
          let name :=
            match lhs with
            | .atom (.symbol sym) => sym.name
            | .atom (.keyword key) => s!":{key}"
            | _ => toString lhs
          some (name, rhs)
      | _ => none

private def parseBindingExpr (bindingSpec : String) : TacticM (List (String × SExpr)) := do
  let expr ←
    match ACL2.Parse.parseAll bindingSpec with
    | .ok [expr] => pure expr
    | .ok _ => throwError "Expected one ACL2 binding list expression"
    | .error err => throwError s!"Could not parse ACL2 instance bindings: {err}"
  match expr.toList? with
  | some items =>
      let bindings := items.filterMap bindingOfSExpr?
      if bindings.length = items.length then
        pure bindings
      else
        match bindingOfSExpr? expr with
        | some binding => pure [binding]
        | none => throwError "ACL2 instance bindings must be a list of pairs like ((n (/ n 2)))"
  | none =>
      match bindingOfSExpr? expr with
      | some binding => pure [binding]
      | none => throwError "ACL2 instance bindings must be a list of pairs like ((n (/ n 2)))"

private def buildAppliedTheoremSyntax
    (declName : Name)
    (bindings : List (String × SExpr)) : TacticM (TSyntax `term) := do
  let mut term : TSyntax `term := mkIdent declName
  for (name, value) in bindings do
    let binderIdent := mkIdent (identNameOfAcl2String name)
    let value ← acl2TermSyntax value
    term ← `($term ($binderIdent:ident := $value))
  pure term

private def resolveImportedCandidates (acl2Name : String) : TacticM (List Name) := do
  let registry := ImportedRegistry.snapshot (← getEnv)
  let candidates := ImportedRegistry.resolve registry acl2Name
  if candidates.isEmpty then
    throwError m!"No imported Lean theorem is registered for ACL2 theorem {acl2Name}"
  pure candidates

private def tryImportedTerms
    (acl2Name : String)
    (declNames : List Name)
    (mkTerm : Name → TacticM (TSyntax `term)) : TacticM Unit := do
  for declName in declNames do
    let term ← mkTerm declName
    let saved ← saveState
    try
      evalTactic (← `(tactic| exact $term))
      return
    catch _ =>
      saved.restore
    try
      evalTactic (← `(tactic| apply $term))
      return
    catch _ =>
      saved.restore
  throwError m!"Imported Lean theorems for ACL2 theorem {acl2Name} were found ({String.intercalate ", " (declNames.map toString)}), but none matched the current goal."

/--
Helper to find the first recursive function application in an expression.
-/
partial def findRecursiveApp (e : Expr) : MetaM (Option (Name × Array Expr)) := do
  let env ← getEnv
  match e with
  | .app .. =>
    let fn := e.getAppFn
    let args := e.getAppArgs
    if let .const declName .. := fn then
      -- Check if it's a recursive definition (has an induct principle)
      if env.contains (declName ++ `induct) then
        let s := declName.toString
        -- Filter out common tactic/logic/init/lean namespaces
        let isBuiltin := s.startsWith "Lean" || s.startsWith "Init" || s.startsWith "ACL2.Logic" || s.startsWith "ACL2.Tactics" || s == "toBool" || s == "if_" || s == "toInt" || s == "toNat" || s == "not" || s == "equal"
        if !isBuiltin then
          return some (declName, args)
    for arg in args do
      if let some res ← findRecursiveApp arg then
        return some res
    return none
  | .lam _ _ b _ => findRecursiveApp b
  | .forallE _ _ b _ => findRecursiveApp b
  | .letE _ _ v b _ => do
    match ← findRecursiveApp v with
    | some res => return some res
    | none => findRecursiveApp b
  | .mdata _ e => findRecursiveApp e
  | .proj _ _ e => findRecursiveApp e
  | _ => return none

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
`acl2_use "acl2-theorem-name"` resolves the ACL2 theorem name through the
imported-theorem registry and tries the matching Lean theorem(s) with `exact`
and `apply`.
-/
elab "acl2_use " theoremName:str : tactic => do
  let acl2Name := theoremName.getString
  let candidates ← resolveImportedCandidates acl2Name
  tryImportedTerms acl2Name candidates (fun declName => pure (mkIdent declName))

/--
`acl2_use_instance "acl2-theorem-name" with "((n (/ n 2)))"` resolves the ACL2
theorem name through the imported-theorem registry, translates the ACL2-style
binding list into Lean ACL2 terms, and tries the matching theorem(s) with named
arguments via `exact` and `apply`.
-/
elab "acl2_use_instance " theoremName:str " with " bindingSpec:str : tactic => do
  let acl2Name := theoremName.getString
  let bindings ← parseBindingExpr bindingSpec.getString
  let candidates ← resolveImportedCandidates acl2Name
  tryImportedTerms acl2Name candidates (fun declName => buildAppliedTheoremSyntax declName bindings)

/--
`acl2_induct [f [args...]]` applies the induction principle for the function `f`.
If `f` is omitted, it tries to find a recursive function call in the goal.
-/
elab "acl2_induct" f:(ident)? args:term* : tactic => do
  let (fName, fArgs) ← match f with
    | some id => pure (id.getId, args)
    | none => do
      let goal ← getMainGoal
      let target ← goal.getType
      match ← findRecursiveApp target with
      | some (name, eArgs) =>
        let tArgs ← eArgs.mapM fun e => do
          let stx ← Term.exprToSyntax e
          return (TSyntax.mk stx)
        pure (name, tArgs)
      | none => throwError "Could not find a recursive function call to induct on."

  let inductName := fName ++ `induct
  let inductTerm := mkIdent inductName
  let mut targets : Array (TSyntax ``Parser.Tactic.elimTarget) := fArgs.map fun a => ⟨a.raw⟩

  if targets.isEmpty then
     let mut fvarNames := #[]
     for fvarId in (← getLCtx).getFVarIds do
       let localDecl ← fvarId.getDecl
       if !localDecl.isAuxDecl then
         fvarNames := fvarNames.push localDecl.userName

     if fvarNames.isEmpty then
       evalTactic (← `(tactic| apply $(inductTerm)))
     else
       let fvarIdents := fvarNames.map mkIdent
       let fvarTargets : Array (TSyntax ``Parser.Tactic.elimTarget) := fvarIdents.map fun id => ⟨id.raw⟩
       evalTactic (← `(tactic| induction $[$fvarTargets],* using $inductTerm))
  else
     evalTactic (← `(tactic| induction $[$targets],* using $inductTerm))

end Tactics
end ACL2
