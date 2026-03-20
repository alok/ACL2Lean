import ACL2Lean.Syntax

namespace ACL2

namespace Translator

def translateSymbol (s : Symbol) : String :=
  let name := s.normalizedName
  if name = "+" || name = "binary-+" then "Logic.plus"
  else if name = "-" || name = "binary--" then "Logic.minus"
  else if name = "*" || name = "binary-*" then "Logic.times"
  else if name = "/" then "Logic.div"
  else if name = "<" then "Logic.lt"
  else if name = "=" then "Logic.eq"
  else if name = ">" then "Logic.gt"
  else if name = "<=" then "Logic.le"
  else if name = ">=" then "Logic.ge"
  else if name = "if" then "Logic.if_"
  else if name = "and" then "Logic.and"
  else if name = "or" then "Logic.or"
  else if name = "not" then "Logic.not"
  else if name = "implies" then "Logic.implies"
  else if name = "equal" then "Logic.equal"
  else if name = "consp" then "Logic.consp"
  else if name = "atom" then "Logic.atom"
  else if name = "car" then "Logic.car"
  else if name = "cdr" then "Logic.cdr"
  else if name = "cons" then "Logic.cons"
  else if name = "list" then "Logic.list"
  else if name = "zp" then "Logic.zp"
  else if name = "evenp" then "Logic.evenp"
  else if name = "oddp" then "Logic.oddp"
  else if name = "integerp" then "Logic.integerp"
  else if name = "posp" then "Logic.posp"
  else if name = "natp" then "Logic.natp"
  else if name = "expt" then "Logic.expt"
  else if name = "endp" then "Logic.endp"
  else if name = "first" then "Logic.first"
  else if name = "second" then "Logic.second"
  else if name = "append" then "Logic.append"
  else if name = "len" then "Logic.len"
  else if name = "true-listp" then "Logic.trueListp"
  else if name = "lexorder" then "lexorder"
  else if name = "stringp" then "Logic.stringp"
  else if name = "string-append" then "Logic.string_append"
  else
    let name := name.replace "-" "_"
    let name := name.replace "!" "_bang"
    let name := name.replace "?" "_p"
    let name := name.replace "/" "_div_"
    let name := name.replace "+" "_plus_"
    let name := name.replace "*" "_times_"
    let name := name.replace "=" "_eq_"
    name

def foldNary (fn : String) (args : List String) : String :=
  match args with
  | [] => "SExpr.nil"
  | [a] => a
  | a :: rest => s!"({fn} {a} {foldNary fn rest})"

mutual
/-- Translate `(cond (test1 val1) (test2 val2) ... (t default))` to nested if_. -/
partial def translateCond (clauses : SExpr) : String :=
  match clauses with
  | .cons (.cons test (.cons val .nil)) rest =>
    match test with
    | .atom (.symbol s) =>
      if s.isNamed "t" then translateExpr val
      else s!"(Logic.if_ {translateExpr test} {translateExpr val} {translateCond rest})"
    | _ => s!"(Logic.if_ {translateExpr test} {translateExpr val} {translateCond rest})"
  | .nil => "SExpr.nil"
  | _ => s!"sorry /- malformed cond: {repr clauses} -/"

partial def translateExpr (expr : SExpr) : String :=
  match expr with
  | .nil => "SExpr.nil"
  | .atom (.bool true) => "(SExpr.atom (.bool true))"
  | .atom (.bool false) => "(SExpr.atom (.bool false))"
  | .atom (.number (.int n)) => s!"(SExpr.atom (.number (.int ({n}))))"
  | .atom (.number (.rational n d)) => s!"(Logic.rational ({n}) ({d}))"
  | .atom (.number (.decimal m e)) => s!"(Logic.decimal ({m}) ({e}))"
  | .atom (.string s) => s!"(SExpr.atom (.string \"{s}\"))"
  | .atom (.symbol s) => translateSymbol s
  | .cons (.atom (.symbol s)) argsExpr =>
      if s.isNamed "quote" then
        match argsExpr with
        | .cons v .nil => s!"(Logic.quote_ {repr v})"
        | _ => s!"sorry /- malformed quote: {repr expr} -/"
      else if s.isNamed "if" then
        match argsExpr with
        | .cons c (.cons t (.cons e .nil)) =>
            s!"(Logic.if_ {translateExpr c} {translateExpr t} {translateExpr e})"
        | _ => s!"sorry /- malformed if: {repr expr} -/"
      else if s.isNamed "cond" then
        translateCond argsExpr
      else if s.isNamed "1+" || s.isNamed "1+$inline" then
        match argsExpr with
        | .cons x .nil => s!"(Logic.plus {translateExpr x} 1)"
        | _ => s!"sorry /- malformed 1+: {repr expr} -/"
      else if s.isNamed "1-" || s.isNamed "1-$inline" then
        match argsExpr with
        | .cons x .nil => s!"(Logic.minus {translateExpr x} 1)"
        | _ => s!"sorry /- malformed 1-: {repr expr} -/"
      else if s.isNamed "cadr" then
        match argsExpr with
        | .cons x .nil => s!"(Logic.car (Logic.cdr {translateExpr x}))"
        | _ => s!"sorry /- malformed cadr: {repr expr} -/"
      else if s.isNamed "declare" then
        "" -- skip declarations
      else
        let args := match argsExpr.toList? with | some l => l.map translateExpr | none => []
        let fn := translateSymbol s
        if ["Logic.plus", "Logic.times", "Logic.and", "Logic.or"].contains fn && args.length > 2 then
          foldNary fn args
        else if args.isEmpty then fn else s!"({fn} {String.intercalate " " args})"
  | _ => s!"sorry /- {repr expr} -/"
end -- mutual (translateCond / translateExpr)

mutual
partial def collectVarsCond (clauses : SExpr) (acc : List String) : List String :=
  match clauses with
  | .cons (.cons test (.cons val .nil)) rest =>
    let acc := collectVars test acc
    let acc := collectVars val acc
    collectVarsCond rest acc
  | _ => acc

partial def collectVars (expr : SExpr) (acc : List String := []) : List String :=
  match expr with
  | .atom (.symbol s) =>
      let name := translateSymbol s
      if name.startsWith "Logic." then acc
      else if ["nil", "true", "false", "rational", "decimal"].contains name then acc
      else if acc.contains name then acc
      else name :: acc
  | .cons (.atom (.symbol s)) argsExpr =>
      if s.isNamed "quote" then
        acc
      else if s.isNamed "if" then
        match argsExpr with
        | .cons c (.cons t (.cons e .nil)) =>
            let acc := collectVars c acc
            let acc := collectVars t acc
            collectVars e acc
        | _ => acc
      else if s.isNamed "cond" then
        collectVarsCond argsExpr acc
      else if s.isNamed "declare" then
        acc
      else
        match argsExpr.toList? with
        | some args => args.foldl (fun a e => collectVars e a) acc
        | none => acc
  | _ => acc
end -- mutual

def sanitizeName (s : String) : String :=
  let s := s.replace "-" "_"
  let s := s.replace "=" "_eq_"
  let s := s.replace "+" "_plus_"
  let s := s.replace "*" "_times_"
  let s := s.replace "/" "_div_"
  let s := s.replace "Logic." ""
  s

/-- Find which formals are recursed on (appear as argument to cdr in recursive calls). -/
private partial def findRecursiveArg (name : Symbol) (formals : List Symbol) (body : SExpr) : Option String :=
  -- Simple heuristic: if the body contains `(name ... (cdr formal) ...)`,
  -- the function recurs on that formal via cdr.
  -- For the sorting corpus this covers most cases.
  let nameStr := name.normalizedName
  let rec go (expr : SExpr) : Option String :=
    match expr with
    | .cons (.atom (.symbol s)) args =>
      if s.isNamed nameStr then
        -- Check args for (cdr formal)
        match args.toList? with
        | some argList =>
          argList.findSome? fun arg =>
            match arg with
            | .cons (.atom (.symbol cdrSym)) (.cons (.atom (.symbol formal)) .nil) =>
              if cdrSym.isNamed "cdr" then
                formals.find? (fun f => f.isNamed formal.normalizedName) |>.map translateSymbol
              else none
            | _ => none
        | none => none
      else
        match args.toList? with
        | some argList => argList.findSome? go
        | none => none
    | .cons a b =>
      match go a with
      | some r => some r
      | none => go b
    | _ => none
  go body

def translateDefun (name : Symbol) (formals : List Symbol) (body : SExpr) : String :=
  let nameStr := translateSymbol name
  let fmls := String.intercalate " " (formals.map fun s => s!"({translateSymbol s} : SExpr)")
  let bodyStr := translateExpr body
  match findRecursiveArg name formals body with
  | some arg =>
    s!"def {nameStr} {fmls} : SExpr :=\n  {bodyStr}\ntermination_by SExpr.acl2Count {arg}\ndecreasing_by all_goals (simp_all [Logic.car, Logic.cdr, Logic.endp, Logic.consp, Logic.toBool, SExpr.acl2Count]; omega)"
  | none =>
    -- Check if body references the function name at all (simple recursion check)
    let isRecursive := (bodyStr.splitOn nameStr).length > 1
    if isRecursive then
      s!"partial def {nameStr} {fmls} : SExpr :=\n  {bodyStr}"
    else
      s!"def {nameStr} {fmls} : SExpr :=\n  {bodyStr}"

private def renderMetadataComment (info : TheoremInfo) : String :=
  let ruleClassLines :=
    match info.ruleClasses.map RuleClass.summary with
    | [] => []
    | ruleClasses => [s!"rule-classes: {String.intercalate ", " ruleClasses}"]
  let hintLines := info.hintGoals.map GoalHint.summary
  let instructionLines :=
    match info.instructions with
    | [] => []
    | instructions =>
        ["instructions:"] ++ (instructions.map (ProofInstruction.renderLines 2)).foldr List.append []
  let extraKeys := info.extraOptions.map (fun option => s!":{option.key}")
  let extraLines :=
    match extraKeys with
    | [] => []
    | keys => [s!"other-options: {String.intercalate ", " keys}"]
  let lines := ruleClassLines ++ hintLines ++ instructionLines ++ extraLines
  if lines.isEmpty then
    ""
  else
    let body := String.intercalate "\n" (lines.map fun line => s!"  {line}")
    s!"/- ACL2 metadata:\n{body}\n-/\n"

def translateDefthm (name : Symbol) (info : TheoremInfo) : String :=
  let nameStr := sanitizeName (translateSymbol name)
  let vars := (collectVars info.body []).reverse
  let fmls := String.intercalate " " (vars.map fun v => s!"({v} : SExpr)")
  let metaComment := renderMetadataComment info
  s!"{metaComment}theorem {nameStr} {fmls} : Logic.toBool ({translateExpr info.body}) = true :=\n  sorry"

private def uppercaseIfExpr : SExpr :=
  .cons
    (.atom (.symbol { name := "IF" }))
    (SExpr.ofList
      [ .atom (.bool true)
      , .cons (.atom (.symbol { name := "CONS" }))
          (SExpr.ofList [ .atom (.symbol { name := "X" }), .nil ])
      , .nil
      ])

#guard translateSymbol { name := "BINARY-+" } = "Logic.plus"
#guard (translateExpr uppercaseIfExpr).startsWith "(Logic.if_"
#guard (translateDefthm { name := "PLUS-COMM" } { body := uppercaseIfExpr }).contains "theorem plus_comm"

end Translator

end ACL2
