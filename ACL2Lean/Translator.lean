import ACL2Lean.Syntax

namespace ACL2

namespace Translator

def translateSymbol (s : Symbol) : String :=
  if s.name = "+" || s.name = "binary-+" then "Logic.plus"
  else if s.name = "-" || s.name = "binary--" then "Logic.minus"
  else if s.name = "*" || s.name = "binary-*" then "Logic.times"
  else if s.name = "/" then "Logic.div"
  else if s.name = "<" then "Logic.lt"
  else if s.name = "=" then "Logic.eq"
  else if s.name = ">" then "Logic.gt"
  else if s.name = "<=" then "Logic.le"
  else if s.name = ">=" then "Logic.ge"
  else if s.name = "if" then "Logic.if_"
  else if s.name = "and" then "Logic.and"
  else if s.name = "or" then "Logic.or"
  else if s.name = "not" then "Logic.not"
  else if s.name = "implies" then "Logic.implies"
  else if s.name = "equal" then "Logic.equal"
  else if s.name = "consp" then "Logic.consp"
  else if s.name = "atom" then "Logic.atom"
  else if s.name = "car" then "Logic.car"
  else if s.name = "cdr" then "Logic.cdr"
  else if s.name = "cons" then "Logic.cons"
  else if s.name = "list" then "Logic.list"
  else if s.name = "zp" then "Logic.zp"
  else if s.name = "evenp" then "Logic.evenp"
  else if s.name = "oddp" then "Logic.oddp"
  else if s.name = "integerp" then "Logic.integerp"
  else if s.name = "posp" then "Logic.posp"
  else if s.name = "natp" then "Logic.natp"
  else if s.name = "expt" then "Logic.expt"
  else
    let name := s.name.toLower
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
  | .cons (.atom (.symbol { name := "quote", .. })) (.cons v .nil) =>
      s!"(Logic.quote_ {repr v})"
  | .cons (.atom (.symbol { name := "if", .. })) (.cons c (.cons t (.cons e .nil))) =>
      s!"(Logic.if_ {translateExpr c} {translateExpr t} {translateExpr e})"
  | .cons (.atom (.symbol s)) argsExpr =>
      let args := match argsExpr.toList? with | some l => l.map translateExpr | none => []
      let fn := translateSymbol s
      if ["Logic.plus", "Logic.times", "Logic.and", "Logic.or"].contains fn && args.length > 2 then
        foldNary fn args
      else if args.isEmpty then fn else s!"({fn} {String.intercalate " " args})"
  | _ => s!"sorry /- {repr expr} -/"

partial def collectVars (expr : SExpr) (acc : List String := []) : List String :=
  match expr with
  | .atom (.symbol s) =>
      let name := translateSymbol s
      if name.startsWith "Logic." then acc
      else if ["nil", "true", "false", "rational", "decimal"].contains name then acc
      else if acc.contains name then acc
      else name :: acc
  | .cons (.atom (.symbol { name := "quote", .. })) _ => acc
  | .cons (.atom (.symbol { name := "if", .. })) (.cons c (.cons t (.cons e .nil))) =>
      let acc := collectVars c acc
      let acc := collectVars t acc
      collectVars e acc
  | .cons (.atom (.symbol _)) argsExpr =>
      match argsExpr.toList? with
      | some args => args.foldl (fun a e => collectVars e a) acc
      | none => acc
  | _ => acc

def sanitizeName (s : String) : String :=
  let s := s.replace "-" "_"
  let s := s.replace "=" "_eq_"
  let s := s.replace "+" "_plus_"
  let s := s.replace "*" "_times_"
  let s := s.replace "/" "_div_"
  let s := s.replace "Logic." ""
  s

def translateDefun (name : Symbol) (formals : List Symbol) (body : SExpr) : String :=
  let nameStr := translateSymbol name
  let fmls := String.intercalate " " (formals.map fun s => s!"({translateSymbol s} : SExpr)")
  s!"partial def {nameStr} {fmls} : SExpr :=\n  {translateExpr body}"

def translateDefthm (name : Symbol) (body : SExpr) (hints : Option SExpr) : String :=
  let nameStr := sanitizeName (translateSymbol name)
  let vars := (collectVars body []).reverse
  let fmls := String.intercalate " " (vars.map fun v => s!"({v} : SExpr)")
  let hintStr := match hints with | some h => s!" /- hints: {repr h} -/" | none => ""
  s!"theorem {nameStr} {fmls} : Logic.toBool ({translateExpr body}) = true :={hintStr}\n  sorry"

end Translator

end ACL2
