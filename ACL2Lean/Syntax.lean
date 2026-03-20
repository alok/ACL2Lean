import Std.Data.HashMap
import Lean
import ACL2Lean.DSL.SyntaxCategories

open Lean

namespace ACL2

/-- Symbols cover ACL2 package-qualified names (e.g. `ACL2::CAR`). -/
structure Symbol where
  package : String := "ACL2"
  name : String
  deriving DecidableEq, BEq, Hashable, Inhabited

namespace Symbol

@[inline] def normalizedName (s : Symbol) : String :=
  s.name.map Char.toLower

@[inline] def isNamed (s : Symbol) (name : String) : Bool :=
  s.normalizedName = name.map Char.toLower

end Symbol

instance : Repr Symbol where
  reprPrec s _ :=
    if s.package == "ACL2" then s.name else s.package ++ "::" ++ s.name

/-- Keywords are stored without the leading colon. -/
abbrev Keyword := String

/-- Numeric literals include integers and common decimal rationals. -/
inductive Number
  | int (value : Int)
  | rational (numerator : Int) (denominator : Nat)
  | decimal (mantissa : Int) (exponent : Int)
  deriving DecidableEq

instance : Repr Number where
  reprPrec n _ := match n with
    | .int v => repr v
    | .rational n d => s!"{n}/{d}"
    | .decimal m e => s!"{m}E{e}"

inductive Atom
  | symbol (value : Symbol)
  | keyword (value : Keyword)
  | string (value : String)
  | bool (value : Bool)
  | number (value : Number)
  deriving DecidableEq

instance : Repr Atom where
  reprPrec a _ := match a with
    | .symbol s => repr s
    | .keyword k => ":" ++ k
    | .string s => repr s
    | .bool true => "T"
    | .bool false => "NIL"
    | .number n => repr n

/-- Minimal s-expression structure to model ACL2 source. -/
inductive SExpr
  | nil
  | atom (a : Atom)
  | cons (car : SExpr) (cdr : SExpr)
  deriving DecidableEq, Inhabited

namespace SExpr

/-- Build a proper list. -/
@[simp] def ofList : List SExpr → SExpr
  | [] => SExpr.nil
  | a :: tl => SExpr.cons a (ofList tl)

/-- Attempt to view an s-expression as a proper list. -/
def toList? : SExpr → Option (List SExpr)
  | .nil => .some []
  | .atom _ => .none
  | .cons hd tl => do
      let rest ← toList? tl
      .some (hd :: rest)

/-- Return the first symbol for quick event classification. -/
def headSymbol? : SExpr → Option Symbol
  | .cons (.atom (.symbol s)) _ => some s
  | .cons (.atom (.keyword _)) _ => none
  | .cons (.atom _) _ => none
  | _ => none

end SExpr

partial def SExpr.toString : SExpr → String
  | .nil => "NIL"
  | .atom a => s!"{repr a}"
  | s@(.cons _ _) =>
    match s.toList? with
    | some l => "(" ++ " ".intercalate (l.map toString) ++ ")"
    | none => match s with
      | .cons car cdr => s!"({toString car} . {toString cdr})"
      | _ => ""

instance : ToString SExpr where
  toString := SExpr.toString

instance : Repr SExpr where
  reprPrec s _ := s.toString

structure TheoremOption where
  key : Keyword
  value : SExpr
  deriving DecidableEq, Inhabited, Repr

inductive TheoryExpr
  | enable (items : List SExpr)
  | disable (items : List SExpr)
  | e_d (enabled : List SExpr) (disabled : List SExpr)
  | literal (items : List SExpr)
  | union (lhs : TheoryExpr) (rhs : TheoryExpr)
  | setDifference (lhs : TheoryExpr) (rhs : TheoryExpr)
  | cons (item : SExpr) (rest : TheoryExpr)
  | call (name : String) (args : List SExpr := [])
  | ref (expr : SExpr)
  | raw (expr : SExpr)
  deriving DecidableEq, Inhabited, Repr

structure GoalHint where
  goal : String
  options : List TheoremOption := []
  deriving DecidableEq, Inhabited, Repr

inductive ProofInstruction
  | atom (name : String)
  | command (name : String) (args : List SExpr := [])
  | block (name : String) (steps : List ProofInstruction)
  | raw (expr : SExpr)
  deriving Inhabited, Repr

structure RuleClass where
  name : String
  options : List TheoremOption := []
  deriving DecidableEq, Inhabited, Repr

structure TheoremInfo where
  body : SExpr
  options : List TheoremOption := []
  deriving DecidableEq, Inhabited, Repr

namespace TheoremOption

@[inline] private def normalizeKey (key : Keyword) : Keyword :=
  key.map Char.toLower

def fromSExprs : List SExpr → List TheoremOption
  | .atom (.keyword key) :: value :: rest =>
      { key := normalizeKey key, value } :: fromSExprs rest
  | _ :: rest => fromSExprs rest
  | [] => []

def findValue? (options : List TheoremOption) (key : Keyword) : Option SExpr :=
  let key := normalizeKey key
  (options.find? fun option => option.key = key).map (·.value)

def render (option : TheoremOption) : String :=
  s!":{option.key} {option.value}"

end TheoremOption

namespace TheoryExpr

private def unpackItems (expr : SExpr) : List SExpr :=
  match expr.toList? with
  | some items => items
  | none => [expr]

private def trimLeftSpaces (line : String) : String :=
  String.ofList <| line.toList.dropWhile (· = ' ')

@[inline] private def renderIndent (indent : Nat) : String :=
  String.ofList (List.replicate indent ' ')

private def quotedItems (expr : SExpr) : List SExpr :=
  match expr.toList? with
  | some (.atom (.keyword _) :: _) => [expr]
  | some items => items
  | none => [expr]

private def unquote? : SExpr → Option SExpr
  | .cons (.atom (.symbol sym)) (.cons inner .nil) =>
      if sym.isNamed "quote" then some inner else none
  | _ => none

private def unquoteItem (expr : SExpr) : SExpr :=
  match unquote? expr with
  | some inner => inner
  | none => expr

partial def ofSExpr (expr : SExpr) : TheoryExpr :=
  match unquote? expr with
  | some inner => .literal (quotedItems inner)
  | none =>
      match expr.toList? with
      | some (SExpr.atom (.symbol head) :: rest) =>
          if head.isNamed "enable" then
            .enable rest
          else if head.isNamed "disable" then
            .disable rest
          else if head.isNamed "e/d" then
            match rest with
            | [enabled, disabled] => .e_d (unpackItems enabled) (unpackItems disabled)
            | _ => .raw expr
          else if head.isNamed "union-theories" then
            match rest with
            | [lhs, rhs] => .union (ofSExpr lhs) (ofSExpr rhs)
            | _ => .call head.normalizedName rest
          else if head.isNamed "set-difference-theories" then
            match rest with
            | [lhs, rhs] => .setDifference (ofSExpr lhs) (ofSExpr rhs)
            | _ => .call head.normalizedName rest
          else if head.isNamed "cons" then
            match rest with
            | [item, tail] => .cons (unquoteItem item) (ofSExpr tail)
            | _ => .call head.normalizedName rest
          else
            .call head.normalizedName rest
      | _ =>
          match expr with
          | .atom _ => .ref expr
          | _ => .raw expr

private def renderItems (items : List SExpr) : String :=
  String.intercalate ", " (items.map toString)

partial def renderLines (indent : Nat := 0) : TheoryExpr → List String
  | .enable items =>
      s!"{renderIndent indent}enable" ::
        items.map (fun item => s!"{renderIndent (indent + 2)}{item}")
  | .disable items =>
      s!"{renderIndent indent}disable" ::
        items.map (fun item => s!"{renderIndent (indent + 2)}{item}")
  | .e_d enabled disabled =>
      [ s!"{renderIndent indent}e/d"
      , s!"{renderIndent (indent + 2)}enable"
      ] ++
        enabled.map (fun item => s!"{renderIndent (indent + 4)}{item}") ++
        [ s!"{renderIndent (indent + 2)}disable" ] ++
        disabled.map (fun item => s!"{renderIndent (indent + 4)}{item}")
  | .literal items =>
      s!"{renderIndent indent}literal-set" ::
        items.map (fun item => s!"{renderIndent (indent + 2)}{item}")
  | .union lhs rhs =>
      [s!"{renderIndent indent}union-theories"] ++
        renderLines (indent + 2) lhs ++
        renderLines (indent + 2) rhs
  | .setDifference lhs rhs =>
      [s!"{renderIndent indent}set-difference-theories"] ++
        renderLines (indent + 2) lhs ++
        renderLines (indent + 2) rhs
  | .cons item rest =>
      [ s!"{renderIndent indent}cons"
      , s!"{renderIndent (indent + 2)}{item}"
      ] ++ renderLines (indent + 2) rest
  | .call name [] => [s!"{renderIndent indent}{name}"]
  | .call name args => [s!"{renderIndent indent}{name}: {renderItems args}"]
  | .ref expr => [s!"{renderIndent indent}{expr}"]
  | .raw expr => [s!"{renderIndent indent}{expr}"]

def labeledLines (label : String) (expr : TheoryExpr) (indent : Nat := 0) : List String :=
  match renderLines (indent + 2) expr with
  | [] => [s!"{renderIndent indent}{label}"]
  | first :: rest =>
      s!"{renderIndent indent}{label}: {trimLeftSpaces first}" :: rest

partial def bulletItems : TheoryExpr → List String
  | .enable items => items.map (fun item => s!"enable {item}")
  | .disable items => items.map (fun item => s!"disable {item}")
  | .e_d enabled disabled =>
      (enabled.map (fun item => s!"enable {item}")) ++
        (disabled.map (fun item => s!"disable {item}"))
  | .literal items => items.map (fun item => s!"literal {item}")
  | .union lhs rhs => ["union-theories"] ++ bulletItems lhs ++ bulletItems rhs
  | .setDifference lhs rhs =>
      ["set-difference-theories"] ++ bulletItems lhs ++ bulletItems rhs
  | .cons item rest => [s!"cons {item}"] ++ bulletItems rest
  | .call name [] => [name]
  | .call name args => [s!"{name} {renderItems args}"]
  | .ref expr => [toString expr]
  | .raw expr => [toString expr]

def summary : TheoryExpr → String
  | .enable items => s!"enable [{renderItems items}]"
  | .disable items => s!"disable [{renderItems items}]"
  | .e_d enabled disabled =>
      s!"e/d enable [{renderItems enabled}] disable [{renderItems disabled}]"
  | .literal items => s!"literal [{renderItems items}]"
  | .union lhs rhs => s!"union-theories ({summary lhs}) ({summary rhs})"
  | .setDifference lhs rhs =>
      s!"set-difference-theories ({summary lhs}) ({summary rhs})"
  | .cons item rest => s!"cons {item} onto ({summary rest})"
  | .call name [] => name
  | .call name args => s!"{name} [{renderItems args}]"
  | .ref expr => toString expr
  | .raw expr => toString expr

end TheoryExpr

namespace GoalHint

private def renderGoal (expr : SExpr) : String :=
  match expr with
  | .atom (.string s) => s
  | .atom (.symbol s) => toString (SExpr.atom (.symbol s))
  | _ => toString expr

def ofSExpr? (expr : SExpr) : Option GoalHint := do
  let items ← expr.toList?
  match items with
  | goalExpr :: rest =>
      some { goal := renderGoal goalExpr, options := TheoremOption.fromSExprs rest }
  | [] => none

def findOption? (hint : GoalHint) (key : Keyword) : Option SExpr :=
  TheoremOption.findValue? hint.options key

def inTheory? (hint : GoalHint) : Option TheoryExpr :=
  hint.findOption? "in-theory" |>.map TheoryExpr.ofSExpr

@[inline] private def renderIndent (indent : Nat) : String :=
  String.ofList (List.replicate indent ' ')

private def trimLeftSpaces (line : String) : String :=
  String.ofList <| line.toList.dropWhile (· = ' ')

def renderLines (indent : Nat := 0) (hint : GoalHint) : List String :=
  let header := s!"{renderIndent indent}hint {hint.goal}"
  let basics :=
    [ hint.findOption? "use" |>.map (fun useExpr => [s!"{renderIndent (indent + 2)}use {useExpr}"])
    , hint.inTheory? |>.map (fun theoryExpr => TheoryExpr.labeledLines "in-theory" theoryExpr (indent + 2))
    , hint.findOption? "induct" |>.map (fun inductExpr => [s!"{renderIndent (indent + 2)}induct {inductExpr}"])
    , hint.findOption? "expand" |>.map (fun expandExpr => [s!"{renderIndent (indent + 2)}expand {expandExpr}"])
    , hint.findOption? "do-not-induct"
        |>.map (fun dniExpr => [s!"{renderIndent (indent + 2)}do-not-induct {dniExpr}"])
    ].filterMap id |>.foldr List.append []
  let handled := ["use", "in-theory", "induct", "expand", "do-not-induct"]
  let extras :=
    hint.options
      |>.filter (fun option => !handled.contains option.key)
      |>.map (fun option => s!"{renderIndent (indent + 2)}:{option.key} {option.value}")
  header :: basics ++ extras

def summary (hint : GoalHint) : String :=
  String.intercalate " | " ((renderLines 0 hint).map trimLeftSpaces)

end GoalHint

namespace ProofInstruction

@[inline] private def renderIndent (indent : Nat) : String :=
  String.ofList (List.replicate indent ' ')

private def instructionName? : SExpr → Option String
  | .atom (.keyword key) => some key
  | .atom (.symbol sym) => some sym.normalizedName
  | _ => none

private def isQuotedName (name : String) : Bool :=
  name = "quote" || name = "quasiquote" || name = "unquote" || name = "unquote-splicing"

private def allowsNestedSteps (name : String) : Bool :=
  name = "quiet!" || name = "repeat"

private def looksLikeInstruction : SExpr → Bool
  | .atom (.keyword _) => true
  | .atom (.symbol _) => true
  | expr =>
      match expr.toList? with
      | some (head :: _) =>
          match instructionName? head with
          | some name => !isQuotedName name
          | none => false
      | _ => false

partial def ofSExpr : SExpr → ProofInstruction
  | .atom (.keyword key) => .atom key
  | .atom (.symbol sym) => .atom sym.normalizedName
  | expr =>
      match expr.toList? with
      | some (head :: rest) =>
          match instructionName? head with
          | some name =>
              if allowsNestedSteps name && rest.all looksLikeInstruction then
                .block name (rest.map ofSExpr)
              else
                .command name rest
          | none => .raw expr
      | _ => .raw expr

private def goalHintsFromExpr (expr : SExpr) : List GoalHint :=
  match GoalHint.ofSExpr? expr with
  | some hint => [hint]
  | none =>
      match expr.toList? with
      | some items => items.filterMap GoalHint.ofSExpr?
      | none => []

def goalHints : ProofInstruction → List GoalHint
  | .command "bash" args => (args.map goalHintsFromExpr).foldr List.append []
  | _ => []

def theoryExpr? : ProofInstruction → Option TheoryExpr
  | .command "in-theory" [expr] => some (TheoryExpr.ofSExpr expr)
  | _ => none

private def renderArgs (args : List SExpr) : String :=
  String.intercalate "; " (args.map toString)

partial def renderLines (indent : Nat := 0) : ProofInstruction → List String
  | .atom name => [s!"{renderIndent indent}{name}"]
  | .raw expr => [s!"{renderIndent indent}{expr}"]
  | .command "bash" args =>
      let hints := goalHints (.command "bash" args)
      if hints.isEmpty then
        [s!"{renderIndent indent}bash: {renderArgs args}"]
      else
        let header := s!"{renderIndent indent}bash:"
        let hintLines := (hints.map (GoalHint.renderLines (indent + 2))).foldr List.append []
        header :: hintLines
  | inst@(.command "in-theory" args) =>
      match inst.theoryExpr? with
      | some theoryExpr => TheoryExpr.labeledLines "in-theory" theoryExpr indent
      | none => [s!"{renderIndent indent}in-theory: {renderArgs args}"]
  | .command name args =>
      if args.isEmpty then
        [s!"{renderIndent indent}{name}"]
      else
        [s!"{renderIndent indent}{name}: {renderArgs args}"]
  | .block name steps =>
      let header := s!"{renderIndent indent}{name}"
      header :: (steps.map (renderLines (indent + 2))).foldr List.append []

end ProofInstruction

namespace RuleClass

def ofSExpr? : SExpr → Option RuleClass
  | .atom (.keyword key) => some { name := key.map Char.toLower }
  | expr => do
      let items ← expr.toList?
      match items with
      | .atom (.keyword key) :: rest =>
          some { name := key.map Char.toLower, options := TheoremOption.fromSExprs rest }
      | _ => none

def summary (ruleClass : RuleClass) : String :=
  let extraKeys := ruleClass.options.map (fun option => s!":{option.key}")
  if extraKeys.isEmpty then
    ruleClass.name
  else
    s!"{ruleClass.name} ({String.intercalate ", " extraKeys})"

end RuleClass

namespace TheoremInfo

def findOption? (info : TheoremInfo) (key : Keyword) : Option SExpr :=
  TheoremOption.findValue? info.options key

def hintGoals (info : TheoremInfo) : List GoalHint :=
  match info.findOption? "hints" with
  | some hints =>
      match hints.toList? with
      | some goals => goals.filterMap GoalHint.ofSExpr?
      | none => []
  | none => []

def ruleClasses (info : TheoremInfo) : List RuleClass :=
  match info.findOption? "rule-classes" with
  | some .nil => []
  | some (.atom (.keyword key)) => [{ name := key.map Char.toLower }]
  | some expr =>
      match expr.toList? with
      | some items => items.filterMap RuleClass.ofSExpr?
      | none => []
  | none => []

def extraOptions (info : TheoremInfo) : List TheoremOption :=
  info.options.filter (fun option =>
    option.key ≠ "hints" && option.key ≠ "rule-classes" && option.key ≠ "instructions")

def instructions (info : TheoremInfo) : List ProofInstruction :=
  match info.findOption? "instructions" with
  | some instructionsExpr =>
      match instructionsExpr.toList? with
      | some items => items.map ProofInstruction.ofSExpr
      | none => [ProofInstruction.ofSExpr instructionsExpr]
  | none => []

end TheoremInfo

-- DSL-like notation for S-expressions in Lean code
syntax "sexpr!{" acl2_sexpr "}" : term

/-- Capture the ACL2 package context for events. -/
structure PackageState where
  current : String := "ACL2"
  openImports : Std.HashMap String (List String) := {}
  deriving Inhabited, Repr

/-- Top-level ACL2 event skeleton. -/
inductive Event
  | inPackage (name : String)
  | includeBook (path : String) (dirs : List String := [])
  | defun (name : Symbol) (formals : List Symbol) (doc : Option String) (decls : List SExpr) (body : SExpr)
  | defthm (name : Symbol) (info : TheoremInfo)
  | defmacro (name : Symbol) (formals : List Symbol) (doc : Option String) (decls : List SExpr) (body : SExpr)
  | mutualRecursion (events : List Event)
  | local (event : Event)
  | inTheory (expr : SExpr)
  | encapsulate (events : List Event)
  | makeEvent (body : SExpr)
  | defrec (name : Symbol) (fields : List Symbol)
  | defconst (name : Symbol) (value : SExpr)
  | defstobj (name : Symbol) (fields : List SExpr)
  | table (name : Symbol) (args : List SExpr)
  | skip (raw : SExpr)
  deriving Repr, Inhabited

namespace Event

/-- Peel off docstrings and declarations from a function body list. -/
partial def parseDefunBody (doc : Option String) (decls : List SExpr) (rest : List SExpr) : (Option String × List SExpr × SExpr) :=
  match rest with
  | SExpr.atom (.string s) :: rest => parseDefunBody (some s) decls rest
  | (d@(SExpr.cons (SExpr.atom (.symbol sym)) _)) :: rest =>
      if sym.normalizedName = "declare" then
        parseDefunBody doc (d :: decls) rest
      else
        let body := match d :: rest with
          | [b] => b
          | many => SExpr.ofList many
        (doc, decls.reverse, body)
  | rest =>
        let body := match rest with
        | [b] => b
        | _ => SExpr.ofList rest
      (doc, decls.reverse, body)

/--
Best-effort recovery of a quasiquoted event skeleton.

This does not execute ACL2; it only peels away quasiquote syntax so that static
`make-event` expansions can still expose nested `defthm` / `defconst` forms.
-/
private partial def dequasiquote (depth : Nat) : SExpr → SExpr
  | expr@(.cons (.atom (.symbol sym)) (.cons inner .nil)) =>
      if sym.isNamed "quasiquote" then
        if depth = 0 then
          dequasiquote (depth + 1) inner
        else
          SExpr.ofList [SExpr.atom (.symbol sym), dequasiquote (depth + 1) inner]
      else if sym.isNamed "unquote" || sym.isNamed "unquote-splicing" then
        if depth = 1 then
          inner
        else
          SExpr.ofList [SExpr.atom (.symbol sym), dequasiquote (depth - 1) inner]
      else
        match expr with
        | .cons car cdr => .cons (dequasiquote depth car) (dequasiquote depth cdr)
        | _ => expr
  | .cons car cdr => .cons (dequasiquote depth car) (dequasiquote depth cdr)
  | expr => expr

/--
Peel lightweight wrappers that ACL2 commonly uses around generated events.

This stays syntactic: it does not attempt to evaluate arbitrary `let`/`cond`
terms produced inside `make-event`.
-/
private partial def unwrapGeneratedEventExpr (expr : SExpr) : SExpr :=
  let expr := dequasiquote 0 expr
  match expr.toList? with
  | some (.atom (.symbol sym) :: rest) =>
      if sym.isNamed "value" || sym.isNamed "value-triple" then
        match rest.reverse with
        | inner :: _ => unwrapGeneratedEventExpr inner
        | [] => expr
      else
        expr
  | _ => expr

/-- Quick best-effort to stratify an ACL2 event from its raw syntax. -/
partial def classify (sexpr : SExpr) : Event :=
  match sexpr with
  | .cons (.atom (.symbol sym)) rest =>
      match sym.normalizedName with
      | "in-package" =>
          match rest.toList? with
          | some [SExpr.atom (.string pkg)] => .inPackage pkg
          | some [SExpr.atom (.symbol pkg)] => .inPackage pkg.name
          | _ => .skip sexpr
      | "include-book" =>
          match rest.toList? with
          | some (SExpr.atom (.string path) :: tail) =>
              let dirs := tail.map fun
                | SExpr.atom (.keyword kw) => kw
                | _ => ""
              .includeBook path dirs
          | some (SExpr.atom (.symbol path) :: tail) =>
              let dirs := tail.map fun
                | SExpr.atom (.keyword kw) => kw
                | _ => ""
              .includeBook path.name dirs
          | _ => .skip sexpr
      | "defun" =>
          match rest.toList? with
          | some (SExpr.atom (.symbol name) :: params :: rest) =>
              let fmls :=
                match params.toList? with
                | some lst =>
                    lst.filterMap
                      (fun
                        | SExpr.atom (.symbol s) => some s
                        | _ => none)
                | none => []
              let (doc, decls, bodyExpr) := parseDefunBody none [] rest
              .defun name fmls doc decls bodyExpr
          | _ => .skip sexpr
      | "defthm" =>
          match rest.toList? with
          | some (SExpr.atom (.symbol name) :: body :: options) =>
              .defthm name { body, options := TheoremOption.fromSExprs options }
          | _ => .skip sexpr
      | "defmacro" =>
          match rest.toList? with
          | some (SExpr.atom (.symbol name) :: params :: rest) =>
              let fmls :=
                match params.toList? with
                | some lst =>
                    lst.filterMap
                      (fun
                        | SExpr.atom (.symbol s) => some s
                        | _ => none)
                | none => []
              let (doc, decls, bodyExpr) := parseDefunBody none [] rest
              .defmacro name fmls doc decls bodyExpr
          | _ => .skip sexpr
      | "local" =>
          match rest.toList? with
          | some [inner] => .local (classify inner)
          | _ => .skip sexpr
      | "with-output" =>
          match rest.toList? with
          | some args =>
              match args.reverse with
              | inner :: _ => classify inner
              | [] => .skip sexpr
          | _ => .skip sexpr
      | "in-theory" =>
          match rest.toList? with
          | some [expr] => .inTheory expr
          | _ => .skip sexpr
      | "mutual-recursion" =>
          match rest.toList? with
          | some lst => .mutualRecursion (lst.map classify)
          | _ => .skip sexpr
      | "encapsulate" =>
          match rest.toList? with
          | some (_ :: events) => .encapsulate (events.map classify)
          | _ => .skip sexpr
      | "make-event" => .makeEvent rest
      | "defrec" =>
          match rest.toList? with
          | some (SExpr.atom (.symbol name) :: params :: _) =>
              let fmls := match params.toList? with
                | some lst => lst.filterMap (fun | SExpr.atom (.symbol s) => some s | _ => none)
                | none => []
              .defrec name fmls
          | _ => .skip sexpr
      | "defconst" =>
          match rest.toList? with
          | some [SExpr.atom (.symbol name), val] => .defconst name val
          | _ => .skip sexpr
      | "defstobj" =>
          match rest.toList? with
          | some (SExpr.atom (.symbol name) :: fields) => .defstobj name fields
          | _ => .skip sexpr
      | "table" =>
          match rest.toList? with
          | some (SExpr.atom (.symbol name) :: args) => .table name args
          | _ => .skip sexpr
      | "program" =>
          match rest with
          | .nil => .skip sexpr
          | _ => .skip sexpr
      | "set-verify-guards-eagerness" => .skip sexpr
      | _ => .skip sexpr
  | _ => .skip sexpr

/-- Recover statically visible nested events from a `make-event`. -/
def generatedEvents (body : SExpr) : List Event :=
  match body.toList? with
  | some [generatedExpr] =>
      let recovered := unwrapGeneratedEventExpr generatedExpr
      match classify recovered with
      | .skip _ => []
      | event => [event]
  | _ => []

/-- Flatten nested ACL2 event structure into replay order. -/
partial def flatten : Event → List Event
  | .local inner => flatten inner
  | .mutualRecursion events => events.foldr (fun ev acc => flatten ev ++ acc) []
  | .encapsulate events => events.foldr (fun ev acc => flatten ev ++ acc) []
  | .makeEvent body =>
      let generated := generatedEvents body
      if generated.isEmpty then
        [.makeEvent body]
      else
        generated.foldr (fun ev acc => flatten ev ++ acc) []
  | event => [event]

def flattenList (events : List Event) : List Event :=
  events.foldr (fun ev acc => flatten ev ++ acc) []

end Event

/-- Semantics: interpret events into a growing environment. -/
structure World where
  package : PackageState := {}
  defs : Std.HashMap Symbol (List Symbol × SExpr) := {}
  macros : Std.HashMap Symbol (List Symbol × SExpr) := {}
  theorems : Std.HashMap Symbol TheoremInfo := {}
  theories : List TheoryExpr := []
  consts : Std.HashMap Symbol SExpr := {}
  recs : Std.HashMap Symbol (List Symbol) := {}
  stobjs : Std.HashMap Symbol (List SExpr) := {}
  tables : Std.HashMap Symbol (List SExpr) := {}
  deriving Repr

instance : Inhabited World :=
  ⟨{ package := {}, defs := {}, macros := {} }⟩

namespace World

/-- Install an event, currently ignoring proof obligations. -/
partial def step (w : World) (event : Event) : World :=
  match event with
  | .inPackage name => { w with package := { w.package with current := name } }
  | .includeBook _ _ => w
  | .defun name formals _ _ body => { w with defs := w.defs.insert name (formals, body) }
  | .defthm name info => { w with theorems := w.theorems.insert name info }
  | .defmacro name formals _ _ body => { w with macros := w.macros.insert name (formals, body) }
  | .local e => step w e
  | .inTheory expr => { w with theories := w.theories ++ [TheoryExpr.ofSExpr expr] }
  | .mutualRecursion evs => evs.foldl step w
  | .encapsulate evs => evs.foldl step w
  | .makeEvent body =>
      match Event.generatedEvents body with
      | [] => w
      | generated => generated.foldl step w
  | .defrec name fields => { w with recs := w.recs.insert name fields }
  | .defconst name value => { w with consts := w.consts.insert name value }
  | .defstobj name fields => { w with stobjs := w.stobjs.insert name fields }
  | .table name args => { w with tables := w.tables.insert name args }
  | .skip _ => w

/-- Replay a script of events. -/
def empty : World := { package := {}, defs := {}, macros := {} }

/-- Replay a script of events. -/
def replay (events : List Event) : World :=
  events.foldl step empty

end World

end ACL2
