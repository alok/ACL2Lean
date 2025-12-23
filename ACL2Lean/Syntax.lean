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
  | defthm (name : Symbol) (body : SExpr) (hints : Option SExpr := none)
  | defmacro (name : Symbol) (formals : List Symbol) (doc : Option String) (decls : List SExpr) (body : SExpr)
  | mutualRecursion (events : List Event)
  | local (event : Event)
  | inTheory (body : SExpr)
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
  | (d@(SExpr.cons (SExpr.atom (.symbol { name := "declare", .. })) _)) :: rest => parseDefunBody doc (d :: decls) rest
  | rest =>
      let body := match rest with
        | [b] => b
        | _ => SExpr.ofList rest
      (doc, decls.reverse, body)

/-- Quick best-effort to stratify an ACL2 event from its raw syntax. -/
partial def classify (sexpr : SExpr) : Event :=
  match sexpr with
  | .cons (.atom (.symbol { name := "in-package", .. })) rest =>
      match rest.toList? with
      | some [SExpr.atom (.string pkg)] => .inPackage pkg
      | some [SExpr.atom (.symbol sym)] => .inPackage sym.name
      | _ => .skip sexpr
  | .cons (.atom (.symbol { name := "include-book", .. })) rest =>
      match rest.toList? with
      | some (SExpr.atom (.string path) :: tail) =>
          let dirs := tail.map fun
            | SExpr.atom (.keyword kw) => kw
            | _ => ""
          .includeBook path dirs
      | some (SExpr.atom (.symbol sym) :: tail) =>
          let dirs := tail.map fun
            | SExpr.atom (.keyword kw) => kw
            | _ => ""
          .includeBook sym.name dirs
      | _ => .skip sexpr
  | .cons (.atom (.symbol { name := "defun", .. })) rest =>
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
  | .cons (.atom (.symbol { name := "defthm", .. })) rest =>
      match rest.toList? with
      | some (SExpr.atom (.symbol name) :: body :: hints) =>
          let hintExpr :=
            match hints with
            | [] => none
            | more => some (SExpr.ofList more)
          .defthm name body hintExpr
      | _ => .skip sexpr
  | .cons (.atom (.symbol { name := "defmacro", .. })) rest =>
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
  | .cons (.atom (.symbol { name := "local", .. })) rest =>
      match rest.toList? with
      | some [inner] => .local (classify inner)
      | _ => .skip sexpr
  | .cons (.atom (.symbol { name := "in-theory", .. })) body =>
      .inTheory body
  | .cons (.atom (.symbol { name := "mutual-recursion", .. })) rest =>
      match rest.toList? with
      | some lst => .mutualRecursion (lst.map classify)
      | _ => .skip sexpr
  | .cons (.atom (.symbol { name := "encapsulate", .. })) rest =>
      match rest.toList? with
      | some (_ :: events) => .encapsulate (events.map classify)
      | _ => .skip sexpr
  | .cons (.atom (.symbol { name := "make-event", .. })) rest =>
      .makeEvent rest
  | .cons (.atom (.symbol { name := "defrec", .. })) rest =>
      match rest.toList? with
      | some (SExpr.atom (.symbol name) :: params :: _) =>
          let fmls := match params.toList? with
            | some lst => lst.filterMap (fun | SExpr.atom (.symbol s) => some s | _ => none)
            | none => []
          .defrec name fmls
      | _ => .skip sexpr
  | .cons (.atom (.symbol { name := "defconst", .. })) rest =>
      match rest.toList? with
      | some [SExpr.atom (.symbol name), val] => .defconst name val
      | _ => .skip sexpr
  | .cons (.atom (.symbol { name := "defstobj", .. })) rest =>
      match rest.toList? with
      | some (SExpr.atom (.symbol name) :: fields) => .defstobj name fields
      | _ => .skip sexpr
  | .cons (.atom (.symbol { name := "table", .. })) rest =>
      match rest.toList? with
      | some (SExpr.atom (.symbol name) :: args) => .table name args
      | _ => .skip sexpr
  | .cons (.atom (.symbol { name := "program", .. })) .nil => .skip sexpr
  | .cons (.atom (.symbol { name := "set-verify-guards-eagerness", .. })) _ => .skip sexpr
  | _ => .skip sexpr

end Event

/-- Semantics: interpret events into a growing environment. -/
structure World where
  package : PackageState := {}
  defs : Std.HashMap Symbol (List Symbol × SExpr) := {}
  macros : Std.HashMap Symbol (List Symbol × SExpr) := {}
  theorems : Std.HashMap Symbol SExpr := {}
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
  | .defthm name body _ => { w with theorems := w.theorems.insert name body }
  | .defmacro name formals _ _ body => { w with macros := w.macros.insert name (formals, body) }
  | .local e => step w e
  | .inTheory _ => w
  | .mutualRecursion evs => evs.foldl step w
  | .encapsulate evs => evs.foldl step w
  | .makeEvent _ => w
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
