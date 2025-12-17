import Std.Data.HashMap

namespace ACL2

/-- Symbols cover ACL2 package-qualified names (e.g. `ACL2::CAR`). -/
structure Symbol where
  package : String := "ACL2"
  name : String
  deriving Repr, DecidableEq, BEq, Hashable, Inhabited

/-- Keywords are stored without the leading colon. -/
abbrev Keyword := String

/-- Numeric literals include integers and common decimal rationals. -/
inductive Number
  | int (value : Int)
  | rational (numerator : Int) (denominator : Nat)
  | decimal (mantissa : Int) (exponent : Int)
  deriving Repr, DecidableEq

inductive Atom
  | symbol (value : Symbol)
  | keyword (value : Keyword)
  | string (value : String)
  | bool (value : Bool)
  | number (value : Number)
  deriving Repr, DecidableEq

/-- Minimal s-expression structure to model ACL2 source. -/
inductive SExpr
  | nil
  | atom (a : Atom)
  | cons (car : SExpr) (cdr : SExpr)
  deriving Repr, DecidableEq

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

/-- Capture the ACL2 package context for events. -/
structure PackageState where
  current : String := "ACL2"
  openImports : Std.HashMap String (List String) := {}
  deriving Inhabited, Repr

/-- Top-level ACL2 event skeleton. Semantics filled in later. -/
inductive Event
  | inPackage (name : String)
  | includeBook (path : String) (dirs : List String := [])
  | defun (name : Symbol) (formals : List Symbol) (body : SExpr)
  | defthm (name : Symbol) (body : SExpr) (hints : Option SExpr := none)
  | defmacro (name : Symbol) (formals : List Symbol) (body : SExpr)
  | mutualRecursion (events : List Event)
  | local (event : Event)
  | inTheory (body : SExpr)
  | encapsulate (events : List Event)
  | makeEvent (body : SExpr)
  | defrec (name : Symbol)
  | skip (raw : SExpr)
  deriving Repr, Inhabited

namespace Event

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
      | some (SExpr.atom (.symbol name) :: params :: body) =>
          let fmls :=
            match params.toList? with
            | some lst =>
                lst.filterMap
                  (fun
                    | SExpr.atom (.symbol s) => some s
                    | _ => none)
            | none => []
          let bodyExpr := SExpr.ofList body
          .defun name fmls bodyExpr
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
      | some (SExpr.atom (.symbol name) :: params :: body) =>
          let fmls :=
            match params.toList? with
            | some lst =>
                lst.filterMap
                  (fun
                    | SExpr.atom (.symbol s) => some s
                    | _ => none)
            | none => []
          let bodyExpr := SExpr.ofList body
          .defmacro name fmls bodyExpr
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
      | some (SExpr.atom (.symbol name) :: _) => .defrec name
      | _ => .skip sexpr
  | _ => .skip sexpr

end Event

/-- Placeholder semantics: interpret events into a growing environment. -/
structure World where
  package : PackageState := {}
  defs : Std.HashMap Symbol SExpr := {}
  deriving Repr

instance : Inhabited World :=
  ⟨{ package := {}, defs := {} }⟩

namespace World

/-- Install an event, currently ignoring proof obligations. -/
def step (w : World) (event : Event) : World :=
  match event with
  | .inPackage name => { w with package := { w.package with current := name } }
  | .includeBook _ _ => w
  | .defun name _ body => { w with defs := w.defs.insert name body }
  | .defthm name body _ => { w with defs := w.defs.insert name body }
  | .defmacro name _ body => { w with defs := w.defs.insert name body }
  | .local e => step w e
  | .inTheory _ => w
  | .mutualRecursion evs => evs.foldl step w
  | .encapsulate evs => evs.foldl step w
  | .makeEvent _ => w
  | .defrec _ => w
  | .skip _ => w

/-- Replay a script of events. -/
def empty : World := { package := {}, defs := {} }

/-- Replay a script of events. -/
def replay (events : List Event) : World :=
  events.foldl step empty

end World

end ACL2
