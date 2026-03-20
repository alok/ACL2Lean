import ACL2Lean.Syntax
import ACL2Lean.Parser
import Std
import Init.System.IO

namespace ACL2

/-- Parse a raw ACL2 source file into events using the best-effort classifier. -/
def loadEventsFromFile (path : System.FilePath) : IO (Except String (List Event)) := do
  let contents ← IO.FS.readFile path
  pure <| do
    let raw ← Parse.parseAll contents
    pure (raw.map Event.classify)

/-- Count how often each event constructor appears. -/
def summarizeFile (path : System.FilePath) : IO (Except String (Std.HashMap String Nat)) := do
  let events ← loadEventsFromFile path
  pure <| events.map fun evs =>
    evs.foldl
      (fun acc ev =>
        let rec getTag : Event → String
          | .inPackage _ => "in-package"
          | .includeBook _ _ => "include-book"
          | .defun .. => "defun"
          | .defthm .. => "defthm"
          | .defmacro .. => "defmacro"
          | .local e => "local(" ++ getTag e ++ ")"
          | .inTheory _ => "in-theory"
          | .mutualRecursion _ => "mutual-recursion"
          | .encapsulate _ => "encapsulate"
          | .makeEvent _ => "make-event"
          | .defrec .. => "defrec"
          | .defconst .. => "defconst"
          | .defstobj .. => "defstobj"
          | .table .. => "table"
          | .skip _ => "skip"
        let tag := getTag ev
        let prev := (acc.get? tag).getD 0
        acc.insert tag (prev + 1))
      ({} : Std.HashMap String Nat)

private def theoremMatches (needle : String) (name : Symbol) : Bool :=
  name.normalizedName = needle.map Char.toLower

/--
Find a theorem together with the top-level `in-theory` events that precede it in
replay order.
-/
def findTheoremContext
    (events : List Event)
    (theoremName : String) : Except String (Symbol × TheoremInfo × List TheoryExpr) :=
  let rec go (theoriesRev : List TheoryExpr) : List Event → Except String (Symbol × TheoremInfo × List TheoryExpr)
    | [] => .error s!"No theorem named {theoremName}"
    | .inTheory expr :: rest => go (TheoryExpr.ofSExpr expr :: theoriesRev) rest
    | .defthm name info :: rest =>
        if theoremMatches theoremName name then
          .ok (name, info, theoriesRev.reverse)
        else
          go theoriesRev rest
    | _ :: rest => go theoriesRev rest
  go [] (Event.flattenList events)

/--
Load a source file, then find the named theorem together with its preceding
top-level `in-theory` context.
-/
def loadTheoremContextFromFile
    (path : System.FilePath)
    (theoremName : String) : IO (Except String (Symbol × TheoremInfo × List TheoryExpr)) := do
  match ← loadEventsFromFile path with
  | .error err => pure (.error err)
  | .ok events => pure (findTheoremContext events theoremName)

end ACL2
