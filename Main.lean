import ACL2Lean

private def theoremMatches (needle : String) (name : ACL2.Symbol) : Bool :=
  name.normalizedName = needle.map Char.toLower

private partial def flattenEvents (event : ACL2.Event) : List ACL2.Event :=
  match event with
  | .local inner => flattenEvents inner
  | .mutualRecursion events => events.foldr (fun ev acc => flattenEvents ev ++ acc) []
  | .encapsulate events => events.foldr (fun ev acc => flattenEvents ev ++ acc) []
  | other => [other]

private def flattenEventList (events : List ACL2.Event) : List ACL2.Event :=
  events.foldr (fun ev acc => flattenEvents ev ++ acc) []

private def printTheoremMetadata (name : ACL2.Symbol) (info : ACL2.TheoremInfo) : IO Unit := do
  IO.println s!"theorem {repr name}"
  let ruleClasses := info.ruleClasses.map ACL2.RuleClass.summary
  if ruleClasses.isEmpty then
    IO.println "  rule-classes: none"
  else
    IO.println s!"  rule-classes: {String.intercalate ", " ruleClasses}"
  let hints := info.hintGoals
  if hints.isEmpty then
    IO.println "  hints: none"
  else
    for hint in hints do
      IO.println s!"  hint {hint.goal}"
      if let some useExpr := hint.findOption? "use" then
        IO.println s!"    use: {useExpr}"
      if let some theoryExpr := hint.inTheory? then
        IO.println s!"    in-theory: {theoryExpr.summary}"
      if let some inductExpr := hint.findOption? "induct" then
        IO.println s!"    induct: {inductExpr}"
      if let some expandExpr := hint.findOption? "expand" then
        IO.println s!"    expand: {expandExpr}"
      if let some dniExpr := hint.findOption? "do-not-induct" then
        IO.println s!"    do-not-induct: {dniExpr}"
  let extraKeys := info.extraOptions.map (fun option => s!":{option.key}")
  if !extraKeys.isEmpty then
    IO.println s!"  other-options: {String.intercalate ", " extraKeys}"

private def printTheoryEvents (events : List ACL2.Event) : IO Unit := do
  let theoryExprs : List ACL2.TheoryExpr :=
    (flattenEventList events).filterMap fun
      | .inTheory expr => some (ACL2.TheoryExpr.ofSExpr expr)
      | _ => none
  if !List.isEmpty theoryExprs then
    IO.println "theory-events"
    for theoryExpr in theoryExprs do
      IO.println s!"  {theoryExpr.summary}"

def main (args : List String) : IO Unit := do
  match args with
  | ["report"] => do
      IO.println "ACL2 to Lean 4 Bridge - Corpus Report"
      ACL2.reportSamples
  | ["eval", exprStr] => do
      match ACL2.Parse.parseSExpr exprStr.toList with
      | .error e => IO.eprintln s!"Parse error: {e}"
      | .ok (sexpr, _) =>
          let w := ACL2.World.empty
          match ACL2.Evaluator.eval w {} sexpr with
          | .error e => IO.eprintln s!"Eval error: {e}"
          | .ok res => IO.println s!"{repr res}"
  | ["eval-in", path, exprStr] => do
      let events ← ACL2.loadEventsFromFile path
      match events with
      | .error e => IO.eprintln s!"Load error: {e}"
      | .ok evs =>
          let w := ACL2.World.replay evs
          match ACL2.Parse.parseSExpr exprStr.toList with
          | .error e => IO.eprintln s!"Parse error: {e}"
          | .ok (sexpr, _) =>
              match ACL2.Evaluator.eval w {} sexpr with
              | .error e => IO.eprintln s!"Eval error: {e}"
              | .ok res => IO.println s!"{repr res}"
  | ["translate", path] => do
      let events ← ACL2.loadEventsFromFile path
      match events with
      | .error e => IO.eprintln s!"Load error: {e}"
      | .ok evs =>
          IO.println "import ACL2Lean.Logic"
          IO.println "import ACL2Lean.Tactics"
          IO.println "open ACL2 ACL2.Logic ACL2.Tactics"
          IO.println ""
          for ev in flattenEventList evs do
            match ev with
            | .defun name formals _ _ body =>
                IO.println (ACL2.Translator.translateDefun name formals body)
                IO.println ""
            | .defthm name info =>
                IO.println (ACL2.Translator.translateDefthm name info)
                IO.println ""
            | .inTheory expr =>
                IO.println s!"/- ACL2 in-theory: {(ACL2.TheoryExpr.ofSExpr expr).summary} -/"
                IO.println ""
            | _ => pure ()
  | ["metadata", path] => do
      let events ← ACL2.loadEventsFromFile path
      match events with
      | .error e => IO.eprintln s!"Load error: {e}"
      | .ok evs => do
          printTheoryEvents evs
          for ev in flattenEventList evs do
            match ev with
            | .defthm name info =>
                printTheoremMetadata name info
            | _ => pure ()
  | ["metadata", path, theoremName] => do
      let events ← ACL2.loadEventsFromFile path
      match events with
      | .error e => IO.eprintln s!"Load error: {e}"
      | .ok evs =>
          let flat := flattenEventList evs
          match flat.find? (fun
            | .defthm name _ => theoremMatches theoremName name
            | _ => false) with
          | some ev =>
              match ev with
              | .defthm name info => printTheoremMetadata name info
              | _ => IO.eprintln s!"No theorem named {theoremName} in {path}"
          | _ => IO.eprintln s!"No theorem named {theoremName} in {path}"
  | _ => do
      IO.println "Usage:"
      IO.println "  acl2lean report"
      IO.println "  acl2lean eval \"(expr)\""
      IO.println "  acl2lean metadata file.lisp [theorem]"
      IO.println "  acl2lean translate file.lisp"
