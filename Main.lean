import ACL2Lean

private def theoremMatches (needle : String) (name : ACL2.Symbol) : Bool :=
  name.normalizedName = needle.map Char.toLower

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
    IO.println "  hints:"
    for hint in hints do
      for line in ACL2.GoalHint.renderLines 4 hint do
        IO.println line
  let instructions := info.instructions
  if !instructions.isEmpty then
    IO.println "  instructions:"
    for instruction in instructions do
      for line in ACL2.ProofInstruction.renderLines 4 instruction do
        IO.println line
  let extraKeys := info.extraOptions.map (fun option => s!":{option.key}")
  if !extraKeys.isEmpty then
    IO.println s!"  other-options: {String.intercalate ", " extraKeys}"

private def printTheoryEvents (events : List ACL2.Event) : IO Unit := do
  let theoryExprs : List ACL2.TheoryExpr :=
    ACL2.Event.flattenList events |>.filterMap fun
      | .inTheory expr => some (ACL2.TheoryExpr.ofSExpr expr)
      | _ => none
  if !List.isEmpty theoryExprs then
    IO.println "theory-events"
    for theoryExpr in theoryExprs do
      for line in ACL2.TheoryExpr.renderLines 2 theoryExpr do
        IO.println line

private def printDynamicHints (artifact : ACL2.HintBridge.DynamicArtifact) : IO Unit := do
  for line in ACL2.HintBridge.renderLines artifact do
    IO.println line

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
          for ev in ACL2.Event.flattenList evs do
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
          for ev in ACL2.Event.flattenList evs do
            match ev with
            | .defthm name info =>
                printTheoremMetadata name info
            | _ => pure ()
  | ["metadata", path, theoremName] => do
      let events ← ACL2.loadEventsFromFile path
      match events with
      | .error e => IO.eprintln s!"Load error: {e}"
      | .ok evs =>
          let flat := ACL2.Event.flattenList evs
          match flat.find? (fun
            | .defthm name _ => theoremMatches theoremName name
            | _ => false) with
          | some ev =>
              match ev with
              | .defthm name info => printTheoremMetadata name info
              | _ => IO.eprintln s!"No theorem named {theoremName} in {path}"
          | _ => IO.eprintln s!"No theorem named {theoremName} in {path}"
  | ["hints", path, theoremName] => do
      match ← ACL2.HintBridge.fetchArtifact path theoremName with
      | .error err => IO.eprintln s!"Hint bridge error: {err}"
      | .ok artifact => printDynamicHints artifact
  | _ => do
      IO.println "Usage:"
      IO.println "  acl2lean report"
      IO.println "  acl2lean eval \"(expr)\""
      IO.println "  acl2lean hints file.lisp theorem-name"
      IO.println "  acl2lean metadata file.lisp [theorem]"
      IO.println "  acl2lean translate file.lisp"
