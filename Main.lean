import ACL2Lean

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
          for ev in evs do
            match ev with
            | .defun name formals _ _ body =>
                IO.println (ACL2.Translator.translateDefun name formals body)
                IO.println ""
            | .defthm name body hints =>
                IO.println (ACL2.Translator.translateDefthm name body hints)
                IO.println ""
            | _ => pure ()
  | _ => do
      IO.println "Usage:"
      IO.println "  acl2lean report"
      IO.println "  acl2lean eval \"(expr)\""
      IO.println "  acl2lean translate file.lisp"
