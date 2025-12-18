import ACL2Lean.Import
import Init.System.FilePath
import Std

open ACL2

namespace ACL2

/-- Non-exhaustive list of ACL2 sample files for syntax probing. -/
def sampleFiles : List System.FilePath :=
  [ "acl2_samples/2009-log2.lisp"
  , "acl2_samples/2009-tri-sq.lisp"
  , "acl2_samples/apply-model-apply.lisp"
  , "acl2_samples/apply-model-apply-prim.lisp"
  , "acl2_samples/die-hard-top.lisp"
  , "acl2_samples/die-hard-work.lisp"
  , "acl2_samples/bakery-programs.lisp"
  , "acl2_samples/bakery-inv-sufficient.lisp"
  , "acl2_samples/execloader-top.lisp"
  , "acl2_samples/gaussian-big-a-and-b.lsp"
  , "acl2_samples/gaussian-df-solver-v9.lisp"
  ]

/-- Render a hash map as a friendly string for debugging. -/
def prettyCounts (m : Std.HashMap String Nat) : String :=
  let entries := m.toList.map (fun (k, v) => s!"{k}: {v}")
  String.intercalate ", " entries

/-- Evaluate the parser+classifier against known ACL2 inputs. -/
def reportSamples : IO Unit := do
  for file in sampleFiles do
    let summary ← summarizeFile file
    match summary with
    | .error msg =>
        IO.println s!"[error] {file}: {msg}"
    | .ok counts =>
        IO.println s!"[ok] {file}: {prettyCounts counts}"

    -- Print skipped events for debugging
    let events ← loadEventsFromFile file
    match events with
    | .ok evs =>
        let skips := evs.filter fun
          | .skip _ => true
          | _ => false
        if ¬ skips.isEmpty then
          IO.println s!"  Skipped {skips.length} events in {file}:"
          for s in skips.take 5 do
            match s with
            | .skip raw => IO.println s!"    {repr raw}"
            | _ => pure ()
          if skips.length > 5 then
            IO.println "    ..."
    | _ => pure ()

end ACL2
