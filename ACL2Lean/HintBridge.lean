import Lean
import Lean.Data.Json

open Lean

namespace ACL2
namespace HintBridge

structure DynamicCheckpoint where
  label : String
  text : String
  deriving Inhabited, Repr, FromJson, ToJson

structure DynamicArtifact where
  book : String
  requested_theorem : String
  theorem_name : String
  status : String
  summary_form : String
  checkpoints : List DynamicCheckpoint
  observations : List String
  warnings : List String
  inductions : List String
  raw_excerpt : List String
  stderr : String
  exit_code : Nat
  deriving Inhabited, Repr, FromJson, ToJson

def parseArtifact (payload : String) : Except String DynamicArtifact := do
  let json ← Json.parse payload
  fromJson? json

def fetchArtifact (book theoremName : String) : IO (Except String DynamicArtifact) := do
  let cwd ← IO.currentDir
  let out ← IO.Process.output
    { cmd := "uv"
      args := #["run", "python", "scripts/acl2_hint_bridge.py", "--book", book, "--theorem", theoremName]
      cwd := some cwd
    } none
  if out.exitCode != 0 then
    pure <| .error s!"acl2_hint_bridge.py failed with exit code {out.exitCode}\n{out.stderr}"
  else
    pure <| parseArtifact out.stdout

def renderLines (artifact : DynamicArtifact) : List String :=
  let header :=
    [ s!"book: {artifact.book}"
    , s!"theorem: {artifact.theorem_name}"
    , s!"status: {artifact.status}"
    ]
  let summary :=
    if artifact.summary_form.isEmpty then
      []
    else
      [s!"summary: {artifact.summary_form}"]
  let observations :=
    if artifact.observations.isEmpty then
      []
    else
      "observations:" :: artifact.observations.map (fun line => s!"  {line}")
  let warnings :=
    if artifact.warnings.isEmpty then
      []
    else
      "warnings:" :: artifact.warnings.map (fun line => s!"  {line}")
  let inductions :=
    if artifact.inductions.isEmpty then
      []
    else
      "inductions:" :: artifact.inductions.map (fun line => s!"  {line}")
  let checkpoints :=
    if artifact.checkpoints.isEmpty then
      []
    else
      "checkpoints:" ::
        artifact.checkpoints.foldr
          (fun checkpoint acc =>
            [ s!"  {checkpoint.label}"
            , s!"    {checkpoint.text.replace "\n" "\n    "}"
            ] ++ acc)
          []
  header ++ summary ++ observations ++ warnings ++ inductions ++ checkpoints

end HintBridge
end ACL2
