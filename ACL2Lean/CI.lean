import Lean
import Lean.Data.Json

open Lean

namespace ACL2
namespace CI

structure RunInfo where
  databaseId : Nat
  headBranch : String
  headSha : String
  status : String
  conclusion : String
  workflowName : String
  url : String
  deriving Inhabited, Repr, FromJson, ToJson

def fetchRuns (branch? : Option String := none) (limit : Nat := 5) : IO (Except String (List RunInfo)) := do
  let mut args : Array String :=
    #["run", "list", "--limit", toString limit,
      "--json", "databaseId,headBranch,headSha,status,conclusion,workflowName,url"]
  if let some branch := branch? then
    args := args ++ #["--branch", branch]
  let out ← IO.Process.output { cmd := "gh", args := args, cwd := some (← IO.currentDir) } none
  if out.exitCode != 0 then
    pure <| .error s!"gh run list failed with exit code {out.exitCode}\n{out.stderr}"
  else
    let json ←
      match Json.parse out.stdout with
      | .ok json => pure json
      | .error err => pure <| Json.str err
    match json with
    | .str err => pure <| .error s!"failed to parse gh output as JSON: {err}"
    | _ =>
        pure <| do
          fromJson? json

def renderLines (runs : List RunInfo) : List String :=
  runs.map fun run =>
    s!"[{run.workflowName}] {run.headBranch} {run.headSha.take 7} status={run.status} conclusion={run.conclusion} url={run.url}"

end CI
end ACL2
