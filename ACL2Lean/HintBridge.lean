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
  resolved_book : String
  load_steps : List String
  load_note : String
  requested_theorem : String
  theorem_name : String
  status : String
  summary_form : String
  summary_rules : List String
  hint_events : List String
  splitter_rules : List String
  warning_kinds : List String
  summary_time : String
  prover_steps : Option Nat
  checkpoints : List DynamicCheckpoint
  observations : List String
  warnings : List String
  inductions : List String
  raw_excerpt : List String
  stderr : String
  exit_code : Nat
  deriving Inhabited, Repr, FromJson, ToJson

def unavailableArtifact (book theoremName reason : String) : DynamicArtifact :=
  { book := book
    resolved_book := book
    load_steps := [book]
    load_note := ""
    requested_theorem := theoremName
    theorem_name := theoremName
    status := "unavailable"
    summary_form := reason
    summary_rules := []
    hint_events := []
    splitter_rules := []
    warning_kinds := []
    summary_time := ""
    prover_steps := none
    checkpoints := []
    observations := []
    warnings := []
    inductions := []
    raw_excerpt := []
    stderr := reason
    exit_code := 255
  }

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

private def renderBlockSection (title : String) (items : List String) : List String :=
  if items.isEmpty then
    []
  else
    title ::
      items.foldr
        (fun item acc => s!"  {item.replace "\n" "\n  "}" :: acc)
        []

private def renderSimpleSection (title : String) (items : List String) : List String :=
  if items.isEmpty then
    []
  else
    title :: items.map (fun item => s!"  {item}")

def renderLines (artifact : DynamicArtifact) : List String :=
  let header :=
    [ s!"book: {artifact.book}"
    , if artifact.resolved_book = artifact.book then
        s!"resolved-book: {artifact.resolved_book}"
      else
        s!"resolved-book: {artifact.resolved_book} (requested {artifact.book})"
    , s!"theorem: {artifact.theorem_name}"
    , s!"status: {artifact.status}"
    ]
  let loadNote :=
    if artifact.load_note.isEmpty then
      []
    else
      [s!"load-note: {artifact.load_note}"]
  let loadSteps := renderSimpleSection "load-steps:" artifact.load_steps
  let summary :=
    if artifact.summary_form.isEmpty then
      []
    else
      [s!"summary: {artifact.summary_form}"]
  let summaryRules := renderSimpleSection "summary-rules:" artifact.summary_rules
  let hintEvents := renderSimpleSection "hint-events:" artifact.hint_events
  let splitterRules := renderSimpleSection "splitter-rules:" artifact.splitter_rules
  let warningKinds :=
    if artifact.warning_kinds.isEmpty then
      []
    else
      [s!"warning-kinds: {String.intercalate ", " artifact.warning_kinds}"]
  let summaryTime :=
    if artifact.summary_time.isEmpty then
      []
    else
      [s!"summary-time: {artifact.summary_time}"]
  let proverSteps :=
    match artifact.prover_steps with
    | some steps => [s!"prover-steps: {steps}"]
    | none => []
  let observations := renderBlockSection "observations:" artifact.observations
  let warnings := renderBlockSection "warnings:" artifact.warnings
  let inductions := renderBlockSection "inductions:" artifact.inductions
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
  header ++ loadNote ++ loadSteps ++ summary ++ summaryRules ++ hintEvents ++ splitterRules ++ warningKinds ++ summaryTime ++ proverSteps ++ observations ++ warnings ++ inductions ++ checkpoints

end HintBridge
end ACL2
