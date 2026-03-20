import Lean
import Lean.Data.Json
import ACL2Lean.Parser

open Lean

namespace ACL2
namespace HintBridge

structure DynamicAction where
  kind : String
  source : String
  summary : String
  goal_target : Option String
  targets : List String
  detail : String
  deriving Inhabited, Repr, FromJson, ToJson

structure DynamicCheckpoint where
  kind : String
  label : String
  text : String
  deriving Inhabited, Repr, FromJson, ToJson

structure DynamicProgress where
  kind : String
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
  actions : List DynamicAction
  checkpoints : List DynamicCheckpoint
  progress : List DynamicProgress
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
    actions := []
    checkpoints := []
    progress := []
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

private def parseSingleSExpr? (text : String) : Option SExpr :=
  match ACL2.Parse.parseAll text with
  | .ok [expr] => some expr
  | _ => none

namespace DynamicAction

def payload? (action : DynamicAction) : Option String :=
  action.targets.head?

def theoryExpr? (action : DynamicAction) : Option TheoryExpr := do
  if action.kind != "in-theory" then
    none
  else
    let payload ← action.payload?
    let expr ← parseSingleSExpr? payload
    some (TheoryExpr.ofSExpr expr)

def theoryItems (action : DynamicAction) : List String :=
  match action.theoryExpr? with
  | some theoryExpr => theoryExpr.bulletItems
  | none => []

def theoryLines (action : DynamicAction) (indent : Nat := 0) : List String :=
  match action.theoryExpr? with
  | some theoryExpr => TheoryExpr.labeledLines "theory" theoryExpr indent
  | none => []

end DynamicAction

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

private def renderActionLines (action : DynamicAction) : List String :=
  let goalLine :=
    match action.goal_target with
    | some goal => [s!"    goal-target: {goal}"]
    | none => []
  let targetLine :=
    if action.targets.isEmpty then
      []
    else
      [s!"    targets: {String.intercalate ", " action.targets}"]
  [s!"  [{action.source}/{action.kind}] {action.summary}"] ++
    goalLine ++
    targetLine ++
    (action.theoryLines 4)

private def renderActions (actions : List DynamicAction) : List String :=
  if actions.isEmpty then
    []
  else
    "actions:" ::
      actions.foldr
        (fun action acc => renderActionLines action ++ acc)
        []

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
  let actions := renderActions artifact.actions
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
            [ s!"  [{checkpoint.kind}] {checkpoint.label}"
            , s!"    {checkpoint.text.replace "\n" "\n    "}"
            ] ++ acc)
          []
  let progress :=
    if artifact.progress.isEmpty then
      []
    else
      "progress:" ::
        artifact.progress.foldr
          (fun entry acc =>
            [ s!"  [{entry.kind}] {entry.label}"
            , s!"    {entry.text.replace "\n" "\n    "}"
            ] ++ acc)
          []
  header ++ loadNote ++ loadSteps ++ summary ++ summaryRules ++ hintEvents ++ splitterRules ++ warningKinds ++ summaryTime ++ proverSteps ++ actions ++ observations ++ warnings ++ inductions ++ progress ++ checkpoints

end HintBridge
end ACL2
