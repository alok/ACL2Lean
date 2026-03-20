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

structure DisableRulePayload where
  rune : String
  goalTarget : Option String := none
  deriving Inhabited, Repr

structure DisableDefinitionPayload where
  definitionRune : String
  thmName : String
  freeVar : Option String := none
  hypothesis : Option String := none
  triggerTerm : Option String := none
  deriving Inhabited, Repr

structure FreeVariableBindingPayload where
  freeVar : String
  hypothesis : String
  triggerTerm : Option String := none
  deriving Inhabited, Repr

structure RewriteOverlapPayload where
  generatedTheorem : String
  existingRule : String
  deriving Inhabited, Repr

structure UseInstanceBinding where
  name : String
  value : SExpr
  deriving Inhabited, Repr

inductive UseTarget
  | ref (expr : SExpr)
  | theorem (expr : SExpr)
  deriving Inhabited, Repr

structure UsePayload where
  target : UseTarget
  bindings : List UseInstanceBinding := []
  deriving Inhabited, Repr

structure SplitGoalPayload where
  splitterName : String
  payloadText : String
  goalTarget : Option String := none
  deriving Inhabited, Repr

structure TypedTermPayload where
  term : SExpr
  goalTarget : Option String := none
  deriving Inhabited, Repr

structure SummaryRule where
  kind : String
  target? : Option SExpr := none
  extras : List SExpr := []
  deriving Inhabited, Repr

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

@[inline] private def renderIndent (indent : Nat) : String :=
  String.ofList (List.replicate indent ' ')

private def renderLabeledItems (label : String) (items : List String) (indent : Nat := 0) : List String :=
  match items with
  | [] => []
  | [item] => [s!"{renderIndent indent}{label}: {item}"]
  | _ =>
      s!"{renderIndent indent}{label}:" ::
        items.map (fun item => s!"{renderIndent (indent + 2)}- {item}")

namespace SummaryRule

def ofSExpr? : SExpr → Option SummaryRule
  | .atom (.keyword key) => some { kind := key.map Char.toLower }
  | expr => do
      let items ← expr.toList?
      match items with
      | .atom (.keyword key) :: rest =>
          match rest with
          | [] => some { kind := key.map Char.toLower }
          | target :: extras =>
              some { kind := key.map Char.toLower, target? := some target, extras }
      | _ => none

def ofString? (text : String) : Option SummaryRule := do
  let expr ← parseSingleSExpr? text
  ofSExpr? expr

def summary (rule : SummaryRule) : String :=
  let extraSummary := String.intercalate "; " (rule.extras.map toString)
  match rule.target?, extraSummary.isEmpty with
  | none, true => rule.kind
  | none, false => s!"{rule.kind} with {extraSummary}"
  | some target, true => s!"{rule.kind} {target}"
  | some target, false => s!"{rule.kind} {target} with {extraSummary}"

def structuredLines (rule : SummaryRule) (indent : Nat := 0) : List String :=
  renderLabeledItems "kind" [rule.kind] indent ++
    (match rule.target? with
      | some target => renderLabeledItems "target" [toString target] indent
      | none => []) ++
    renderLabeledItems "extra" (rule.extras.map toString) indent

end SummaryRule

private def payloadExprsFromPayload (payload : String) : List SExpr :=
  let trimmed := payload.trimAscii.toString
  if trimmed.isEmpty then
    []
  else
    match parseSingleSExpr? payload with
    | none => []
    | some expr =>
        if trimmed.startsWith "((" then
          match expr.toList? with
          | some exprs => exprs
          | none => [expr]
        else
          [expr]

namespace UseInstanceBinding

def ofSExpr? : SExpr → Option UseInstanceBinding
  | expr => do
      let parts ← expr.toList?
      match parts with
      | [lhs, rhs] =>
          let varName :=
            match lhs with
            | .atom (.symbol sym) => sym.name
            | .atom (.keyword key) => s!":{key}"
            | _ => toString lhs
          some { name := varName, value := rhs }
      | _ => none

def summary (binding : UseInstanceBinding) : String :=
  s!"{binding.name} := {binding.value}"

end UseInstanceBinding

namespace UseTarget

def ofSExpr (expr : SExpr) : UseTarget :=
  match expr.toList? with
  | some (.atom (.keyword key) :: [body]) =>
      if key = "theorem" then
        .theorem body
      else
        .ref expr
  | _ => .ref expr

def summary : UseTarget → String
  | .ref expr => toString expr
  | .theorem expr => toString expr

def structuredLine? : UseTarget → Option String
  | .ref _ => none
  | .theorem expr => some s!"use-theorem: {expr}"

def instanceSummary : UseTarget → String
  | .ref expr => toString expr
  | .theorem expr => s!"theorem {expr}"

end UseTarget

namespace UsePayload

def ofSExpr (expr : SExpr) : UsePayload :=
  match expr.toList? with
  | some (.atom (.keyword key) :: target :: rest) =>
      if key = "instance" then
        { target := UseTarget.ofSExpr target
          bindings := rest.filterMap UseInstanceBinding.ofSExpr? }
      else
        { target := UseTarget.ofSExpr expr }
  | _ => { target := UseTarget.ofSExpr expr }

def structuredLines (payload : UsePayload) (indent : Nat := 0) : List String :=
  let targetLines :=
    match payload.bindings with
    | [] =>
        match payload.target.structuredLine? with
        | some line => [s!"{renderIndent indent}{line}"]
        | none => []
    | _ => renderLabeledItems "use-instance" [payload.target.instanceSummary] indent
  let bindingLines :=
    renderLabeledItems "binding" (payload.bindings.map UseInstanceBinding.summary) indent
  targetLines ++ bindingLines

end UsePayload

namespace SplitGoalPayload

def payloadExprs (payload : SplitGoalPayload) : List SExpr :=
  payloadExprsFromPayload payload.payloadText

def payloadItems (payload : SplitGoalPayload) : List String :=
  match payload.payloadExprs.map toString with
  | [] => [payload.payloadText]
  | items => items

def summary (payload : SplitGoalPayload) : String :=
  match payload.payloadItems with
  | [] => payload.splitterName
  | items => s!"{payload.splitterName} with {String.intercalate ", " items}"

def structuredLines (payload : SplitGoalPayload) (indent : Nat := 0) : List String :=
  renderLabeledItems "splitter" [payload.splitterName] indent ++
    renderLabeledItems "split-term" payload.payloadItems indent

end SplitGoalPayload

namespace TypedTermPayload

def structuredLines (payload : TypedTermPayload) (indent : Nat := 0) : List String :=
  renderLabeledItems "typed-term" [toString payload.term] indent

end TypedTermPayload

namespace DynamicAction

def nonGoalTargets (action : DynamicAction) : List String :=
  match action.goal_target with
  | some goal => action.targets.filter (· != goal)
  | none => action.targets

def payload? (action : DynamicAction) : Option String :=
  action.nonGoalTargets.head?

def payloadExpr? (action : DynamicAction) : Option SExpr := do
  let payload ← action.payload?
  parseSingleSExpr? payload

def payloadExprs (action : DynamicAction) : List SExpr :=
  match action.payload? with
  | some payload => payloadExprsFromPayload payload
  | none => []

def usePayload? (action : DynamicAction) : Option UsePayload := do
  if action.kind != "use" then
    none
  else
    let expr ← action.payloadExpr?
    some (UsePayload.ofSExpr expr)

def useLines (action : DynamicAction) (indent : Nat := 0) : List String :=
  match action.usePayload? with
  | some payload => payload.structuredLines indent
  | none => []

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

def clauseProcessorExpr? (action : DynamicAction) : Option SExpr := do
  if action.kind != "clause-processor" then
    none
  else
    action.payloadExpr?

def clauseProcessorItems (action : DynamicAction) : List String :=
  match action.clauseProcessorExpr? with
  | some expr => [toString expr]
  | none => []

def otfFlagExpr? (action : DynamicAction) : Option SExpr := do
  if action.kind != "otf-flg" then
    none
  else
    action.payloadExpr?

def expandExprs (action : DynamicAction) : List SExpr :=
  if action.kind = "expand" then
    action.payloadExprs
  else
    []

def expandItems (action : DynamicAction) : List String :=
  action.expandExprs.map toString

def casesExprs (action : DynamicAction) : List SExpr :=
  if action.kind = "cases" then
    action.payloadExprs
  else
    []

def casesItems (action : DynamicAction) : List String :=
  action.casesExprs.map toString

def doNotInductExpr? (action : DynamicAction) : Option SExpr := do
  if action.kind != "do-not-induct" then
    none
  else
    action.payloadExpr?

def inductTermExpr? (action : DynamicAction) : Option SExpr := do
  if action.kind != "induct" then
    none
  else
    let term ← action.nonGoalTargets.head?
    parseSingleSExpr? term

def inductTermItems (action : DynamicAction) : List String :=
  match action.inductTermExpr? with
  | some expr => [toString expr]
  | none => []

def inductionRule? (action : DynamicAction) : Option String :=
  if action.kind != "induct" then
    none
  else
    match action.nonGoalTargets.drop 1 with
    | rule :: _ => some rule
    | [] => none

def disableRulePayload? (action : DynamicAction) : Option DisableRulePayload := do
  if action.kind != "disable-rule" then
    none
  else
    let rune <- action.nonGoalTargets.head?
    some { rune, goalTarget := action.goal_target }

def disableDefinitionPayload? (action : DynamicAction) : Option DisableDefinitionPayload := do
  if action.kind != "disable-definition" then
    none
  else
    let definitionRune :: thmName :: rest := action.targets | none
    let base : DisableDefinitionPayload := { definitionRune := definitionRune, thmName := thmName }
    match rest with
    | freeVar :: hypothesis :: _ =>
        some { base with freeVar := some freeVar, hypothesis := some hypothesis }
    | single :: _ =>
      if single.trimAscii.toString.startsWith "(" then
        some { base with triggerTerm := some single }
      else
        some { base with freeVar := some single }
    | [] => some base

def freeVariableBindingPayload? (action : DynamicAction) : Option FreeVariableBindingPayload := do
  if action.kind != "bind-free-variable" then
    none
  else
    let freeVar :: hypothesis :: rest := action.targets | none
    match rest with
    | triggerTerm :: _ => some { freeVar, hypothesis, triggerTerm := some triggerTerm }
    | [] => some { freeVar, hypothesis }

def rewriteOverlapPayload? (action : DynamicAction) : Option RewriteOverlapPayload := do
  if action.kind != "watch-rune-overlap" then
    none
  else
    let generatedTheorem :: existingRule :: _ := action.targets | none
    some { generatedTheorem, existingRule }

def splitGoalPayload? (action : DynamicAction) : Option SplitGoalPayload := do
  if action.kind != "split-goal" then
    none
  else
    let splitterName :: payloadText :: _ := action.targets | none
    some { splitterName, payloadText, goalTarget := action.goal_target }

def splitGoalItems (action : DynamicAction) : List String :=
  match action.splitGoalPayload? with
  | some payload => payload.payloadItems
  | none => []

def typedTermPayload? (action : DynamicAction) : Option TypedTermPayload := do
  if action.kind != "typed-term" then
    none
  else
    let termText ← action.nonGoalTargets.head?
    let term ← parseSingleSExpr? termText
    some { term, goalTarget := action.goal_target }

def typedTermItems (action : DynamicAction) : List String :=
  match action.typedTermPayload? with
  | some payload => [toString payload.term]
  | none => []

def structuredLines (action : DynamicAction) (indent : Nat := 0) : List String :=
  match action.kind with
  | "use" => action.useLines indent
  | "in-theory" => action.theoryLines indent
  | "split-goal" =>
      match action.splitGoalPayload? with
      | some payload => payload.structuredLines indent
      | none => []
  | "clause-processor" => renderLabeledItems "clause-processor" action.clauseProcessorItems indent
  | "otf-flg" =>
      match action.otfFlagExpr? with
      | some expr => renderLabeledItems "otf-flg" [toString expr] indent
      | none => []
  | "expand" => renderLabeledItems "expand" action.expandItems indent
  | "cases" => renderLabeledItems "cases" action.casesItems indent
  | "do-not-induct" =>
      match action.doNotInductExpr? with
      | some expr => renderLabeledItems "do-not-induct" [toString expr] indent
      | none => []
  | "induct" =>
      renderLabeledItems "induct-term" action.inductTermItems indent ++
        (match action.inductionRule? with
          | some rule => renderLabeledItems "induction-rule" [rule] indent
          | none => [])
  | "disable-rule" =>
      match action.disableRulePayload? with
      | some payload => renderLabeledItems "disable-rule" [payload.rune] indent
      | none => []
  | "disable-definition" =>
      match action.disableDefinitionPayload? with
      | some payload =>
          renderLabeledItems "disable-definition" [payload.definitionRune] indent ++
            renderLabeledItems "theorem" [payload.thmName] indent ++
            (match payload.freeVar with
              | some freeVar => renderLabeledItems "variable" [freeVar] indent
              | none => []) ++
            (match payload.hypothesis with
              | some hypothesis => renderLabeledItems "hypothesis" [hypothesis] indent
              | none => []) ++
            (match payload.triggerTerm with
              | some triggerTerm => renderLabeledItems "trigger-term" [triggerTerm] indent
              | none => [])
      | none => []
  | "bind-free-variable" =>
      match action.freeVariableBindingPayload? with
      | some payload =>
          renderLabeledItems "variable" [payload.freeVar] indent ++
            renderLabeledItems "hypothesis" [payload.hypothesis] indent ++
            (match payload.triggerTerm with
              | some triggerTerm => renderLabeledItems "trigger-term" [triggerTerm] indent
              | none => [])
      | none => []
  | "watch-rune-overlap" =>
      match action.rewriteOverlapPayload? with
      | some payload =>
          renderLabeledItems "generated-theorem" [payload.generatedTheorem] indent ++
            renderLabeledItems "existing-rule" [payload.existingRule] indent
      | none => []
  | "typed-term" =>
      match action.typedTermPayload? with
      | some payload => payload.structuredLines indent
      | none => []
  | _ => []

end DynamicAction

private def dedupStrings (items : List String) : List String :=
  items.foldl
    (fun acc item =>
      if item.isEmpty || acc.contains item then
        acc
      else
        acc ++ [item])
    []

private def goalSuffix (goalTarget : Option String) : String :=
  match goalTarget with
  | some goal => s!" @ {goal}"
  | none => ""

private def formatReplayEntry (source : String) (goalTarget : Option String) (detail : String) : String :=
  s!"{source}{goalSuffix goalTarget}: {detail}"

structure DynamicReplayState where
  theoryTimeline : List String := []
  useTimeline : List String := []
  splitTimeline : List String := []
  clauseProcessors : List String := []
  expandTimeline : List String := []
  caseTimeline : List String := []
  typedTerms : List String := []
  inductionTerm : Option String := none
  inductionRule : Option String := none
  inductionGoal : Option String := none
  doNotInduct : Option String := none
  doNotInductGoal : Option String := none
  otfFlag : Option String := none
  deriving Inhabited, Repr

namespace DynamicReplayState

def isEmpty (state : DynamicReplayState) : Bool :=
  state.theoryTimeline.isEmpty &&
    state.useTimeline.isEmpty &&
    state.splitTimeline.isEmpty &&
    state.clauseProcessors.isEmpty &&
    state.expandTimeline.isEmpty &&
    state.caseTimeline.isEmpty &&
    state.typedTerms.isEmpty &&
    state.inductionTerm.isNone &&
    state.inductionRule.isNone &&
    state.doNotInduct.isNone &&
    state.otfFlag.isNone

def inductionSummary? (state : DynamicReplayState) : Option String :=
  let base :=
    match state.inductionTerm, state.inductionRule with
    | some term, some rule => some s!"{term} using {rule}"
    | some term, none => some term
    | none, some rule => some s!"rule {rule}"
    | none, none => none
  match base with
  | some summary =>
      match state.inductionGoal with
      | some goal => some s!"{summary} @ {goal}"
      | none => some summary
  | none => none

def doNotInductSummary? (state : DynamicReplayState) : Option String :=
  match state.doNotInduct with
  | some value =>
      match state.doNotInductGoal with
      | some goal => some s!"{value} @ {goal}"
      | none => some value
  | none => none

def noteLines (state : DynamicReplayState) : List String :=
  let summaryLines :=
    [ inductionSummary? state |>.map (fun summary => s!"Replay induction: {summary}")
    , doNotInductSummary? state |>.map (fun summary => s!"Replay do-not-induct: {summary}")
    , state.otfFlag.map (fun value => s!"Replay otf-flg: {value}")
    ].filterMap id
  summaryLines ++
    (state.theoryTimeline.map (fun line => s!"Replay theory: {line}")) ++
    (state.useTimeline.map (fun line => s!"Replay use: {line}")) ++
    (state.splitTimeline.map (fun line => s!"Replay split: {line}")) ++
    (state.clauseProcessors.map (fun line => s!"Replay clause-processor: {line}")) ++
    (state.expandTimeline.map (fun line => s!"Replay expand: {line}")) ++
    (state.caseTimeline.map (fun line => s!"Replay cases: {line}")) ++
    (state.typedTerms.map (fun line => s!"Replay typed-term: {line}"))

end DynamicReplayState

namespace DynamicArtifact

def summaryRulePayloads (artifact : DynamicArtifact) : List SummaryRule :=
  artifact.summary_rules.filterMap SummaryRule.ofString?

def summaryRuleItems (artifact : DynamicArtifact) : List String :=
  artifact.summary_rules.map fun ruleText =>
    match SummaryRule.ofString? ruleText with
    | some rule => rule.summary
    | none => ruleText

def replayState (artifact : DynamicArtifact) : DynamicReplayState :=
  let state : DynamicReplayState :=
    artifact.actions.foldl
      (fun (state : DynamicReplayState) action =>
        match action.kind with
        | "in-theory" =>
            let detail :=
              match action.theoryItems with
              | [] => action.summary
              | items => String.intercalate "; " items
            ({ state with
                theoryTimeline := state.theoryTimeline ++ [formatReplayEntry action.source action.goal_target detail] } : DynamicReplayState)
        | "disable-rule" =>
            match action.disableRulePayload? with
            | some payload =>
                ({ state with
                    theoryTimeline :=
                      state.theoryTimeline ++
                        [formatReplayEntry action.source payload.goalTarget s!"disable {payload.rune}"] } : DynamicReplayState)
            | none => state
        | "disable-definition" =>
            match action.disableDefinitionPayload? with
            | some payload =>
                ({ state with
                    theoryTimeline :=
                      state.theoryTimeline ++
                        [formatReplayEntry action.source action.goal_target
                          s!"disable {payload.definitionRune} for {payload.thmName}"] } : DynamicReplayState)
            | none => state
        | "use" =>
            let detail :=
              match action.usePayload? with
              | some payload =>
                  match payload.bindings with
                  | [] => s!"use {payload.target.summary}"
                  | bindings =>
                      let bindingSummary := String.intercalate ", " (bindings.map UseInstanceBinding.summary)
                      s!"use {payload.target.instanceSummary} with {bindingSummary}"
              | none => action.summary
            ({ state with
                useTimeline := state.useTimeline ++ [formatReplayEntry action.source action.goal_target detail] } : DynamicReplayState)
        | "split-goal" =>
            let detail :=
              match action.splitGoalPayload? with
              | some payload => payload.summary
              | none => action.summary
            ({ state with
                splitTimeline := state.splitTimeline ++ [formatReplayEntry action.source action.goal_target detail] } : DynamicReplayState)
        | "clause-processor" =>
            match action.clauseProcessorItems with
            | [] => state
            | items =>
                ({ state with
                    clauseProcessors :=
                      state.clauseProcessors ++
                        items.map (fun item => formatReplayEntry action.source action.goal_target item) } : DynamicReplayState)
        | "expand" =>
            match action.expandItems with
            | [] => state
            | items =>
                ({ state with
                    expandTimeline :=
                      state.expandTimeline ++
                        items.map (fun item => formatReplayEntry action.source action.goal_target item) } : DynamicReplayState)
        | "cases" =>
            match action.casesItems with
            | [] => state
            | items =>
                ({ state with
                    caseTimeline :=
                      state.caseTimeline ++
                        items.map (fun item => formatReplayEntry action.source action.goal_target item) } : DynamicReplayState)
        | "typed-term" =>
            let terms := action.typedTermItems
            if terms.isEmpty then
              state
            else
              ({ state with
                  typedTerms :=
                    state.typedTerms ++
                      terms.map (fun term => formatReplayEntry action.source action.goal_target term) } : DynamicReplayState)
        | "induct" =>
            ({ state with
                inductionTerm :=
                  match action.inductTermItems with
                  | item :: _ => some item
                  | [] => state.inductionTerm
                inductionRule :=
                  match action.inductionRule? with
                  | some rule => some rule
                  | none => state.inductionRule
                inductionGoal :=
                  match action.goal_target with
                  | some goal => some goal
                  | none => state.inductionGoal } : DynamicReplayState)
        | "do-not-induct" =>
            match action.doNotInductExpr? with
            | some expr =>
                ({ state with
                    doNotInduct := some (toString expr)
                    doNotInductGoal :=
                      match action.goal_target with
                      | some goal => some goal
                      | none => state.doNotInductGoal } : DynamicReplayState)
            | none => state
        | "otf-flg" =>
            match action.otfFlagExpr? with
            | some expr => ({ state with otfFlag := some (toString expr) } : DynamicReplayState)
            | none => state
        | _ => state)
      ({} : DynamicReplayState)
  ({ state with
      theoryTimeline := dedupStrings state.theoryTimeline
      useTimeline := dedupStrings state.useTimeline
      splitTimeline := dedupStrings state.splitTimeline
      clauseProcessors := dedupStrings state.clauseProcessors
      expandTimeline := dedupStrings state.expandTimeline
      caseTimeline := dedupStrings state.caseTimeline
      typedTerms := dedupStrings state.typedTerms } : DynamicReplayState)

end DynamicArtifact

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

private def renderReplayState (state : DynamicReplayState) : List String :=
  if state.isEmpty then
    []
  else
    let induction :=
      match state.inductionSummary? with
      | some summary => [s!"  selected-induction: {summary}"]
      | none => []
    let doNotInduct :=
      match state.doNotInductSummary? with
      | some summary => [s!"  do-not-induct: {summary}"]
      | none => []
    let otfFlag :=
      match state.otfFlag with
      | some value => [s!"  otf-flg: {value}"]
      | none => []
    let theory := renderLabeledItems "theory-timeline" state.theoryTimeline 2
    let uses := renderLabeledItems "use-timeline" state.useTimeline 2
    let splits := renderLabeledItems "split-timeline" state.splitTimeline 2
    let clauseProcessors := renderLabeledItems "clause-processors" state.clauseProcessors 2
    let expands := renderLabeledItems "expand-timeline" state.expandTimeline 2
    let cases := renderLabeledItems "case-timeline" state.caseTimeline 2
    let typedTerms := renderLabeledItems "typed-terms" state.typedTerms 2
    "replay-state:" ::
      induction ++ doNotInduct ++ otfFlag ++ theory ++ uses ++ splits ++ clauseProcessors ++ expands ++ cases ++ typedTerms

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
    (action.structuredLines 4)

private def renderActions (actions : List DynamicAction) : List String :=
  if actions.isEmpty then
    []
  else
    "actions:" ::
      actions.foldr
        (fun action acc => renderActionLines action ++ acc)
        []

def renderLines (artifact : DynamicArtifact) : List String :=
  let replayState := artifact.replayState
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
  let summaryRules := renderSimpleSection "summary-rules:" artifact.summaryRuleItems
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
  let replay := renderReplayState replayState
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
  header ++ loadNote ++ loadSteps ++ summary ++ summaryRules ++ hintEvents ++ splitterRules ++ warningKinds ++ summaryTime ++ proverSteps ++ actions ++ replay ++ observations ++ warnings ++ inductions ++ progress ++ checkpoints

private def dynamicExpandPayloadParses : Bool :=
  let action : DynamicAction :=
    { kind := "expand"
      source := "transcript-hint"
      summary := "expand ((EV$ X A)) in Goal"
      goal_target := some "Goal"
      targets := ["((EV$ X A))", "Goal"]
      detail := "Goal: (:EXPAND ((EV$ X A)))"
    }
  action.expandItems.length == 1 &&
    (action.expandItems.headD "").contains "ev$" &&
    (action.structuredLines 2).any (fun line => line.contains "expand:" && line.contains "ev$")

#guard dynamicExpandPayloadParses

private def dynamicUsePayloadParses : Bool :=
  let theoremAction : DynamicAction :=
    { kind := "use"
      source := "hint-event"
      summary := "use NOTE-3"
      goal_target := none
      targets := ["NOTE-3"]
      detail := "(:USE NOTE-3)"
    }
  let instanceAction : DynamicAction :=
    { kind := "use"
      source := "transcript-hint"
      summary := "use (:INSTANCE NOTE-3 (P P) (Q Q)) in Goal"
      goal_target := some "Goal"
      targets := ["(:INSTANCE NOTE-3 (P P) (Q Q))", "Goal"]
      detail := "Goal: (:USE ((:INSTANCE NOTE-3 (P P) (Q Q))))"
    }
  let theoremHintAction : DynamicAction :=
    { kind := "use"
      source := "hint-event"
      summary := "use (:THEOREM (IMPLIES (P X) (Q X)))"
      goal_target := none
      targets := ["(:THEOREM (IMPLIES (P X) (Q X)))"]
      detail := "(:USE (:THEOREM (IMPLIES (P X) (Q X))))"
    }
  theoremAction.useLines 2 = [] &&
    (match instanceAction.usePayload? with
      | some payload =>
          payload.bindings.map UseInstanceBinding.summary = ["p := p", "q := q"]
      | none => false) &&
    (instanceAction.structuredLines 2).any (fun line =>
      line.contains "use-instance:" && line.contains "note-3") &&
    (instanceAction.structuredLines 2).any (fun line =>
      line.contains "binding:") &&
    (instanceAction.structuredLines 2).any (fun line =>
      line.contains "p := p") &&
    (instanceAction.structuredLines 2).any (fun line =>
      line.contains "q := q") &&
    (match theoremHintAction.usePayload? with
      | some payload =>
          match payload.target with
          | .theorem expr => (toString expr).contains "(implies (p x) (q x))"
          | _ => false
      | none => false) &&
    (theoremHintAction.structuredLines 2).any (fun line =>
      line.contains "use-theorem:" && line.contains "(implies (p x) (q x))")

#guard dynamicUsePayloadParses

private def dynamicClauseProcessorPayloadParses : Bool :=
  let action : DynamicAction :=
    { kind := "clause-processor"
      source := "hint-event"
      summary := "clause-processor FLAG::FLAG-IS-CP"
      goal_target := none
      targets := ["FLAG::FLAG-IS-CP"]
      detail := "(:CLAUSE-PROCESSOR FLAG::FLAG-IS-CP)"
    }
  (match action.clauseProcessorExpr? with
    | some expr => (toString expr).toLower.contains "flag-is-cp"
    | none => false) &&
    (action.structuredLines 2).any (fun line =>
      line.toLower.contains "clause-processor:" && line.toLower.contains "flag-is-cp")

#guard dynamicClauseProcessorPayloadParses

private def dynamicOtfFlagPayloadParses : Bool :=
  let action : DynamicAction :=
    { kind := "otf-flg"
      source := "transcript-option"
      summary := "set otf-flg T"
      goal_target := none
      targets := ["T"]
      detail := "(:OTF-FLG T)"
    }
  (match action.otfFlagExpr? with
    | some expr => toString expr = "T"
    | none => false) &&
    (action.structuredLines 2).any (fun line => line.contains "otf-flg:" && line.contains "T")

#guard dynamicOtfFlagPayloadParses

private def dynamicDoNotInductPayloadParses : Bool :=
  let action : DynamicAction :=
    { kind := "do-not-induct"
      source := "transcript-hint"
      summary := "do-not-induct T in Goal"
      goal_target := some "Goal"
      targets := ["T", "Goal"]
      detail := "Goal: (:DO-NOT-INDUCT T)"
    }
  (match action.doNotInductExpr? with
    | some expr => toString expr = "T"
    | none => false) &&
    (action.structuredLines 2).any (fun line => line.contains "do-not-induct:" && line.contains "T")

#guard dynamicDoNotInductPayloadParses

private def dynamicSplitGoalPayloadParses : Bool :=
  let action : DynamicAction :=
    { kind := "split-goal"
      source := "splitter"
      summary := "split using if-intro with ((:DEFINITION GCD-PROG!)) in Goal''"
      goal_target := some "Goal''"
      targets := ["if-intro", "((:DEFINITION GCD-PROG!))", "Goal''"]
      detail := "if-intro: ((:DEFINITION GCD-PROG!))"
    }
  (match action.splitGoalPayload? with
    | some payload =>
        payload.splitterName = "if-intro" &&
          payload.goalTarget = some "Goal''" &&
          payload.payloadItems = ["(:definition gcd-prog!)"]
    | none => false) &&
    (action.structuredLines 2).any (fun line =>
      line.contains "splitter:" && line.contains "if-intro") &&
    (action.structuredLines 2).any (fun line =>
      line.contains "split-term:" && line.contains "(:definition gcd-prog!)")

#guard dynamicSplitGoalPayloadParses

private def dynamicTypedTermPayloadParses : Bool :=
  let action : DynamicAction :=
    { kind := "typed-term"
      source := "observation"
      summary := "focus on typed term (CLOG2 N)"
      goal_target := none
      targets := ["(CLOG2 N)"]
      detail := "ACL2 Observation ..."
    }
  (match action.typedTermPayload? with
    | some payload => toString payload.term = "(clog2 n)"
    | none => false) &&
    (action.structuredLines 2).any (fun line =>
      line.contains "typed-term:" && line.contains "(clog2 n)")

#guard dynamicTypedTermPayloadParses

private def dynamicInductPayloadParses : Bool :=
  let action : DynamicAction :=
    { kind := "induct"
      source := "induction"
      summary := "induct on (MAKE-PROG1-INDUCTION I N) using rule MAKE-PROG1-INDUCTION"
      goal_target := none
      targets := ["(MAKE-PROG1-INDUCTION I N)", "MAKE-PROG1-INDUCTION"]
      detail := "We will induct according to a scheme suggested by (MAKE-PROG1-INDUCTION I N)."
    }
  (match action.inductTermExpr? with
    | some expr => (toString expr).toLower.contains "make-prog1-induction"
    | none => false) &&
    action.inductionRule? = some "MAKE-PROG1-INDUCTION" &&
    (action.structuredLines 2).any (fun line =>
      line.toLower.contains "induct-term:" && line.toLower.contains "make-prog1-induction") &&
    (action.structuredLines 2).any (fun line =>
      line.contains "induction-rule:" && line.contains "MAKE-PROG1-INDUCTION")

#guard dynamicInductPayloadParses

private def dynamicDisableRulePayloadParses : Bool :=
  let action : DynamicAction :=
    { kind := "disable-rule"
      source := "warning"
      summary := "disable (:REWRITE NBR-CALLS-FLOG2-UPPER-BOUND) in Goal"
      goal_target := some "Goal"
      targets := ["(:REWRITE NBR-CALLS-FLOG2-UPPER-BOUND)", "Goal"]
      detail := "ACL2 Warning [Use] ..."
    }
  (match action.disableRulePayload? with
    | some payload => payload.rune.contains "NBR-CALLS-FLOG2-UPPER-BOUND" && payload.goalTarget = some "Goal"
    | none => false) &&
    (action.structuredLines 2).any (fun line =>
      line.contains "disable-rule:" && line.contains "NBR-CALLS-FLOG2-UPPER-BOUND")

#guard dynamicDisableRulePayloadParses

private def dynamicDisableDefinitionPayloadParses : Bool :=
  let triggerAction : DynamicAction :=
    { kind := "disable-definition"
      source := "warning"
      summary := "disable (:DEFINITION BADGE) so trigger term (BADGE FN) can arise for BADGE-TYPE"
      goal_target := none
      targets := ["(:DEFINITION BADGE)", "BADGE-TYPE", "(BADGE FN)"]
      detail := "ACL2 Warning [Non-rec] ..."
    }
  let freeSearchAction : DynamicAction :=
    { kind := "disable-definition"
      source := "warning"
      summary := "disable (:DEFINITION POSP) so free-variable search for Y via (POSP Y) can succeed in LEMMA-2"
      goal_target := none
      targets := ["(:DEFINITION POSP)", "LEMMA-2", "Y", "(POSP Y)"]
      detail := "ACL2 Warning [Non-rec] ..."
    }
  (match triggerAction.disableDefinitionPayload? with
    | some payload =>
        payload.definitionRune = "(:DEFINITION BADGE)" &&
          payload.thmName = "BADGE-TYPE" &&
          payload.triggerTerm = some "(BADGE FN)"
    | none => false) &&
    (match freeSearchAction.disableDefinitionPayload? with
      | some payload =>
          payload.definitionRune = "(:DEFINITION POSP)" &&
            payload.thmName = "LEMMA-2" &&
            payload.freeVar = some "Y" &&
            payload.hypothesis = some "(POSP Y)"
      | none => false) &&
    (freeSearchAction.structuredLines 2).any (fun line =>
      line.contains "hypothesis:" && line.contains "(POSP Y)")

#guard dynamicDisableDefinitionPayloadParses

private def dynamicFreeVariableBindingPayloadParses : Bool :=
  let action : DynamicAction :=
    { kind := "bind-free-variable"
      source := "warning"
      summary := "bind free variable J using (EQUAL (NONNEG-INT-MOD J GCD) '0) when rule sees (FLOOR I GCD)"
      goal_target := none
      targets := ["J", "(EQUAL (NONNEG-INT-MOD J GCD) '0)", "(FLOOR I GCD)"]
      detail := "ACL2 Warning [Free] ..."
    }
  (match action.freeVariableBindingPayload? with
    | some payload =>
        payload.freeVar = "J" &&
          payload.hypothesis.contains "NONNEG-INT-MOD" &&
          payload.triggerTerm = some "(FLOOR I GCD)"
    | none => false) &&
    (action.structuredLines 2).any (fun line =>
      line.contains "trigger-term:" && line.contains "(FLOOR I GCD)")

#guard dynamicFreeVariableBindingPayloadParses

private def dynamicRewriteOverlapPayloadParses : Bool :=
  let action : DynamicAction :=
    { kind := "watch-rune-overlap"
      source := "warning"
      summary := "compare generated rewrite from LEMMA-4 with existing rewrite |(+ y x)|"
      goal_target := none
      targets := ["LEMMA-4", "|(+ y x)|"]
      detail := "ACL2 Warning [Subsume] ..."
    }
  (match action.rewriteOverlapPayload? with
    | some payload => payload.generatedTheorem = "LEMMA-4" && payload.existingRule = "|(+ y x)|"
    | none => false) &&
    (action.structuredLines 2).any (fun line =>
      line.contains "existing-rule:" && line.contains "|(+ y x)|")

#guard dynamicRewriteOverlapPayloadParses

private def dynamicSummaryRuleParses : Bool :=
  let rewriteRule? := SummaryRule.ofString? "(:REWRITE NBR-CALLS-FLOG2-UPPER-BOUND)"
  let fakeRune? := SummaryRule.ofString? "(:FAKE-RUNE-FOR-LINEAR NIL)"
  (match rewriteRule? with
    | some rule =>
        rule.kind = "rewrite" &&
          rule.target?.map toString = some "nbr-calls-flog2-upper-bound" &&
          rule.extras.isEmpty &&
          rule.summary = "rewrite nbr-calls-flog2-upper-bound"
    | none => false) &&
    (match fakeRune? with
      | some rule =>
          rule.kind = "fake-rune-for-linear" &&
            rule.target?.map toString = some "NIL" &&
            rule.summary = "fake-rune-for-linear NIL" &&
            ((rule.structuredLines 2).any (fun line =>
              line.contains "target:" && line.contains "NIL")
            )
      | none => false)

#guard dynamicSummaryRuleParses

private def dynamicSummaryRulesRenderStructured : Bool :=
  let artifact : DynamicArtifact :=
    { book := "acl2_samples/demo.lisp"
      resolved_book := "acl2_samples/demo.lisp"
      load_steps := ["acl2_samples/demo.lisp"]
      load_note := ""
      requested_theorem := "demo"
      theorem_name := "DEMO"
      status := "proved"
      summary_form := "( DEFTHM DEMO ...)"
      summary_rules :=
        [ "(:REWRITE NBR-CALLS-FLOG2-UPPER-BOUND)"
        , "(:FAKE-RUNE-FOR-LINEAR NIL)"
        ]
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
      stderr := ""
      exit_code := 0
    }
  artifact.summaryRuleItems =
      ["rewrite nbr-calls-flog2-upper-bound", "fake-rune-for-linear NIL"] &&
    (renderLines artifact).any (·.contains "rewrite nbr-calls-flog2-upper-bound") &&
    (renderLines artifact).any (·.contains "fake-rune-for-linear NIL")

#guard dynamicSummaryRulesRenderStructured

private def dynamicReplayStateSummarizesActions : Bool :=
  let artifact : DynamicArtifact :=
    { book := "acl2_samples/demo.lisp"
      resolved_book := "acl2_samples/demo.lisp"
      load_steps := ["acl2_samples/demo.lisp"]
      load_note := ""
      requested_theorem := "demo"
      theorem_name := "DEMO"
      status := "proved"
      summary_form := "( DEFTHM DEMO ...)"
      summary_rules := []
      hint_events := []
      splitter_rules := []
      warning_kinds := []
      summary_time := ""
      prover_steps := none
      actions :=
        [ { kind := "in-theory"
            source := "hint-event"
            summary := "adjust theory (DISABLE FLOOR)"
            goal_target := none
            targets := ["(DISABLE FLOOR)"]
            detail := "(:IN-THEORY (DISABLE FLOOR))"
          }
        , { kind := "disable-rule"
            source := "warning"
            summary := "disable (:REWRITE FOO) in Goal"
            goal_target := some "Goal"
            targets := ["(:REWRITE FOO)", "Goal"]
            detail := "ACL2 Warning [Use] ..."
          }
        , { kind := "use"
            source := "transcript-hint"
            summary := "use (:INSTANCE NOTE-3 (P P) (Q Q)) in Goal"
            goal_target := some "Goal"
            targets := ["(:INSTANCE NOTE-3 (P P) (Q Q))", "Goal"]
            detail := "Goal: (:USE ((:INSTANCE NOTE-3 (P P) (Q Q))))"
          }
        , { kind := "split-goal"
            source := "splitter"
            summary := "split using if-intro with ((:DEFINITION GCD-PROG!)) in Goal''"
            goal_target := some "Goal''"
            targets := ["if-intro", "((:DEFINITION GCD-PROG!))", "Goal''"]
            detail := "if-intro: ((:DEFINITION GCD-PROG!))"
          }
        , { kind := "induct"
            source := "induction"
            summary := "induct on (MAKE-PROG1-INDUCTION I N) using rule MAKE-PROG1-INDUCTION"
            goal_target := some "Goal'"
            targets := ["(MAKE-PROG1-INDUCTION I N)", "MAKE-PROG1-INDUCTION"]
            detail := "We will induct according to a scheme suggested by (MAKE-PROG1-INDUCTION I N)."
          }
        , { kind := "do-not-induct"
            source := "transcript-hint"
            summary := "do-not-induct T in Goal"
            goal_target := some "Goal"
            targets := ["T", "Goal"]
            detail := "Goal: (:DO-NOT-INDUCT T)"
          }
        , { kind := "otf-flg"
            source := "transcript-option"
            summary := "set otf-flg T"
            goal_target := none
            targets := ["T"]
            detail := "(:OTF-FLG T)"
          }
        , { kind := "typed-term"
            source := "observation"
            summary := "focus on typed term (CLOG2 N)"
            goal_target := none
            targets := ["(CLOG2 N)"]
            detail := "ACL2 Observation ..."
          }
        ]
      checkpoints := []
      progress := []
      observations := []
      warnings := []
      inductions := []
      raw_excerpt := []
      stderr := ""
      exit_code := 0
    }
  let state := artifact.replayState
  state.inductionSummary? = some "(make-prog1-induction i n) using MAKE-PROG1-INDUCTION @ Goal'" &&
    state.doNotInductSummary? = some "T @ Goal" &&
    state.otfFlag = some "T" &&
    state.theoryTimeline.any (fun line => line.contains "disable floor") &&
    state.theoryTimeline.any (fun line => line.contains "disable (:REWRITE FOO)") &&
    state.useTimeline.any (fun line => line.contains "note-3") &&
    state.splitTimeline.any (fun line => line.contains "if-intro with (:definition gcd-prog!)") &&
    state.typedTerms.any (fun line => line.contains "(clog2 n)") &&
    (renderLines artifact).any (fun line =>
      line.contains "selected-induction: (make-prog1-induction i n) using MAKE-PROG1-INDUCTION @ Goal'") &&
    (renderLines artifact).any (fun line =>
      line.contains "split-timeline:") &&
    (renderLines artifact).any (fun line =>
      line.contains "typed-terms:")

#guard dynamicReplayStateSummarizesActions

end HintBridge
end ACL2
