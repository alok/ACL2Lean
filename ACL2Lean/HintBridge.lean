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

def structuredLines (action : DynamicAction) (indent : Nat := 0) : List String :=
  match action.kind with
  | "in-theory" => action.theoryLines indent
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
  | _ => []

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

end HintBridge
end ACL2
