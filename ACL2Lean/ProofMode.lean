import Lean
import Lean.Data.Json
import ACL2Lean.Import
import ACL2Lean.HintBridge
import ProofWidgets.Component.HtmlDisplay

open Lean
open Lean.Json
open ProofWidgets
open Lean Elab Command Term Meta

namespace ACL2
namespace ProofMode

structure Checkpoint where
  title : String
  detail : String
  status : String

structure Snapshot where
  theoremName : String
  goal : String
  checkpoints : List Checkpoint
  runes : List String
  nextMoves : List String
  notes : List String

private def theoremMatches (needle : String) (name : Symbol) : Bool :=
  name.normalizedName = needle.map Char.toLower

private def dedupStrings (items : List String) : List String :=
  items.foldl
    (fun acc item =>
      if item.isEmpty || acc.contains item then
        acc
      else
        acc ++ [item])
    []

private def inlineBlock (text : String) : String :=
  String.intercalate " " <|
    (text.splitOn "\n").foldr
      (fun line acc =>
        let trimmed := line.trimAscii.toString
        if trimmed.isEmpty then acc else trimmed :: acc)
      []

private def summarizeInstruction (instruction : ProofInstruction) : String :=
  String.intercalate " -> " (ProofInstruction.renderLines 0 instruction)

private def summarizeRuleClasses (info : TheoremInfo) : String :=
  match info.ruleClasses.map RuleClass.summary with
  | [] => "none"
  | ruleClasses => String.intercalate ", " ruleClasses

private def theoremContextCheckpoint (info : TheoremInfo) (theories : List TheoryExpr) : Checkpoint :=
  { title := "Imported theorem context"
    detail := s!"Recovered {info.hintGoals.length} hints, {info.instructions.length} instruction blocks, and {theories.length} prior theory events."
    status := "done" }

private def instructionCheckpoints : Nat → List ProofInstruction → List Checkpoint
  | _, [] => []
  | idx, instruction :: rest =>
      { title := s!"Replay step {idx + 1}"
        detail := summarizeInstruction instruction
        status := if idx = 0 then "active" else "planned" } ::
        instructionCheckpoints (idx + 1) rest

private def hintCheckpoints : Nat → List GoalHint → List Checkpoint
  | _, [] => []
  | idx, hint :: rest =>
      { title := s!"Hint target {idx + 1}"
        detail := hint.summary
        status := if idx = 0 then "active" else "planned" } ::
        hintCheckpoints (idx + 1) rest

private def theoryItems : TheoryExpr → List String
  | expr => expr.bulletItems

private def hintRunes (hint : GoalHint) : List String :=
  let useLines :=
    match hint.findOption? "use" with
    | some expr => [s!"use {expr}"]
    | none => []
  let theoryLines :=
    match hint.inTheory? with
    | some theoryExpr => theoryItems theoryExpr
    | none => []
  useLines ++ theoryLines

private def importedCheckpoints (info : TheoremInfo) (theories : List TheoryExpr) : List Checkpoint :=
  let context := theoremContextCheckpoint info theories
  let instructions := info.instructions
  match instructions with
  | _ :: _ =>
      context :: instructionCheckpoints 0 instructions
  | [] =>
      let hints := info.hintGoals
      match hints with
      | _ :: _ =>
          context :: hintCheckpoints 0 hints
      | [] =>
          [ context
          , { title := "Replay planning"
              detail := "No structured :instructions or goal hints were imported; start replay from the theorem body and active theory context."
              status := "active" }
          ]

private def importedRunes (info : TheoremInfo) (theories : List TheoryExpr) : List String :=
  let theoryLines := theories.foldr (fun theory acc => theoryItems theory ++ acc) []
  let hintLines := info.hintGoals.foldr (fun hint acc => hintRunes hint ++ acc) []
  dedupStrings <|
    theoryLines ++
      hintLines ++
      (info.ruleClasses.map (fun ruleClass => s!"rule-class {ruleClass.summary}"))

private def importedNextMoves (info : TheoremInfo) (theories : List TheoryExpr) : List String :=
  let candidates : List (Option String) :=
    [ if info.instructions.isEmpty then
        some "Start replay from the theorem body and imported hints because this theorem has no explicit proof-builder script."
      else
        some "Interpret the imported proof-builder instructions against a Lean goal and replace planned checkpoints with checked replay state."
    , if theories.isEmpty then
        none
      else
        some "Map the prior ACL2 theory events into a Lean-side active rune or simp set before replay."
    , if info.ruleClasses.isEmpty then
        none
      else
        some "Thread imported ACL2 rule-classes into replay so rewrite and meta intent survives translation."
    ]
  dedupStrings (candidates.filterMap id)

private def importedNotes (sourcePath : String) (info : TheoremInfo) (theories : List TheoryExpr) : List String :=
  let extraOptionNote :=
    match info.extraOptions.map (fun option => s!":{option.key}") with
    | [] => []
    | keys => [s!"Other theorem options: {String.intercalate ", " keys}"]
  [ s!"Source ACL2 book: {sourcePath}"
  , s!"Rule-classes: {summarizeRuleClasses info}"
  , s!"Top-level theory events before theorem: {theories.length}"
  ] ++ extraOptionNote

def snapshotOfImportedTheorem
    (sourcePath : String)
    (theoremName : Symbol)
    (info : TheoremInfo)
    (theories : List TheoryExpr) : Snapshot :=
  { theoremName := s!"Imported ACL2 theorem {repr theoremName}"
    goal := s!"ACL2 formula:\n  {info.body}\n\nReplay context:\n  prior theory events in scope: {theories.length}\n  structured hints: {info.hintGoals.length}\n  structured instructions: {info.instructions.length}"
    checkpoints := importedCheckpoints info theories
    runes := importedRunes info theories
    nextMoves := importedNextMoves info theories
    notes := importedNotes sourcePath info theories
  }

private def dynamicContextCheckpoint (artifact : ACL2.HintBridge.DynamicArtifact) : Checkpoint :=
  let replayState := artifact.replayState
  let keyCheckpointCount :=
    artifact.checkpoints.foldl
      (fun count checkpoint => if checkpoint.kind = "key-checkpoint" then count + 1 else count)
      0
  let traceCheckpointCount := artifact.checkpoints.length - keyCheckpointCount
  let progressCount := artifact.progress.length
  { title := "Dynamic ACL2 hint extraction"
    detail := s!"Recovered {keyCheckpointCount} key checkpoints, {traceCheckpointCount} raw goal/subgoal markers, {progressCount} lifecycle progress events, {artifact.actions.length} candidate replay actions, {replayState.theoryTimeline.length} theory steps, {replayState.useTimeline.length} replay uses, {replayState.splitTimeline.length} split steps, {replayState.typedTerms.length} typed-term foci, {artifact.observations.length} observations, {artifact.warnings.length} warnings, {artifact.inductions.length} induction summaries, {artifact.summary_rules.length} summary rules, and {artifact.hint_events.length} hint-events from the ACL2 proof run."
    status :=
      if artifact.checkpoints.isEmpty && artifact.progress.isEmpty && artifact.actions.isEmpty then
        "planned"
      else
        "done" }

private def completedCheckpointLabels (artifact : ACL2.HintBridge.DynamicArtifact) : List String :=
  dedupStrings <|
    artifact.progress.foldr
      (fun entry acc =>
        if entry.kind = "checkpoint-complete" then
          entry.label :: acc
        else
          acc)
      []

private def dynamicCheckpointTitle (idx : Nat) (checkpoint : ACL2.HintBridge.DynamicCheckpoint) : String :=
  match checkpoint.kind with
  | "key-checkpoint" => s!"ACL2 key checkpoint {idx + 1}: {checkpoint.label}"
  | "goal" => s!"ACL2 goal: {checkpoint.label}"
  | "subgoal" => s!"ACL2 {checkpoint.label}"
  | _ => s!"Emitted checkpoint {idx + 1}: {checkpoint.label}"

private def checkpointTargetedActions
    (artifact : ACL2.HintBridge.DynamicArtifact)
    (checkpoint : ACL2.HintBridge.DynamicCheckpoint) : List ACL2.HintBridge.DynamicAction :=
  artifact.actions.filter (fun action => action.goal_target = some checkpoint.label)

private def targetedActionDetailLines (action : ACL2.HintBridge.DynamicAction) : List String :=
  [s!"- {action.summary}"] ++ action.structuredLines 4

private def dynamicCheckpointDetail
    (artifact : ACL2.HintBridge.DynamicArtifact)
    (checkpoint : ACL2.HintBridge.DynamicCheckpoint) : String :=
  let targeted := checkpointTargetedActions artifact checkpoint
  if targeted.isEmpty then
    checkpoint.text
  else
    checkpoint.text ++
      "\n\nTargeted ACL2 actions:\n" ++
      (String.intercalate "\n" <|
        targeted.foldr (fun action acc => targetedActionDetailLines action ++ acc) [])

private def dynamicCheckpointEntries
    (artifact : ACL2.HintBridge.DynamicArtifact)
    (completedLabels : List String) : Nat → List ACL2.HintBridge.DynamicCheckpoint → List Checkpoint
  | _, [] => []
  | idx, checkpoint :: rest =>
      { title := dynamicCheckpointTitle idx checkpoint
        detail := dynamicCheckpointDetail artifact checkpoint
        status :=
          if completedLabels.contains checkpoint.label then
            "done"
          else if idx = 0 then
            "active"
          else
            "planned" } ::
        dynamicCheckpointEntries artifact completedLabels (idx + 1) rest

private def dynamicProgressTitle (idx : Nat) (entry : ACL2.HintBridge.DynamicProgress) : String :=
  match entry.kind with
  | "induction-push" => s!"ACL2 induction push: {entry.label}"
  | "subproof-complete" => s!"ACL2 subproof complete: {entry.label}"
  | "checkpoint-complete" => s!"ACL2 checkpoint complete: {entry.label}"
  | _ => s!"ACL2 progress {idx + 1}: {entry.label}"

private def dynamicProgressEntries : Nat → List ACL2.HintBridge.DynamicProgress → List Checkpoint
  | _, [] => []
  | idx, entry :: rest =>
      { title := dynamicProgressTitle idx entry
        detail := entry.text
        status := "done" } ::
        dynamicProgressEntries (idx + 1) rest

private def dynamicCheckpoints (artifact : ACL2.HintBridge.DynamicArtifact) : List Checkpoint :=
  let context := dynamicContextCheckpoint artifact
  let completedLabels := completedCheckpointLabels artifact
  let progress := dynamicProgressEntries 0 artifact.progress
  let emitted := dynamicCheckpointEntries artifact completedLabels 0 artifact.checkpoints
  match progress ++ emitted with
  | [] =>
      [ context
      , { title := "Hint generation"
          detail := "ACL2 did not emit any checkpoints or lifecycle progress for this theorem; inspect observations, warnings, and the raw excerpt."
          status := "active" }
      ]
  | checkpoints => context :: checkpoints

private def dynamicRunes (artifact : ACL2.HintBridge.DynamicArtifact) : List String :=
  let replayState := artifact.replayState
  let nonTheoryHintEvents :=
    artifact.hint_events.filter (fun event => !(inlineBlock event).startsWith "(:IN-THEORY")
  dedupStrings <|
    (artifact.summaryRuleItems.map (fun item => s!"summary-rule {item}")) ++
      (nonTheoryHintEvents.map (fun event => s!"hint-event {event}")) ++
      (replayState.theoryTimeline.map (fun line => s!"theory-step {line}")) ++
      (artifact.splitter_rules.map (fun rule => s!"splitter {rule}")) ++
      (artifact.warning_kinds.map (fun kind => s!"warning-kind {kind}"))

private def actionSummary (action : ACL2.HintBridge.DynamicAction) : String :=
  s!"ACL2 suggests: {action.summary}"

private def actionNote (action : ACL2.HintBridge.DynamicAction) : String :=
  let goalTarget :=
    match action.goal_target with
    | some goal => s!" @ {goal}"
    | none => ""
  let targets :=
    if action.targets.isEmpty then
      ""
    else
      s!" [{String.intercalate ", " action.targets}]"
  let theory :=
    match action.theoryItems with
    | [] => ""
    | items => " {theory: " ++ String.intercalate "; " items ++ "}"
  let clauseProcessor :=
    match action.clauseProcessorItems with
    | [] => ""
    | items => " {clause-processor: " ++ String.intercalate "; " items ++ "}"
  let otfFlag :=
    match action.otfFlagExpr? with
    | some expr => " {otf-flg: " ++ toString expr ++ "}"
    | none => ""
  let inductTerm :=
    match action.inductTermItems with
    | [] => ""
    | items => " {induct-term: " ++ String.intercalate "; " items ++ "}"
  let inductionRule :=
    match action.inductionRule? with
    | some rule => " {induction-rule: " ++ rule ++ "}"
    | none => ""
  let expand :=
    match action.expandItems with
    | [] => ""
    | items => " {expand: " ++ String.intercalate "; " items ++ "}"
  let cases :=
    match action.casesItems with
    | [] => ""
    | items => " {cases: " ++ String.intercalate "; " items ++ "}"
  let doNotInduct :=
    match action.doNotInductExpr? with
    | some expr => " {do-not-induct: " ++ toString expr ++ "}"
    | none => ""
  let disableRule :=
    match action.disableRulePayload? with
    | some payload => " {disable-rule: " ++ payload.rune ++ "}"
    | none => ""
  let disableDefinition :=
    match action.disableDefinitionPayload? with
    | some payload => " {disable-definition: " ++ payload.definitionRune ++ "}"
    | none => ""
  let warningTheorem :=
    match action.disableDefinitionPayload? with
    | some payload => " {theorem: " ++ payload.thmName ++ "}"
    | none => ""
  let freeVariable :=
    match action.freeVariableBindingPayload? with
    | some payload => " {variable: " ++ payload.freeVar ++ "}"
    | none =>
        match action.disableDefinitionPayload? with
        | some payload =>
            match payload.freeVar with
            | some freeVar => " {variable: " ++ freeVar ++ "}"
            | none => ""
        | none => ""
  let hypothesis :=
    match action.freeVariableBindingPayload? with
    | some payload => " {hypothesis: " ++ payload.hypothesis ++ "}"
    | none =>
        match action.disableDefinitionPayload? with
        | some payload =>
            match payload.hypothesis with
            | some hypothesis => " {hypothesis: " ++ hypothesis ++ "}"
            | none => ""
        | none => ""
  let triggerTerm :=
    match action.freeVariableBindingPayload? with
    | some payload =>
        match payload.triggerTerm with
        | some term => " {trigger-term: " ++ term ++ "}"
        | none => ""
    | none =>
        match action.disableDefinitionPayload? with
        | some payload =>
            match payload.triggerTerm with
            | some term => " {trigger-term: " ++ term ++ "}"
            | none => ""
        | none => ""
  let generatedTheorem :=
    match action.rewriteOverlapPayload? with
    | some payload => " {generated-theorem: " ++ payload.generatedTheorem ++ "}"
    | none => ""
  let existingRule :=
    match action.rewriteOverlapPayload? with
    | some payload => " {existing-rule: " ++ payload.existingRule ++ "}"
    | none => ""
  let splitGoal :=
    match action.splitGoalPayload? with
    | some payload => " {splitter: " ++ payload.splitterName ++ "}"
    | none => ""
  let splitTerms :=
    match action.splitGoalItems with
    | [] => ""
    | items => " {split-term: " ++ String.intercalate "; " items ++ "}"
  let typedTerm :=
    match action.typedTermItems with
    | [] => ""
    | items => " {typed-term: " ++ String.intercalate "; " items ++ "}"
  s!"action {action.source}/{action.kind}{goalTarget}: {action.summary}{targets}{theory}{clauseProcessor}{otfFlag}{inductTerm}{inductionRule}{expand}{cases}{doNotInduct}{disableRule}{disableDefinition}{warningTheorem}{freeVariable}{hypothesis}{triggerTerm}{generatedTheorem}{existingRule}{splitGoal}{splitTerms}{typedTerm}"

private def dynamicNextMoves (artifact : ACL2.HintBridge.DynamicArtifact) : List String :=
  let replayState := artifact.replayState
  dedupStrings <|
    (artifact.actions.map actionSummary) ++
    [ if artifact.summary_rules.isEmpty then
        some "ACL2 did not report summary rules for this theorem; extend the parser or pick a theorem whose proof emits replay-relevant rule usage."
      else
        some "Map ACL2's summary rules into a Lean-side active rune or simp-set model instead of treating them as display-only metadata."
    , if replayState.theoryTimeline.isEmpty then
        none
      else
        some "Translate ACL2's interpreted theory timeline into Lean-side simp/grind configuration instead of leaving theory changes as display-only metadata."
    , if artifact.hint_events.isEmpty then
        none
      else
        some "Interpret ACL2's emitted hint-events as candidate Lean replay steps before reconstructing those hints manually."
    , if artifact.checkpoints.isEmpty then
        some "Try a theorem with richer ACL2 proof output or adjust the ACL2 driver to emit more checkpoints."
      else
        some "Translate the first emitted ACL2 checkpoint into a Lean-side replay step and compare it to the current theorem goal."
    , if artifact.progress.isEmpty then
        none
      else
        some "Use ACL2's emitted induction-push and completion events to reconcile planned checkpoints with checked replay progress."
    , if artifact.inductions.isEmpty then
        none
      else
        some "Map ACL2's emitted induction scheme into a Lean induction candidate instead of reconstructing it from scratch."
    , if replayState.inductionSummary?.isNone then
        none
      else
        some "Use ACL2's selected induction candidate directly in the next Lean replay step instead of re-deriving it manually."
    , if replayState.doNotInductSummary?.isNone then
        none
      else
        some "Respect ACL2's do-not-induct guidance when choosing between simplification and induction on the Lean side."
    , if replayState.useTimeline.isEmpty then
        none
      else
        some "Try ACL2's concrete use timeline before broad manual lemma search."
    , if replayState.splitTimeline.isEmpty then
        none
      else
        some "Use ACL2's checkpoint-local split timeline to decide whether the next Lean replay step should branch before rewriting."
    , if replayState.typedTerms.isEmpty then
        none
      else
        some "Use ACL2's typed-term focus as the next Lean simplification or rewriting target instead of scanning the full goal blindly."
    , if artifact.warnings.isEmpty then
        none
      else
        some "Treat ACL2 warning lines as replay guidance or fallback heuristics for Lean proof search."
    ].filterMap id

private def dynamicNotes (sourcePath : String) (artifact : ACL2.HintBridge.DynamicArtifact) : List String :=
  let replayState := artifact.replayState
  dedupStrings <|
    [ s!"Source ACL2 book: {sourcePath}"
    , s!"ACL2 loaded book: {artifact.resolved_book}"
    , s!"Requested theorem: {artifact.requested_theorem}"
    , s!"ACL2 matched theorem: {artifact.theorem_name}"
    , s!"Extraction status: {artifact.status}"
    , s!"Structured ACL2 actions: {artifact.actions.length}"
    ] ++
      (if artifact.load_note.isEmpty then [] else [s!"Load plan: {artifact.load_note}"]) ++
      (if artifact.load_steps.length ≤ 1 then
        []
      else
        [s!"ACL2 load steps: {String.intercalate " -> " artifact.load_steps}"]) ++
      (if artifact.summary_time.isEmpty then [] else [s!"ACL2 summary time: {artifact.summary_time}"]) ++
      (match artifact.prover_steps with
        | some steps => [s!"ACL2 prover steps: {steps}"]
        | none => []) ++
      replayState.noteLines ++
      (artifact.actions.map actionNote) ++
      (artifact.actions.foldr
        (fun action acc =>
          match action.usePayload? with
          | some payload =>
              let targetLines :=
                match payload.bindings with
                | [] =>
                    match payload.target with
                    | .theorem expr => [s!"action-use-theorem {action.source}/{action.kind}: {expr}"]
                    | .ref _ => []
                | _ => [s!"action-use-instance {action.source}/{action.kind}: {payload.target.instanceSummary}"]
              let bindingLines :=
                payload.bindings.map (fun binding =>
                  s!"action-use-binding {action.source}/{action.kind}: {binding.summary}")
              targetLines ++ bindingLines ++ acc
          | none => acc)
        []) ++
      (artifact.actions.foldr
        (fun action acc =>
          (action.theoryItems.map (fun item => s!"action-theory {action.source}/{action.kind}: {item}")) ++ acc)
        []) ++
      (artifact.actions.foldr
        (fun action acc =>
          (action.clauseProcessorItems.map (fun item => s!"action-clause-processor {action.source}/{action.kind}: {item}")) ++ acc)
        []) ++
      (artifact.actions.foldr
        (fun action acc =>
          match action.otfFlagExpr? with
          | some expr => s!"action-otf-flg {action.source}/{action.kind}: {expr}" :: acc
          | none => acc)
        []) ++
      (artifact.actions.foldr
        (fun action acc =>
          (action.inductTermItems.map (fun item => s!"action-induct-term {action.source}/{action.kind}: {item}")) ++ acc)
        []) ++
      (artifact.actions.foldr
        (fun action acc =>
          match action.inductionRule? with
          | some rule => s!"action-induction-rule {action.source}/{action.kind}: {rule}" :: acc
          | none => acc)
        []) ++
      (artifact.actions.foldr
        (fun action acc =>
          (action.expandItems.map (fun item => s!"action-expand {action.source}/{action.kind}: {item}")) ++ acc)
        []) ++
      (artifact.actions.foldr
        (fun action acc =>
          (action.casesItems.map (fun item => s!"action-cases {action.source}/{action.kind}: {item}")) ++ acc)
        []) ++
      (artifact.actions.foldr
        (fun action acc =>
          match action.splitGoalPayload? with
          | some payload =>
              let payloadLines :=
                action.splitGoalItems.map (fun item =>
                  s!"action-split-term {action.source}/{action.kind}: {item}")
              (s!"action-splitter {action.source}/{action.kind}: {payload.splitterName}" :: payloadLines) ++ acc
          | none => acc)
        []) ++
      (artifact.actions.foldr
        (fun action acc =>
          match action.doNotInductExpr? with
          | some expr => s!"action-do-not-induct {action.source}/{action.kind}: {expr}" :: acc
          | none => acc)
        []) ++
      (artifact.actions.foldr
        (fun action acc =>
          (action.typedTermItems.map (fun item => s!"action-typed-term {action.source}/{action.kind}: {item}")) ++ acc)
        []) ++
      (artifact.actions.foldr
        (fun action acc =>
          match action.disableRulePayload? with
          | some payload => s!"action-disable-rule {action.source}/{action.kind}: {payload.rune}" :: acc
          | none => acc)
        []) ++
      (artifact.actions.foldr
        (fun action acc =>
          match action.disableDefinitionPayload? with
          | some payload =>
              let base :=
                [ s!"action-disable-definition {action.source}/{action.kind}: {payload.definitionRune}"
                , s!"action-warning-theorem {action.source}/{action.kind}: {payload.thmName}"
                ]
              let withVariable :=
                match payload.freeVar with
                | some freeVar => base ++ [s!"action-free-variable {action.source}/{action.kind}: {freeVar}"]
                | none => base
              let withHypothesis :=
                match payload.hypothesis with
                | some hypothesis => withVariable ++ [s!"action-binding-hypothesis {action.source}/{action.kind}: {hypothesis}"]
                | none => withVariable
              let withTrigger :=
                match payload.triggerTerm with
                | some term => withHypothesis ++ [s!"action-trigger-term {action.source}/{action.kind}: {term}"]
                | none => withHypothesis
              withTrigger ++ acc
          | none => acc)
        []) ++
      (artifact.actions.foldr
        (fun action acc =>
          match action.freeVariableBindingPayload? with
          | some payload =>
              let base :=
                [ s!"action-free-variable {action.source}/{action.kind}: {payload.freeVar}"
                , s!"action-binding-hypothesis {action.source}/{action.kind}: {payload.hypothesis}"
                ]
              let withTrigger :=
                match payload.triggerTerm with
                | some term => base ++ [s!"action-trigger-term {action.source}/{action.kind}: {term}"]
                | none => base
              withTrigger ++ acc
          | none => acc)
        []) ++
      (artifact.actions.foldr
        (fun action acc =>
          match action.rewriteOverlapPayload? with
          | some payload =>
              [ s!"action-generated-theorem {action.source}/{action.kind}: {payload.generatedTheorem}"
              , s!"action-existing-rule {action.source}/{action.kind}: {payload.existingRule}"
              ] ++ acc
          | none => acc)
        []) ++
      (if artifact.observations.isEmpty then [] else artifact.observations.map (fun block => s!"observation: {inlineBlock block}")) ++
      (if artifact.warnings.isEmpty then [] else artifact.warnings.map (fun block => s!"warning: {inlineBlock block}")) ++
      (if artifact.inductions.isEmpty then [] else artifact.inductions.map (fun block => s!"induction: {inlineBlock block}")) ++
      (if artifact.progress.isEmpty then
        []
      else
        artifact.progress.map (fun entry => s!"progress {entry.kind}: {inlineBlock entry.text}")) ++
      (if artifact.warning_kinds.isEmpty then [] else [s!"Warning kinds: {String.intercalate ", " artifact.warning_kinds}"]) ++
      (if artifact.stderr.isEmpty then [] else [s!"ACL2 stderr: {artifact.stderr}"])

def snapshotOfDynamicHints
    (sourcePath theoremName : String)
    (artifact : ACL2.HintBridge.DynamicArtifact) : Snapshot :=
  let replayState := artifact.replayState
  let selectedInduction := replayState.inductionSummary?.getD "none"
  let doNotInduct := replayState.doNotInductSummary?.getD "none"
  let otfFlag := replayState.otfFlag.getD "none"
  { theoremName := s!"ACL2 emitted hints for {theoremName}"
    goal := s!"ACL2 dynamic summary:\n  {artifact.summary_form}\n\nDynamic proof context:\n  checkpoints: {artifact.checkpoints.length}\n  lifecycle progress events: {artifact.progress.length}\n  candidate actions: {artifact.actions.length}\n  theory timeline entries: {replayState.theoryTimeline.length}\n  replay use suggestions: {replayState.useTimeline.length}\n  split timeline entries: {replayState.splitTimeline.length}\n  typed-term foci: {replayState.typedTerms.length}\n  selected induction: {selectedInduction}\n  do-not-induct: {doNotInduct}\n  otf-flg: {otfFlag}\n  observations: {artifact.observations.length}\n  warnings: {artifact.warnings.length}\n  induction summaries: {artifact.inductions.length}\n  summary rules: {artifact.summary_rules.length}\n  hint-events: {artifact.hint_events.length}\n  prover steps: {artifact.prover_steps.getD 0}"
    checkpoints := dynamicCheckpoints artifact
    runes := dynamicRunes artifact
    nextMoves := dynamicNextMoves artifact
    notes := dynamicNotes sourcePath artifact
  }

private def dynamicTheoryItemsSurfaceInRunes : Bool :=
  let artifact : ACL2.HintBridge.DynamicArtifact :=
    { book := "acl2_samples/demo.lisp"
      resolved_book := "acl2_samples/demo.lisp"
      load_steps := ["acl2_samples/demo.lisp"]
      load_note := ""
      requested_theorem := "demo"
      theorem_name := "DEMO"
      status := "proved"
      summary_form := "( DEFTHM DEMO ...)"
      summary_rules := []
      hint_events := ["(:IN-THEORY (DISABLE FLOOR))"]
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
  dynamicRunes artifact = ["theory-step hint-event: disable floor"]

#guard dynamicTheoryItemsSurfaceInRunes

private def dynamicSummaryRulesSurfaceInRunes : Bool :=
  let artifact : ACL2.HintBridge.DynamicArtifact :=
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
  dynamicRunes artifact =
      [ "summary-rule rewrite nbr-calls-flog2-upper-bound"
      , "summary-rule fake-rune-for-linear NIL"
      ]

#guard dynamicSummaryRulesSurfaceInRunes

private def dynamicStructuredPayloadsSurfaceInNotes : Bool :=
  let artifact : ACL2.HintBridge.DynamicArtifact :=
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
        [ { kind := "clause-processor"
            source := "hint-event"
            summary := "clause-processor FLAG::FLAG-IS-CP"
            goal_target := none
            targets := ["FLAG::FLAG-IS-CP"]
            detail := "(:CLAUSE-PROCESSOR FLAG::FLAG-IS-CP)"
          }
        , { kind := "use"
            source := "transcript-hint"
            summary := "use (:INSTANCE NOTE-3 (P P) (Q Q)) in Goal"
            goal_target := some "Goal"
            targets := ["(:INSTANCE NOTE-3 (P P) (Q Q))", "Goal"]
            detail := "Goal: (:USE ((:INSTANCE NOTE-3 (P P) (Q Q))))"
          }
        , { kind := "otf-flg"
            source := "transcript-option"
            summary := "set otf-flg T"
            goal_target := none
            targets := ["T"]
            detail := "(:OTF-FLG T)"
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
            goal_target := none
            targets := ["(MAKE-PROG1-INDUCTION I N)", "MAKE-PROG1-INDUCTION"]
            detail := "We will induct according to a scheme suggested by (MAKE-PROG1-INDUCTION I N)."
          }
        , { kind := "expand"
            source := "transcript-hint"
            summary := "expand ((EV$ X A)) in Goal"
            goal_target := some "Goal"
            targets := ["((EV$ X A))", "Goal"]
            detail := "Goal: (:EXPAND ((EV$ X A)))"
          }
        , { kind := "do-not-induct"
            source := "transcript-hint"
            summary := "do-not-induct T in Goal"
            goal_target := some "Goal"
            targets := ["T", "Goal"]
            detail := "Goal: (:DO-NOT-INDUCT T)"
          }
        , { kind := "disable-rule"
            source := "warning"
            summary := "disable (:REWRITE NBR-CALLS-FLOG2-UPPER-BOUND) in Goal"
            goal_target := some "Goal"
            targets := ["(:REWRITE NBR-CALLS-FLOG2-UPPER-BOUND)", "Goal"]
            detail := "ACL2 Warning [Use] ..."
          }
        , { kind := "disable-definition"
            source := "warning"
            summary := "disable (:DEFINITION POSP) so free-variable search for Y via (POSP Y) can succeed in LEMMA-2"
            goal_target := none
            targets := ["(:DEFINITION POSP)", "LEMMA-2", "Y", "(POSP Y)"]
            detail := "ACL2 Warning [Non-rec] ..."
          }
        , { kind := "bind-free-variable"
            source := "warning"
            summary := "bind free variable J using (EQUAL (NONNEG-INT-MOD J GCD) '0) when rule sees (FLOOR I GCD)"
            goal_target := none
            targets := ["J", "(EQUAL (NONNEG-INT-MOD J GCD) '0)", "(FLOOR I GCD)"]
            detail := "ACL2 Warning [Free] ..."
          }
        , { kind := "watch-rune-overlap"
            source := "warning"
            summary := "compare generated rewrite from LEMMA-4 with existing rewrite |(+ y x)|"
            goal_target := none
            targets := ["LEMMA-4", "|(+ y x)|"]
            detail := "ACL2 Warning [Subsume] ..."
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
  let notes := (snapshotOfDynamicHints "acl2_samples/demo.lisp" "demo" artifact).notes
  notes.any (fun note => note.contains "Replay induction: (make-prog1-induction i n) using MAKE-PROG1-INDUCTION") &&
    notes.any (fun note => note.contains "Replay otf-flg: T") &&
    notes.any (fun note => note.contains "Replay use: transcript-hint @ Goal: use note-3 with p := p, q := q") &&
    notes.any (fun note => note.contains "action-clause-processor hint-event/clause-processor:" && note.toLower.contains "flag-is-cp") &&
    notes.any (fun note => note.contains "action-use-instance transcript-hint/use:" && note.toLower.contains "note-3") &&
    notes.any (fun note => note.contains "action-use-binding transcript-hint/use:" && note.contains "p := p") &&
    notes.any (fun note => note.contains "action-use-binding transcript-hint/use:" && note.contains "q := q") &&
    notes.any (fun note => note.contains "action-otf-flg transcript-option/otf-flg: T") &&
    notes.any (fun note => note.contains "action-induct-term induction/induct:" && note.toLower.contains "make-prog1-induction") &&
    notes.any (fun note => note.contains "action-induction-rule induction/induct: MAKE-PROG1-INDUCTION") &&
    notes.any (fun note => note.contains "action-expand transcript-hint/expand:" && note.contains "ev$") &&
    notes.any (fun note => note.contains "Replay split: splitter @ Goal'': if-intro with (:definition gcd-prog!)") &&
    notes.any (fun note => note.contains "action-splitter splitter/split-goal: if-intro") &&
    notes.any (fun note => note.contains "action-split-term splitter/split-goal: (:definition gcd-prog!)") &&
    notes.any (fun note => note.contains "action-do-not-induct transcript-hint/do-not-induct:" && note.contains "T") &&
    notes.any (fun note => note.contains "Replay typed-term: observation: (clog2 n)") &&
    notes.any (fun note => note.contains "action-typed-term observation/typed-term: (clog2 n)") &&
    notes.any (fun note => note.contains "action-disable-rule warning/disable-rule:" && note.contains "NBR-CALLS-FLOG2-UPPER-BOUND") &&
    notes.any (fun note => note.contains "action-disable-definition warning/disable-definition:" && note.contains "(:DEFINITION POSP)") &&
    notes.any (fun note => note.contains "action-warning-theorem warning/disable-definition:" && note.contains "LEMMA-2") &&
    notes.any (fun note => note.contains "action-free-variable warning/bind-free-variable:" && note.contains "J") &&
    notes.any (fun note => note.contains "action-binding-hypothesis warning/bind-free-variable:" && note.contains "NONNEG-INT-MOD") &&
    notes.any (fun note => note.contains "action-trigger-term warning/bind-free-variable:" && note.contains "(FLOOR I GCD)") &&
    notes.any (fun note => note.contains "action-generated-theorem warning/watch-rune-overlap:" && note.contains "LEMMA-4") &&
    notes.any (fun note => note.contains "action-existing-rule warning/watch-rune-overlap:" && note.contains "|(+ y x)|")

#guard dynamicStructuredPayloadsSurfaceInNotes

private def findImportedTheoremContext
    (events : List Event)
    (theoremName : String) : Except String (Symbol × TheoremInfo × List TheoryExpr) :=
  let rec go (theoriesRev : List TheoryExpr) : List Event → Except String (Symbol × TheoremInfo × List TheoryExpr)
    | [] => .error s!"No theorem named {theoremName}"
    | .inTheory expr :: rest => go (TheoryExpr.ofSExpr expr :: theoriesRev) rest
    | .defthm name info :: rest =>
        if theoremMatches theoremName name then
          .ok (name, info, theoriesRev.reverse)
        else
          go theoriesRev rest
    | _ :: rest => go theoriesRev rest
  go [] (Event.flattenList events)

private def importedSnapshotFromFile (sourcePath theoremName : String) : IO (Except String Snapshot) := do
  match ← ACL2.loadEventsFromFile sourcePath with
  | .error err => pure (.error err)
  | .ok events =>
      pure <|
        (findImportedTheoremContext events theoremName).map fun (name, info, theories) =>
          snapshotOfImportedTheorem sourcePath name info theories

private def dynamicSnapshotFromFile (sourcePath theoremName : String) : IO (Except String Snapshot) := do
  match ← ACL2.HintBridge.fetchArtifact sourcePath theoremName with
  | .error err => pure (.error err)
  | .ok artifact =>
      if artifact.status = "proved" then
        pure (.ok (snapshotOfDynamicHints sourcePath theoremName artifact))
      else
        pure (.error s!"ACL2 did not prove {theoremName}; status was {artifact.status}")

private def dynamicSnapshotForPanel (sourcePath theoremName : String) : IO Snapshot := do
  match ← ACL2.HintBridge.fetchArtifact sourcePath theoremName with
  | .ok artifact =>
      pure <| snapshotOfDynamicHints sourcePath theoremName artifact
  | .error err =>
      pure <| snapshotOfDynamicHints sourcePath theoremName
        (ACL2.HintBridge.unavailableArtifact sourcePath theoremName err)

private def attr (name : String) (value : Json) : String × Json :=
  (name, value)

private def strAttr (name value : String) : String × Json :=
  (name, Json.str value)

private def badgeColor (status : String) : String :=
  match status with
  | "done" => "#125b35"
  | "active" => "#8c4b00"
  | "planned" => "#214f9b"
  | _ => "#555555"

private def pill (label : String) (status : String) : Html :=
  let style := Json.mkObj
    [ ("display", Json.str "inline-block")
    , ("padding", Json.str "0.15rem 0.55rem")
    , ("borderRadius", Json.str "999px")
    , ("background", Json.str (badgeColor status))
    , ("color", Json.str "#ffffff")
    , ("fontSize", Json.str "0.72rem")
    , ("fontWeight", Json.str "700")
    , ("letterSpacing", Json.str "0.04em")
    , ("textTransform", Json.str "uppercase")
    ]
  Html.element "span" #[attr "style" style] #[Html.text label]

private def sectionTitle (title : String) : Html :=
  Html.element "h3"
    #[strAttr "style" "margin:0 0 0.55rem 0; font-size:0.95rem; letter-spacing:0.04em; text-transform:uppercase; color:#355070;"]
    #[Html.text title]

private def bulletList (items : List String) : Html :=
  let children : Array Html := Id.run do
    let mut acc := #[]
    for item in items do
      acc := acc.push (Html.element "li" #[] #[Html.text item])
    acc
  Html.element "ul"
    #[strAttr "style" "margin:0; padding-left:1.1rem; display:flex; flex-direction:column; gap:0.3rem;"]
    children

private def checkpointCard (cp : Checkpoint) : Html :=
  let cardStyle := Json.mkObj
    [ ("display", Json.str "flex")
    , ("flexDirection", Json.str "column")
    , ("gap", Json.str "0.35rem")
    , ("padding", Json.str "0.7rem 0.8rem")
    , ("border", Json.str "1px solid #d7dee8")
    , ("borderRadius", Json.str "10px")
    , ("background", Json.str "#fbfcfe")
    ]
  Html.element "div" #[attr "style" cardStyle] #[
    Html.element "div"
      #[strAttr "style" "display:flex; align-items:center; justify-content:space-between; gap:0.75rem;"]
      #[
        Html.element "strong" #[strAttr "style" "color:#1f2937;"] #[Html.text cp.title],
        pill cp.status cp.status
      ],
    Html.element "div" #[strAttr "style" "color:#475569; line-height:1.35;"] #[Html.text cp.detail]
  ]

def render (snap : Snapshot) : Html :=
  let checkpointChildren : Array Html := Id.run do
    let mut acc := #[]
    for cp in snap.checkpoints do
      acc := acc.push (checkpointCard cp)
    acc
  let shellStyle := Json.mkObj
    [ ("fontFamily", Json.str "'Iosevka Term', 'SFMono-Regular', 'Menlo', monospace")
    , ("display", Json.str "grid")
    , ("gridTemplateColumns", Json.str "1.3fr 1fr")
    , ("gap", Json.str "0.9rem")
    , ("padding", Json.str "1rem")
    , ("borderRadius", Json.str "14px")
    , ("background", Json.str "linear-gradient(180deg, #f8fbff 0%, #eef4fb 100%)")
    , ("border", Json.str "1px solid #c9d6e5")
    , ("color", Json.str "#162033")
    ]
  let paneStyle := Json.mkObj
    [ ("display", Json.str "flex")
    , ("flexDirection", Json.str "column")
    , ("gap", Json.str "0.75rem")
    ]
  let cardStyle := Json.mkObj
    [ ("padding", Json.str "0.8rem 0.9rem")
    , ("borderRadius", Json.str "12px")
    , ("background", Json.str "#ffffff")
    , ("border", Json.str "1px solid #d7dee8")
    , ("boxShadow", Json.str "0 1px 2px rgba(0,0,0,0.03)")
    ]
  Html.element "div" #[attr "style" shellStyle] #[
    Html.element "div" #[attr "style" paneStyle] #[
      Html.element "div" #[attr "style" cardStyle] #[
        sectionTitle "ACL Proof Mode",
        Html.element "div" #[strAttr "style" "font-size:1rem; font-weight:700; margin-bottom:0.5rem;"] #[Html.text snap.theoremName],
        Html.element "pre"
          #[strAttr "style" "margin:0; white-space:pre-wrap; line-height:1.35; color:#243b53; background:#f7fafc; padding:0.75rem; border-radius:10px;"]
          #[Html.text snap.goal]
      ],
      Html.element "div" #[attr "style" cardStyle] #[
        sectionTitle "Checkpoints",
        Html.element "div"
          #[strAttr "style" "display:flex; flex-direction:column; gap:0.55rem;"]
          checkpointChildren
      ]
    ],
    Html.element "div" #[attr "style" paneStyle] #[
      Html.element "div" #[attr "style" cardStyle] #[
        sectionTitle "Runes / Facts",
        bulletList snap.runes
      ],
      Html.element "div" #[attr "style" cardStyle] #[
        sectionTitle "Next Moves",
        bulletList snap.nextMoves
      ],
      Html.element "div" #[attr "style" cardStyle] #[
        sectionTitle "Co-Design Notes",
        bulletList snap.notes
      ]
    ]
  ]

def demoSnapshot : Snapshot :=
  { theoremName := "demoLenAppendNil"
    goal := "Goal:\n  prove (equal (len (append x nil)) (len x))\n\nACL view:\n  checkpoint on simplification before induction\n  keep visible the selected induction variable and active rewrite runes"
    checkpoints :=
      [ { title := "Checkpoint 1"
          detail := "Normalize the current ACL term into the Lean encoding and show the exact translation the tactic is working on."
          status := "done" }
      , { title := "Checkpoint 2"
          detail := "Show the chosen induction variable, previous checkpoint goal, and resulting subgoals side by side."
          status := "active" }
      , { title := "Checkpoint 3"
          detail := "Track which rewrite rules or theorem hints were explicitly enabled for the current step."
          status := "planned" }
      ]
    runes :=
      [ "consp_cons"
      , "car_cons / cdr_cons"
      , "equal_self"
      , "demoAppend equation"
      , "demoLen equation"
      ]
    nextMoves :=
      [ "Connect widget props to actual tactic state instead of the static snapshot."
      , "Expose a compact rune timeline next to the active goal."
      , "Mirror the same theorem in lean-tui so the terminal and infoview layouts evolve together."
      ]
    notes :=
      [ "Infoview should specialize for ACL concerns instead of duplicating Lean's default goal view."
      , "lean-tui can own graph navigation; the infoview panel can own ACL-specific metadata and controls."
      , "A later grind/Sym pass can feed canonicalized term views and rewrite provenance into this panel."
      ]
  }

def demo : Html :=
  render demoSnapshot

def panelForGoal (theoremName goal : String) : Html :=
  render { demoSnapshot with theoremName, goal }

private def checkpointSyntax (cp : Checkpoint) : CommandElabM (TSyntax `term) := do
  let title := Syntax.mkStrLit cp.title
  let detail := Syntax.mkStrLit cp.detail
  let status := Syntax.mkStrLit cp.status
  `(ACL2.ProofMode.Checkpoint.mk $title $detail $status)

private def stringListSyntax : List String → CommandElabM (TSyntax `term)
  | [] => `([])
  | item :: rest => do
      let item := Syntax.mkStrLit item
      let rest ← stringListSyntax rest
      `($item :: $rest)

private def checkpointListSyntax : List Checkpoint → CommandElabM (TSyntax `term)
  | [] => `([])
  | checkpoint :: rest => do
      let checkpoint ← checkpointSyntax checkpoint
      let rest ← checkpointListSyntax rest
      `($checkpoint :: $rest)

private def snapshotSyntax (snap : Snapshot) : CommandElabM (TSyntax `term) := do
  let theoremName := Syntax.mkStrLit snap.theoremName
  let goal := Syntax.mkStrLit snap.goal
  let checkpoints ← checkpointListSyntax snap.checkpoints
  let runes ← stringListSyntax snap.runes
  let nextMoves ← stringListSyntax snap.nextMoves
  let notes ← stringListSyntax snap.notes
  `(ACL2.ProofMode.Snapshot.mk $theoremName $goal $checkpoints $runes $nextMoves $notes)

syntax (name := aclPanelCmd) "#acl_panel " ident : command
syntax (name := aclImportedPanelCmd) "#acl_imported_panel " str str : command
syntax (name := aclHintPanelCmd) "#acl_hint_panel " str str : command

@[command_elab aclPanelCmd]
def elabAclPanel : CommandElab := fun stx => do
  let `( #acl_panel $id:ident ) := stx | throwUnsupportedSyntax
  let (nameStr, goalStr) ← liftTermElabM do
    let declName ← realizeGlobalConstNoOverloadWithInfo id
    let info ← getConstInfo declName
    let typeFmt ← Meta.ppExpr info.type
    pure (declName.toString, typeFmt.pretty)
  let nameLit := Syntax.mkStrLit nameStr
  let goalLit := Syntax.mkStrLit s!"Type:\n{goalStr}"
  elabCommand (← `(#html ACL2.ProofMode.panelForGoal $nameLit $goalLit))

@[command_elab aclImportedPanelCmd]
def elabAclImportedPanel : CommandElab := fun stx => do
  let path := stx[1]
  let theoremStx := stx[2]
  let some pathStr := path.isStrLit?
    | throwError "expected a string literal ACL2 book path"
  let some theoremStr := theoremStx.isStrLit?
    | throwError "expected a string literal ACL2 theorem name"
  let snap ← liftIO do
    importedSnapshotFromFile pathStr theoremStr
  match snap with
  | .error err => throwError err
  | .ok snap =>
      let snapTerm ← snapshotSyntax snap
      elabCommand (← `(#html ACL2.ProofMode.render $snapTerm))

@[command_elab aclHintPanelCmd]
def elabAclHintPanel : CommandElab := fun stx => do
  let path := stx[1]
  let theoremStx := stx[2]
  let some pathStr := path.isStrLit?
    | throwError "expected a string literal ACL2 book path"
  let some theoremStr := theoremStx.isStrLit?
    | throwError "expected a string literal ACL2 theorem name"
  let snap ← liftIO do
    dynamicSnapshotForPanel pathStr theoremStr
  let snapTerm ← snapshotSyntax snap
  elabCommand (← `(#html ACL2.ProofMode.render $snapTerm))

end ProofMode
end ACL2
