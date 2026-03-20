import Lean
import Lean.Data.Json
import ACL2Lean.Import
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
  | .enable items => items.map (fun item => s!"enable {item}")
  | .disable items => items.map (fun item => s!"disable {item}")
  | .e_d enabled disabled =>
      (enabled.map (fun item => s!"enable {item}")) ++
        (disabled.map (fun item => s!"disable {item}"))
  | .raw expr => [s!"theory {TheoryExpr.summary (.raw expr)}"]

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

end ProofMode
end ACL2
