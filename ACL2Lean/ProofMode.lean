import Lean
import Lean.Data.Json
import ProofWidgets.Component.HtmlDisplay

open Lean
open Lean.Json
open ProofWidgets

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

end ProofMode
end ACL2
