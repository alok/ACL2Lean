import Lean
import ACL2Lean.Translator

open Lean
open Lean Elab Command Term

namespace ACL2
namespace ImportedRegistry

structure Entry where
  acl2Name : String
  declName : Name
  deriving Inhabited, Repr, DecidableEq

abbrev RegistryState := Std.HashMap String (List Entry)

def normalizeAcl2Name (name : String) : String :=
  let base :=
    match (name.splitOn "::").reverse with
    | head :: _ => head
    | [] => name
  let translated := Translator.translateSymbol { name := base }
  let sanitized := Translator.sanitizeName translated
  sanitized.map Char.toLower

private def addEntryToState (state : RegistryState) (entry : Entry) : RegistryState :=
  let key := normalizeAcl2Name entry.acl2Name
  let existing := state.getD key []
  let updated :=
    if existing.any (·.declName == entry.declName) then
      existing
    else
      entry :: existing
  state.insert key updated

initialize ext : SimplePersistentEnvExtension Entry RegistryState ←
  registerSimplePersistentEnvExtension {
    name := `acl2ImportedRegistry
    addImportedFn := fun imported =>
      imported.foldl
        (fun state entries => entries.foldl addEntryToState state)
        {}
    addEntryFn := addEntryToState
  }

syntax (name := acl2ImportedCmd) "acl2_imported " str ident : command

@[command_elab acl2ImportedCmd]
def elabAcl2Imported : CommandElab := fun stx => do
  let acl2NameStx := stx[1]
  let declStx := stx[2]
  let some acl2Name := acl2NameStx.isStrLit?
    | throwErrorAt acl2NameStx "expected a string literal ACL2 theorem name"
  let declName ← liftTermElabM <| realizeGlobalConstNoOverloadWithInfo declStx
  match (← getEnv).find? declName with
  | some (.thmInfo ..) =>
      modifyEnv fun env => ext.addEntry env { acl2Name, declName }
  | _ =>
      throwErrorAt declStx "`acl2_imported` can only register theorems"

structure Snapshot where
  entries : RegistryState := {}
  deriving Inhabited, Repr

def ofEntries (entries : List Entry) : Snapshot :=
  { entries := entries.foldl addEntryToState {} }

def snapshot (env : Environment) : Snapshot :=
  { entries := ext.getState env }

def resolve (snapshot : Snapshot) (acl2Name : String) : List Name :=
  (snapshot.entries.getD (normalizeAcl2Name acl2Name) []).reverse.map (·.declName)

private def projectSearchPath : IO SearchPath := do
  let appDir ← IO.appDir
  let some buildDir := appDir.parent
    | pure []
  let some lakeDir := buildDir.parent
    | pure []
  let some projectRoot := lakeDir.parent
    | pure []
  let localLib := projectRoot / ".lake" / "build" / "lib" / "lean"
  let packagesDir := projectRoot / ".lake" / "packages"
  let mut searchPath : SearchPath := []
  if ← packagesDir.isDir then
    for pkg in ← packagesDir.readDir do
      let packageLib := pkg.path / ".lake" / "build" / "lib" / "lean"
      if ← packageLib.isDir then
        searchPath := searchPath ++ [packageLib]
  if ← localLib.isDir then
    searchPath := searchPath ++ [localLib]
  pure searchPath

def loadRuntimeSnapshot : IO Snapshot := do
  initSearchPath (← findSysroot) (← projectSearchPath)
  let env ← importModules #[{ module := `ACL2Lean }] {} (loadExts := true)
  pure (snapshot env)

private def entryTerm (entry : Entry) : CommandElabM (TSyntax `term) := do
  let acl2Name := Syntax.mkStrLit entry.acl2Name
  let declName := Lean.quote entry.declName
  `(ACL2.ImportedRegistry.Entry.mk $acl2Name $declName)

private def entryListTerm : List Entry → CommandElabM (TSyntax `term)
  | [] => `([])
  | entry :: rest => do
      let entry ← entryTerm entry
      let rest ← entryListTerm rest
      `($entry :: $rest)

syntax (name := emitAcl2ImportSnapshotCmd) "emit_acl2_import_snapshot " ident : command

@[command_elab emitAcl2ImportSnapshotCmd]
def elabEmitAcl2ImportSnapshot : CommandElab := fun stx => do
  let target := stx[1]
  let snap := snapshot (← getEnv)
  let entries :=
    snap.entries.toList.foldl
      (fun acc (_, values) => values.reverse ++ acc)
      []
  let entriesTerm ← entryListTerm entries
  elabCommand
    (← `(def $(mkIdent target.getId) : ACL2.ImportedRegistry.Snapshot :=
          ACL2.ImportedRegistry.ofEntries $entriesTerm))

#guard normalizeAcl2Name "NBR-CALLS-FLOG2-UPPER-BOUND" = "nbr_calls_flog2_upper_bound"
#guard normalizeAcl2Name "nbr-calls-clog2=1+clog2" = "nbr_calls_clog2_eq_1_plus_clog2"
#guard normalizeAcl2Name "ACL2::POSP" = "posp"

private def demoSnapshot : Snapshot :=
  { entries :=
      ({} : RegistryState).insert
        (normalizeAcl2Name "NBR-CALLS-FLOG2-UPPER-BOUND")
        [{ acl2Name := "NBR-CALLS-FLOG2-UPPER-BOUND"
           declName := `ACL2.Imported.Log2Replay.nbr_calls_flog2_upper_bound }]
  }

#guard resolve demoSnapshot "nbr-calls-flog2-upper-bound" = [`ACL2.Imported.Log2Replay.nbr_calls_flog2_upper_bound]

end ImportedRegistry
end ACL2
