import ACL2Lean
import Lean

open Lean Meta ACL2

def main : IO Unit := do
  initSearchPath (← getLeanPath)
  let env ← importModules #[{ module := `ACL2Lean }] {}
  let coreCtx : Core.Context := { fileName := "test", fileMap := { source := "", positions := #[] } }
  let coreState : Core.State := { env := env }
  
  let _ ← coreCtx.toIO (m := Core.CoreM) coreState do
    MetaM.run' do
      let one ← mkAppM ``SExpr.atom #[← mkAppM ``Atom.number #[← mkAppM ``Number.int #[← mkAppM ``Int.ofNat #[mkRawNatLit 1]]]]
      let two ← mkAppM ``SExpr.atom #[← mkAppM ``Atom.number #[← mkAppM ``Number.int #[← mkAppM ``Int.ofNat #[mkRawNatLit 2]]]]
      let expr ← mkAppM ``Logic.plus #[one, two]
      let pp ← ppExpr expr
      IO.println s!"Pretty printed: {pp}"
