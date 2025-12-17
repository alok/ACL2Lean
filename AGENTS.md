# Repository Guidelines

## Project Structure & Module Organization
This Lean 4 project is managed by Lake. `Main.lean` in the root is the executable entry point; keep it thin and delegate logic to library modules. Place shared code in `ACL2Lean/` (currently `Basic.lean` exposes `hello`) and export new modules through `ACL2Lean.lean`. Store experiments or notes in clearly named folders outside the library namespace.

## Build, Test, and Development Commands
- `lake build` — type-checks all Lean files and refreshes artifacts; run after any library change.
- `lake exe Main` — builds and runs the main program, handy for verifying IO demos.
- `lake clean` — removes build outputs when troubleshooting stale results.
- `lake env lean --server` — starts the Lean language server for editor integrations.

## Coding Style & Naming Conventions
Use Lean community conventions: lemmas and defs in `lowerCamelCase`, structures/types in `UpperCamelCase`, namespaces in `PascalCase`. Indent tactic blocks and nested `do` expressions by two spaces. Prefer structured tactic blocks (`simp`, `rw`, `apply`, etc.) over long semicolon chains, and comment only when the reasoning is non-obvious. Update `ACL2Lean.lean` with `open` or `export` statements when adding modules so downstream imports stay clean.

## Testing Guidelines
Compilation is the first safety net: every `example`, lemma, and `#eval` must succeed under `lake build`. Colocate small property checks near the code they exercise, and gate runnable demos behind IO functions that can be executed with `lake exe`. As the project grows, consider a `Tests/` namespace populated with scenario modules that import the library and confirm tactics still solve the intended goals.

## Commit & Pull Request Guidelines
With no history yet, adopt short imperative commit headers (e.g., `Add ACL2 bridge skeleton`) and group related edits per commit. Pull requests should describe the problem, the solution, any new namespaces or automation, and link issues or build transcripts. Request review only after `lake build` and `lake exe` succeed and new modules are reachable from `ACL2Lean.lean`.

## Lean Tooling Tips
Stay on the pinned toolchain recorded in `lean-toolchain`; run `lake update` only when coordinating version bumps. Use `rg` or `lake env ast-grep` to locate identifiers before creating duplicates, and rely on sorry placeholders while sketching proofs—remove them before merging.
