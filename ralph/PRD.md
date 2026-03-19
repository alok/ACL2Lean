# ACL2Lean Autoresearch PRD

## Mission

Use Lean's kernel as the checker for imported ACL2 theorems.

The concrete end-state to optimize toward is:

- take an existing ACL2 book or theorem,
- import enough proof information to replay it in Lean,
- end with a native Lean theorem term, not just an ACL2-side success report,
- keep the result inspectable in both `lean-tui` and the custom ACL infoview panel.

## Current baseline

The repo already has:

- ACL2 parser/import/evaluator/translator scaffolding
- evaluator checks against ACL2 for basic expressions plus `flog2` / `clog2`
- `lean-tui` + `LeanPrism` installed
- a first ProofWidgets infoview panel in `ACL2Lean/ProofMode.lean`
- a theorem-aware `#acl_panel` command
- notes on `Sym` / `grind` extension points in `docs/acl-proof-mode.md`

## Operating mode

Do not scope yourself so tightly that you finish early and idle.

Treat this as a 10-hour autonomous engineering/research loop with one north star and multiple active workstreams.

The north star is still:

- import existing ACL2 proofs and replay them in Lean so Lean's kernel checks the result and the output is a native Lean theorem.

But you should self-manage across the whole dependency graph required to get there. If one lane blocks, immediately pivot to the next highest-leverage lane instead of stopping.

## Autonomous workstreams

At any point, pick the best next task from these tracks:

1. **Proof artifact extraction**
   - discover what ACL2 proof output, hints, proof trees, or source-level artifacts can be harvested and replayed
   - read ACL2 source/books/binary behavior as needed
2. **Replay infrastructure**
   - design and implement an import format or replay engine that turns ACL2 proof information into Lean proof terms or proof scripts
   - prefer checked-in Lean theorems as the end result
3. **Translator and import pipeline**
   - improve translation of `defthm`, hints, recursive definitions, and theorem dependencies
   - add CLI or file-generation workflows that make replay reproducible
4. **Lean proving support**
   - extend ACL-oriented tactics, `Sym`/`grind` integration, and helper lemmas
   - use Lean source directly to understand the right APIs/typeclasses
5. **Evaluator and semantics**
   - fix semantic mismatches against ACL2 that block proof replay or theorem checking
   - keep the ACL2 regression harness green
6. **UI / proof mode**
   - continue evolving `lean-tui` + infoview into an ACL proof mode that helps inspect imported/replayed proofs
7. **Research and documentation**
   - write down what ACL2 exposes, what replay formats seem viable, and what still blocks full replay
   - keep the progress log useful for a human returning later

## Execution policy

- Always work on the most leverage-positive task available, not necessarily the one originally started.
- If you hit a blocker after a reasonable attempt, pivot instead of stopping.
- Keep a rolling backlog in the progress log.
- Make commits and push checkpoints when you have something real.
- Never conclude early just because one narrow objective is blocked or "done enough".

## Priority order

1. Demonstrate real Lean-kernel-checked replay/import on a small ACL2 theorem.
2. Make the replay/import path reproducible from CLI or checked-in Lean files.
3. Strengthen the supporting stack that most increases the chance of larger theorem replay next.
4. Improve the ACL proof-mode UI so it reflects real replay state, not just static scaffolding.

## Constraints

- Follow repo instructions in `AGENTS.md`.
- Use `uv` for Python workflows.
- Keep working on a branch you control, never on `main`.
- Commit and push useful checkpoints.
- Prefer small, verifiable steps over speculative refactors.
- Do not break the existing evaluator regression flow.

## Deliverables to chase during the loop

- a documented proof-artifact extraction strategy for ACL2
- at least one imported theorem that is checked by Lean
- CLI and/or generated-file workflow for replaying imported proofs
- UI hooks that reflect real imported theorem/proof state instead of static placeholders

## Good first targets

- `acl2_samples/simple.lisp`
- small arithmetic/list lemmas that do not require heavy theory

## Nice-to-have

- use `Lean.Meta.Sym.Grind.Goal` APIs (`mkGoal`, `introN`, `simpIgnoringNoProgress`, `internalizeAll`, `Goal.grind`) to structure replay/checkpointing
- thread ACL rune/hint provenance into the infoview panel
