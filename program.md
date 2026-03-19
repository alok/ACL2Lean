# autoresearch

This repo is running in an autoresearch-style autonomous engineering loop.

The point is not to work one tiny task to completion and then idle. The point is
to keep moving the whole codebase forward for a long unattended run, while
keeping a clear north star.

## North star

Use Lean's kernel as the checker for imported ACL2 theorems.

The desired end state is:

- import an existing ACL2 theorem and as much of its proof information as is useful,
- replay or reconstruct that proof in Lean,
- end with a native Lean theorem term checked by Lean,
- keep the path reproducible and inspectable.

## Current baseline

The repo already has:

- ACL2 parser/import/evaluator/translator scaffolding
- evaluator checks against ACL2, including contextual `flog2` / `clog2` tests
- a first ACL proof-mode UI using `lean-tui`, `LeanPrism`, and ProofWidgets
- theorem-aware infoview panel support via `#acl_panel`
- notes on Lean 4.29 `Sym` / `grind` extension points in `docs/acl-proof-mode.md`

## Read these first

Before acting in any fresh iteration, read enough of these for context:

- `README.md`
- `ACL2_SPEC.md`
- `docs/acl-proof-mode.md`
- `Verify.py`
- `ACL2Lean/Syntax.lean`
- `ACL2Lean/Parser.lean`
- `ACL2Lean/Import.lean`
- `ACL2Lean/Translator.lean`
- `ACL2Lean/Logic.lean`
- `ACL2Lean/Evaluator.lean`
- `ACL2Lean/Tactics.lean`
- `ACL2Lean/ProofMode.lean`
- `ACL2Lean/ProofModeDemo.lean`
- relevant files in `acl2_samples/`

Also read ACL2 and Lean source material as needed. Using the ACL2 binary and the
Lean source tree is in scope.

## Autonomous workstreams

Do not scope yourself so tightly that you finish early and starve the run.

At every step, pick the highest-leverage task from these workstreams:

1. **ACL2 proof artifact extraction**
   - find what ACL2 can expose: proof trees, checkpoints, hints, events, traces, source-level proof structure
   - use ACL2 binaries and ACL2 source code as needed
2. **Proof replay infrastructure**
   - design a replay format or importer
   - generate Lean proof scripts or proof terms
   - build a checker/replayer around Lean
3. **Translator/import pipeline**
   - improve theorem/dependency import
   - better preserve hints, recursive structure, theorem metadata, and proof-relevant annotations
4. **Lean theorem support**
   - strengthen helper lemmas and tactics
   - use `Sym` / `grind` APIs when they increase replay success
5. **Semantic alignment**
   - fix evaluator or logic mismatches that block proof replay or theorem checking
   - keep ACL2 regression checks green
6. **UI / proof mode**
   - make the ACL proof-mode panel and `lean-tui` reflect real imported/replayed theorem state
7. **Documentation / research notes**
   - keep a clear record of what works, what failed, and what to try next

If one lane blocks, pivot immediately to another useful lane. Do not wait for the user.

## Mainline promotion policy

This repo now has two distinct responsibilities:

- the `autoresearch/...` branch is allowed to be rough, experimental, and ahead of itself
- `main` should receive stable, useful increments over time

Your job is not to dump every research commit onto `main`.
Your job is to continuously judge which parts of the research branch deserve promotion.

When you have a batch of changes that is:

- self-contained,
- clearly useful,
- verified enough for its scope,
- and unlikely to be invalidated by the next hour of rough exploration,

then promote that batch to `main`.

### How to promote

1. Stay on the research branch while exploring.
2. When a set of commits or a coherent change is main-worthy:
   - identify the exact commits or recreate the minimal clean patch
   - switch to `main`
   - cherry-pick or reapply only the stable subset
   - run the relevant checks
   - commit if needed
   - push `main`
   - switch back to the research branch and continue

### Promotion cadence

- Do **not** promote every commit.
- Do promote incrementally whenever there is a real, stable slice worth saving to `main`.
- Favor fewer, cleaner mainline promotions over noisy main history.
- If unsure, leave work on the research branch until the boundary is clearer.

### What belongs on `main`

Usually worthy:

- reproducible tooling improvements
- stable parser/import/evaluator fixes
- generally useful proof infrastructure
- working UI/proof-mode improvements
- documentation that captures real findings
- imported Lean theorems or replay infrastructure that actually checks

Usually not yet worthy:

- half-working experiments
- changes that currently fail the build
- speculative rewrites without verification
- temporary hacks that are likely to be replaced soon

## Allowed changes

You may modify any repo files that help move toward the north star.

Prefer:

- small, verifiable changes
- checked-in scripts or docs that make replay reproducible
- commits that preserve working checkpoints

Avoid:

- speculative refactors with no verification
- breaking the existing evaluator checks without replacing them
- waiting for more instructions

## Verification baseline

Use these often:

- `lake build`
- `lake build <specific targets>`
- `uv run python Verify.py`
- direct ACL2 invocations for ground-truth behavior

## Logging

Maintain:

- `AUTORESEARCH_PROGRESS.md`
- `results.tsv`

Update them every iteration with:

- what you changed
- what you verified
- whether the iteration was a keep / discard / crash
- what the next best ideas are

## results.tsv format

Tab-separated, with this header:

`timestamp	commit	status	focus	checks	notes`

Status should be one of:

- `keep`
- `discard`
- `crash`

## Loop

LOOP FOREVER until externally interrupted:

1. Inspect current branch/commit and recent progress.
2. Choose the single highest-leverage task right now.
3. Implement it end-to-end.
4. Run the most relevant checks.
5. Commit if it is a real advance.
6. Push useful checkpoints.
7. Append concise progress and result entries.
8. Repeat immediately.

If an iteration is bad or inconclusive, revert or discard it and keep moving.

Never stop just because one subproblem is blocked.
