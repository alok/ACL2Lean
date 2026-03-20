# Autoresearch Progress

## 2026-03-19 Baseline

Known-good starting point:

- branch: `autoresearch/mar19-acl2lean`
- theorem-aware ACL infoview panel exists
- `lean-tui` / `LeanPrism` integration exists
- `lake build ACL2Lean.ProofMode ACL2Lean.ProofModeDemo Main` passes
- `uv run python Verify.py` matches ACL2 on the current regression set

Current north star:

- import existing ACL2 proofs and replay them in Lean so Lean's kernel is the checker

Initial backlog:

1. figure out what proof artifacts ACL2 can expose in a replay-friendly form
2. replay one small theorem from `acl2_samples/simple.lisp` or another tiny sample as a Lean theorem
3. build the infrastructure that most increases the chance of scaling replay
4. connect imported/replayed proof state to the ACL proof-mode UI

User direction update:

- the loop should also determine which stable slices belong on `main`
- do not mirror every rough research commit onto `main`
- promote stable, verified batches incrementally while keeping rough work on the research branch

## 2026-03-19 Iteration 1

Completed this iteration:

- normalized parsed ACL2 symbol names to lowercase and package qualifiers to uppercase so imported names match ACL2's case-insensitive reader model more closely
- added `Symbol.isNamed` and used it to make evaluator/translator handling of `quote`, `if`, and `let` case-insensitive even when syntax is constructed outside the parser
- added build-covered mixed-case regressions in `ACL2Lean/Parser.lean`, `ACL2Lean/Translator.lean`, and `ACL2Lean/Evaluator.lean`
- extended `Verify.py` with ACL2-backed mixed-case checks, including imported `FLOG2` / `CLOG2` lookups from `acl2_samples/2009-log2.lisp`

Verification:

- research branch commit `ba78e78`: `lake build`
- research branch commit `ba78e78`: `uv run python Verify.py`
- promoted the stable slice to `main` as `9c78e31`
- on `main`, a stale read-only `.lake/build` artifact blocked the first build; after `lake clean`, both `lake build` and `uv run python Verify.py` passed

Outcome:

- keep
- promoted to `main`

Next best ideas:

1. preserve original ACL2 symbol spellings alongside normalized lookup names so proof extraction can display source-faithful theorem/rune names without reintroducing lookup bugs
2. import more proof-relevant theorem metadata from `defthm` hints and `in-theory` events instead of only storing theorem bodies
3. replay a slightly richer imported theorem with locals/hints and connect that metadata to the proof-mode UI

## 2026-03-19 Iteration 2

Completed this iteration:

- replaced raw `defthm` hint blobs with structured theorem metadata (`TheoremInfo`, `GoalHint`, `RuleClass`, `TheoryExpr`) so imported ACL2 theorems now preserve `:hints`, `:rule-classes`, and `:in-theory` data in a replay-friendly form
- changed `World` to retain theorem metadata plus replay-order top-level theory events instead of only theorem bodies
- taught the translator to emit ACL2 metadata comments and top-level `in-theory` comments in generated Lean output, preserving proof-relevant context next to imported theorems
- added `acl2lean metadata <file> [theorem]` for inspecting extracted theorem metadata directly from sample books
- added parser regression guards for theorem options and `in-theory` parsing, and updated the ACL2 spec / proof-mode notes to reflect the new import surface

Verification:

- research branch commit `fc0f984`: `lake build`
- research branch commit `fc0f984`: `uv run python Verify.py`
- research branch commit `fc0f984`: `./.lake/build/bin/acl2lean metadata acl2_samples/2009-log2.lisp clog2-lemma-a`
- research branch commit `fc0f984`: `./.lake/build/bin/acl2lean metadata acl2_samples/2009-log2.lisp`
- research branch commit `fc0f984`: `./.lake/build/bin/acl2lean translate acl2_samples/2009-log2.lisp | rg -n "ACL2 metadata|ACL2 in-theory|rule-classes"`

Outcome:

- keep
- not promoted to `main` yet

Notes:

- the new metadata path works on top-level theorem-rich books like `acl2_samples/2009-log2.lisp`
- `acl2_samples/apply-model-apply-prim.lisp` still does not surface deeper `encapsulate`-scoped theorem metadata such as `badge-prim-type`, so mainline promotion should wait for better nested-event coverage

Next best ideas:

1. make theorem metadata inspection and translation recurse cleanly through more `encapsulate` / `local` / `make-event` shapes in books like `apply-model-apply-prim.lisp`
2. parse richer hint subforms such as `:instructions`, `:cases`, and nested theory combinators so replay can use more than just `:use` / `:in-theory`
3. connect extracted `GoalHint` and `TheoryExpr` data to `ACL2Lean.ProofMode` so the widget shows imported rune/hint provenance instead of only demo data

## 2026-03-19 Iteration 3

Completed this iteration:

- added best-effort static `make-event` recovery by dequasiquoting generated event skeletons and exposing them through shared `Event.generatedEvents` / `Event.flattenList` helpers
- taught `Event.classify` to unwrap `with-output` wrappers so nested events inside generated books survive classification instead of collapsing to `skip`
- updated `World.step` and the `acl2lean metadata` / `acl2lean translate` CLI paths to consume the shared flattening logic, so recovered generated events participate in replay-oriented inspection
- added build-time regression guards for wrapped `defthm` events and quasiquoted `make-event` encapsulates, and updated `ACL2_SPEC.md` to document the expanded import surface

Verification:

- research branch commit `84ceff5`: `lake build`
- research branch commit `84ceff5`: `uv run python Verify.py`
- research branch commit `84ceff5`: `./.lake/build/bin/acl2lean metadata acl2_samples/apply-model-apply-prim.lisp | sed -n '1,80p'`
- research branch commit `84ceff5`: `./.lake/build/bin/acl2lean metadata acl2_samples/apply-model-apply-prim.lisp 'apply$-prim-meta-fn-correct'`
- research branch commit `84ceff5`: `./.lake/build/bin/acl2lean translate acl2_samples/apply-model-apply-prim.lisp | sed -n '48,80p'`
- promoted the stable metadata batch to `main` as `0a2fa23` + `5a5caf6`
- on `main`, a stale read-only `.lake` artifact broke the first `lake build`; after `lake clean`, both `lake build` and `uv run python Verify.py` passed
- on `main`, `./.lake/build/bin/acl2lean metadata acl2_samples/apply-model-apply-prim.lisp 'apply$-prim-meta-fn-correct'` passed and showed the recovered meta theorem metadata

Outcome:

- keep
- promoted to `main`

Notes:

- `acl2_samples/apply-model-apply-prim.lisp` now surfaces the deeper generated theorems `n-car-cadr-caddr-etc-opener`, `apply$-prim-meta-fn-correct`, and `apply$-primp-implies-symbolp`, which unblocks promotion of the earlier structured-metadata work
- theorem lookup from the shell needs quoting around `$`-bearing ACL2 names, but the CLI lookup path itself works correctly once the shell does not mangle the theorem name

Next best ideas:

1. parse `:instructions`, `:cases`, and richer nested theory expressions into structured metadata instead of only preserving them as raw extra options
2. extend static recovery beyond direct quasiquote skeletons to dynamic-but-still-inspectable `make-event` result shapes such as `value` / `er-progn` branches
3. feed the recovered theorem metadata into `ACL2Lean.ProofMode` so imported books drive the infoview panel instead of the current demo snapshot

## 2026-03-19 Iteration 4

Completed this iteration:

- added a structured `ProofInstruction` tree to theorem metadata import so ACL2 `:instructions` are no longer opaque extra options
- taught the importer to recognize nested proof-builder blocks like `quiet!` / `:repeat` while keeping command arguments available for later replay
- added reusable rendering helpers so `acl2lean metadata` and translated Lean theorem comments now show proof-builder structure for imported theorems such as `apply$-prim-meta-fn-correct`
- added parser regression coverage for a real proof-builder script drawn from `acl2_samples/apply-model-apply-prim.lisp`
- updated the ACL2 spec to treat structured proof-builder instructions as the next replay seam instead of just a future parsing TODO

Verification:

- research branch commit `b3440b8`: `lake build`
- research branch commit `b3440b8`: `uv run python Verify.py`
- research branch commit `b3440b8`: `./.lake/build/bin/acl2lean metadata acl2_samples/apply-model-apply-prim.lisp 'apply$-prim-meta-fn-correct'`
- research branch commit `b3440b8`: `./.lake/build/bin/acl2lean translate acl2_samples/apply-model-apply-prim.lisp | sed -n '48,95p'`
- promoted the stable code slice to `main` as `bcfb1a4`
- on `main`, a stale read-only `.lake` artifact from the older toolchain broke the first build; after `lake clean`, `lake build` passed
- on `main`, `uv run python Verify.py` passed after rebuilding
- on `main`, `./.lake/build/bin/acl2lean metadata acl2_samples/apply-model-apply-prim.lisp 'apply$-prim-meta-fn-correct'` passed and showed the imported proof-builder structure

Outcome:

- keep
- promoted to `main`

Notes:

- the promoted `main` slice excluded `docs/acl-proof-mode.md` because `main` currently does not carry the proof-mode files that exist on the research branch
- this is the first imported ACL2 proof artifact in the repo that is closer to replay than presentation: the metadata path now preserves a navigable script skeleton instead of a raw s-expression blob

Next best ideas:

1. interpret the imported `ProofInstruction` tree for a tiny replay prototype, starting with `quiet!`, `:bash`, `:in-theory`, and `:repeat :prove`
2. parse additional hint metadata such as `:cases` and more nested theory combinators so more ACL2 books import replay-relevant structure cleanly
3. feed the imported instruction tree into `ACL2Lean.ProofMode` so the infoview can show real theorem steps rather than the current demo snapshot

## 2026-03-19 Iteration 5

Completed this iteration:

- taught `ACL2Lean.ProofMode` to derive a real widget `Snapshot` from imported `TheoremInfo` plus the preceding top-level ACL2 `in-theory` context instead of only using the hard-coded demo props
- added `#acl_imported_panel "<book>" "<theorem>"`, which loads an ACL2 book during elaboration and renders an imported-theorem proof-mode panel
- updated `ACL2Lean/ProofModeDemo.lean` to exercise the new path on `acl2_samples/apply-model-apply-prim.lisp` / `apply$-prim-meta-fn-correct`
- updated `README.md`, `ACL2_SPEC.md`, and `docs/acl-proof-mode.md` so the imported-panel path is part of the documented replay/UI seam

Verification:

- research branch commit `77052ac`: `lake build ACL2Lean.ProofMode ACL2Lean.ProofModeDemo Main`
- research branch commit `77052ac`: `lake build`
- research branch commit `77052ac`: `uv run python Verify.py`
- research branch commit `77052ac`: `./.lake/build/bin/acl2lean metadata acl2_samples/apply-model-apply-prim.lisp 'apply$-prim-meta-fn-correct' | sed -n '1,80p'`

Outcome:

- keep
- not promoted to `main` yet

Notes:

- proof-mode now displays imported checkpoints, runes/facts, and next-move suggestions from a real ACL2 theorem instead of only the synthetic `demoSnapshot`
- the imported panel is still a replay plan view, not checked replay state: long `union-theories` / `set-difference-theories` forms still surface as raw summaries, and the steps are not yet being executed against Lean goals

Next best ideas:

1. interpret `:bash`, `:in-theory`, and `:repeat :prove` against real Lean goals so the imported panel can report checked replay progress
2. parse richer nested theory combinators so the rune pane can decompose `union-theories` / `set-difference-theories` / `current-theory` instead of dumping raw expressions
3. connect the imported snapshot path to live tactic-state updates so the panel can mix imported ACL2 provenance with actual Lean checkpoint state

## 2026-03-19 Iteration 6

Completed this iteration:

- extended `TheoryExpr` so imported ACL2 theory metadata now preserves nested theory combinators and theory-set constructors, including quoted literal rune sets, `union-theories`, `set-difference-theories`, `current-theory`, `function-theory`, and `cons`
- added structured rendering helpers for theory trees and hint lines, then threaded them through `ProofInstruction` rendering so imported `:bash` / `:in-theory` steps are inspectable as trees instead of raw ACL2 s-expressions
- updated the `acl2lean metadata` CLI, translated Lean metadata comments, and `ACL2Lean.ProofMode` rune list to surface the decomposed theory context from real books such as `acl2_samples/apply-model-apply-prim.lisp`
- added a parser guard for `set-difference-theories` with `current-theory` / `function-theory` and documented the richer theory-expression coverage in `README.md`, `ACL2_SPEC.md`, and `docs/acl-proof-mode.md`

Verification:

- research branch commit `c9efe09`: `lake build ACL2Lean.Parser ACL2Lean.ProofMode Main`
- research branch commit `c9efe09`: `lake build`
- research branch commit `c9efe09`: `uv run python Verify.py`
- research branch commit `c9efe09`: `./.lake/build/bin/acl2lean metadata acl2_samples/apply-model-apply-prim.lisp 'apply$-prim-meta-fn-correct' | sed -n '1,120p'`
- research branch commit `c9efe09`: `./.lake/build/bin/acl2lean translate acl2_samples/apply-model-apply-prim.lisp | sed -n '48,115p'`

Outcome:

- keep
- not promoted to `main` yet

Notes:

- this is a real replay-facing improvement because the imported theorem path now exposes nested ACL2 theory structure in a form Lean-side tooling can inspect, rather than hiding it behind raw strings
- I did not promote this slice to `main` yet because the proof-mode consumer for the new rendering still depends on the earlier imported-panel batch that remains only on the research branch; promotion should likely bundle those stable UI commits together

Next best ideas:

1. interpret the structured `TheoryExpr` tree into a Lean-side active rune / simp-set model so imported `:in-theory` can affect checked replay instead of only display
2. parse `:cases` and other still-unstructured hint options so more ACL2 proof metadata becomes replay-usable
3. replace the imported panel's planned checkpoints with checked replay state by executing `:bash`, `:in-theory`, and `:repeat :prove` against Lean goals

## 2026-03-19 Iteration 7

Completed this iteration:

- added `ACL2Lean/Imported/Log2Replay.lean`, a new module that reconstructs ACL2 theorem `nbr-calls-clog2=1+clog2` from `acl2_samples/2009-log2.lisp` as a native Lean theorem over the `SExpr` encoding
- introduced a proof-friendly `Nat` semantic mirror for the positive-integer execution path of imported `clog2` / `nbrCallsClog2`, then used it to prove the imported theorem instead of leaving another translated `sorry`
- added build-time `#guard` checks for representative imported values from the ACL2 book, including `clog2 10 = 4` and `nbrCallsClog2 17 = 6`
- exported the new module through `ACL2Lean.lean` and updated `README.md` / `ACL2_SPEC.md` so the repo now documents a real kernel-checked imported theorem checkpoint

Verification:

- research branch commit `f7559ac`: `lake build ACL2Lean.Imported.Log2Replay`
- research branch commit `f7559ac`: `lake build`
- research branch commit `f7559ac`: `uv run python Verify.py`
- research branch commit `f7559ac`: `./.lake/build/bin/acl2lean eval-in acl2_samples/2009-log2.lisp "(clog2 10)"`
- research branch commit `f7559ac`: `./.lake/build/bin/acl2lean eval-in acl2_samples/2009-log2.lisp "(nbr-calls-clog2 17)"`
- pushed research branch commit `f7559ac` to `origin/autoresearch/mar19-acl2lean`
- promoted the stable slice to `main` as `87f1687`
- on `main`, the first `lake build` hit the same stale read-only `.lake` artifact issue seen in earlier promotions; after `lake clean`, both `lake build` and `uv run python Verify.py` passed

Outcome:

- keep
- promoted to `main`

Notes:

- this is the first imported ACL2 theorem in the repo that is actually checked by Lean's kernel rather than only translated, rendered, or preserved as metadata
- the proof is a reconstruction, not yet generic replay: it lowers the imported theorem's positive-integer path to a small `Nat` model and then lifts the result back to the ACL2 `SExpr` statement
- the `Log2Replay` module is intentionally narrow, but it establishes a concrete pattern for turning computational ACL2 theorems into real Lean theorems without waiting for the full proof-mode / instruction-replay pipeline

Next best ideas:

1. generalize the `Log2Replay` lowering pattern into reusable infrastructure so more imported ACL2 theorems can reconstruct through proof-friendly semantic mirrors
2. connect imported hint / instruction metadata to these reconstructions so the next checked theorem uses real ACL2 proof artifacts instead of only theorem statements
3. prove one more small imported theorem from `acl2_samples/2009-log2.lisp` or `acl2_samples/die-hard-work.lisp` to test whether the new pattern scales beyond a single hand-held example

## 2026-03-19 Iteration 8

Completed this iteration:

- extended `ACL2Lean/Imported/Log2Replay.lean` from a single call-count theorem into a checked `clog2` theorem cluster covering `natp-clog2`, `posp-clog2`, `clog2-is-correct-lower`, `clog2-is-correct-upper`, `clog2-is-correct`, and the existing `nbr-calls-clog2=1+clog2`
- factored the positive-input replay path into reusable `Nat` lemmas (`clog2Nat_pos`, `self_le_two_pow_clog2Nat`, `two_pow_pred_clog2Nat_lt_self`) plus imported `expt` normalization helpers for replaying ACL2 inequalities over the `SExpr` encoding
- removed an initial `native_decide` shortcut from the concrete `n = 1` branches after axiom checking showed it introduced generated native axioms, replacing it with ordinary kernel-checked reduction
- updated `README.md` and `ACL2_SPEC.md` so the repo now documents a small imported theorem bundle rather than a single isolated replay theorem

Verification:

- research branch commit `4bdd637`: `lake build ACL2Lean.Imported.Log2Replay`
- research branch commit `4bdd637`: namespaced `#print axioms` for `ACL2.Imported.Log2Replay.{natp_clog2,posp_clog2,clog2_is_correct_lower,clog2_is_correct_upper,clog2_is_correct,nbr_calls_clog2_eq_1_plus_clog2}` showed only standard axioms (`propext`, `Quot.sound`)
- research branch commit `4bdd637`: `lake build`
- research branch commit `4bdd637`: `uv run python Verify.py`
- research branch commit `4bdd637`: `./.lake/build/bin/acl2lean eval-in acl2_samples/2009-log2.lisp "(clog2 1)"`
- research branch commit `4bdd637`: `./.lake/build/bin/acl2lean eval-in acl2_samples/2009-log2.lisp "(clog2 17)"`
- research branch commit `4bdd637`: `./.lake/build/bin/acl2lean eval-in acl2_samples/2009-log2.lisp "(nbr-calls-clog2 17)"`
- pushed research branch commit `4bdd637` to `origin/autoresearch/mar19-acl2lean`
- promoted the stable slice to `main` as `2094b19`
- on `main`, `lake build` passed in a separate worktree
- on `main`, `uv run python Verify.py` passed in the promotion worktree

Outcome:

- keep
- promoted to `main`

Notes:

- this turns `Log2Replay` into the first imported ACL2 theorem bundle in the repo whose central bound theorem (`clog2-is-correct`) is checked by Lean’s kernel instead of being left as imported metadata or a translated `sorry`
- the positive-integer `Nat` mirror is still specialized to the `2009-log2.lisp` path, but it now captures enough reusable structure to replay more than one theorem from the book without starting over
- `acl2lean eval-in` still reports `unknown built-in or wrong arity: expt` on raw `(expt ...)` forms, so theorem-adjacent smoke tests currently have to go through imported book functions like `clog2` rather than ACL2’s exponentiation primitive directly

Next best ideas:

1. generalize the `Log2Replay` helper layer into reusable imported-theorem replay infrastructure so other numeric ACL2 books can reuse the same positive-integer lowering pattern
2. use the new `clog2` correctness bundle to replay one of the remaining `nbr-calls-flog2` theorems from `acl2_samples/2009-log2.lisp`, ideally reusing imported hint metadata instead of reconstructing everything by hand
3. extend the evaluator / `eval-in` built-in surface to support `expt` directly, so imported theorem smoke tests can execute the ACL2 bound statements themselves instead of only adjacent function calls

## 2026-03-19 Iteration 9

Completed this iteration:

- taught `scripts/acl2_hint_bridge.py` to run theorem extraction through explicit ACL2 load plans instead of assuming `(ld <sample>)` is always valid
- added resolution/fallback support for excerpted repo samples, including canonical upstream book fallback for `acl2_samples/die-hard-work.lisp` / `acl2_samples/die-hard-top.lisp` and upstream `MODAPP` portcullis preload support for the `apply-model` samples
- distinguished ACL2 load failures from ordinary theorem misses in the dynamic bridge so package/include errors surface as `failed` artifacts instead of silently collapsing to `not-found`
- extended the Lean-side `DynamicArtifact` schema, CLI rendering, and proof-mode notes to show the actual ACL2 book/load steps used by the dynamic bridge
- added unit coverage for load-plan resolution and failure classification, and documented the excerpted-sample fallback behavior in `README.md`

Verification:

- research branch commit `1cbf39a`: `uv run python scripts/test_acl2_hint_bridge.py`
- research branch commit `1cbf39a`: `uv run python scripts/acl2_hint_bridge.py --book acl2_samples/die-hard-work.lisp --theorem make-prog-correct`
- research branch commit `1cbf39a`: `lake build ACL2Lean.HintBridge ACL2Lean.ProofMode Main`
- research branch commit `1cbf39a`: `LAKE_NO_CACHE=1 lake build`
- research branch commit `1cbf39a`: `lake exe acl2lean hints acl2_samples/die-hard-work.lisp make-prog-correct`
- research branch commit `1cbf39a`: `uv run python Verify.py`

Outcome:

- keep
- not promoted to `main` yet

Notes:

- this is a real hint-generator-path advance because the ACL2 binary can now act as a usable theorem-local oracle on a previously broken excerpted sample instead of only on self-contained books like `2009-log2.lisp`
- `make-prog-correct` from the die-hard bottle-game path now reaches Lean with real ACL2-emitted warning kinds, hint-events, prover-step counts, and the resolved upstream source path
- a plain `lake build` initially failed in this environment because Lake could not write to the global artifact cache; rerunning with `LAKE_NO_CACHE=1` succeeded, so this was an environment/cache permission issue rather than a Lean regression
- I also added `MODAPP`/portcullis-aware fallback plans for `apply-model` samples, but I did not wait for a full end-to-end dynamic theorem extraction from that heavier path before checkpointing this slice

Next best ideas:

1. validate the new `MODAPP` load-plan path on `acl2_samples/apply-model-apply-prim.lisp` and surface dynamic artifacts for one of its generated theorems such as `n-car-cadr-caddr-etc-opener`
2. make the sample-to-canonical-book resolution table more data-driven so excerpted samples can advertise their upstream source/prelude requirements instead of relying on Python-side hardcoded cases
3. parse the dynamic `raw_excerpt` goal/subgoal lines into additional structured checkpoint entries so the bridge captures more of ACL2's actual proof search trace instead of only summary sections and explicit `A key checkpoint` blocks

## 2026-03-19 Iteration 10

Completed this iteration:

- promoted lightweight ACL2 `Goal'` / `Subgoal ...` transcript lines into structured dynamic checkpoints instead of leaving them trapped inside `raw_excerpt`
- extended the Lean-side `DynamicCheckpoint` schema and proof-mode rendering so dynamic hint panels now distinguish explicit ACL2 key checkpoints from raw goal/subgoal progress markers
- added parser coverage for raw goal/subgoal extraction and expanded the existing checkpoint regression to confirm explicit key checkpoints still coexist cleanly with the new raw-trace checkpoints
- updated `README.md`, `ACL2_SPEC.md`, and `docs/acl-proof-mode.md` so the dynamic hint bridge documentation now describes the raw-trace checkpoint path
- validated the heavier `MODAPP` load-plan path on `acl2_samples/apply-model-apply-prim.lisp` while exploring this slice, which confirmed the portcullis fallback works and exposed theorem-local scoping within large encapsulates as the next bridge issue

Verification:

- research branch commit `25f0904`: `uv run python scripts/test_acl2_hint_bridge.py`
- research branch commit `25f0904`: `uv run python scripts/acl2_hint_bridge.py --book acl2_samples/die-hard-work.lisp --theorem make-prog-correct`
- research branch commit `25f0904`: `LAKE_NO_CACHE=1 lake build ACL2Lean.HintBridge ACL2Lean.ProofMode Main`
- research branch commit `25f0904`: `lean-lsp-mcp` diagnostics on `ACL2Lean/HintBridge.lean` and `ACL2Lean/ProofMode.lean`
- research branch commit `25f0904`: `LAKE_NO_CACHE=1 lake build acl2lean`
- research branch commit `25f0904`: `./.lake/build/bin/acl2lean hints acl2_samples/die-hard-work.lisp make-prog-correct | sed -n '1,120p'`
- research branch commit `25f0904`: `uv run python Verify.py`
- exploratory validation during this iteration: `uv run python scripts/acl2_hint_bridge.py --book acl2_samples/apply-model-apply-prim.lisp --theorem 'n-car-cadr-caddr-etc-opener'`

Outcome:

- keep
- not promoted to `main` yet

Notes:

- `make-prog-correct` from the die-hard path now reaches Lean with eleven structured raw-trace checkpoints (`Goal'`, `Goal''`, and the emitted `Subgoal ...` chain) even though ACL2 did not emit a full `A key checkpoint` block for that theorem
- the targeted Lean builds and the `acl2lean` executable build passed, but a full `LAKE_NO_CACHE=1 lake build` in this environment still hit the existing toolchain artifact-cache permission failure on `ACL2Lean.ProofMode:c.o`; this remains an environment issue rather than a regression from the checkpoint changes
- validating `n-car-cadr-caddr-etc-opener` on the `apply-model` sample showed that the new `MODAPP`/portcullis load plan succeeds, but some collected observations/warnings still span more of the enclosing encapsulate than the single target theorem, so theorem-local transcript scoping is now the main open gap on the dynamic bridge path
- tracked this slice in Linear as `ALOK-549`

Next best ideas:

1. make theorem-section extraction in `scripts/acl2_hint_bridge.py` more theorem-local inside `encapsulate` / `make-event` output so dynamic observations, warnings, and inductions stop bleeding across neighboring generated theorems
2. feed the new raw goal/subgoal checkpoint kinds into richer proof-mode UI treatment, such as separate styling or timelines for explicit ACL2 checkpoints versus lightweight trace markers
3. replace the Python-side hardcoded sample-resolution table with data-driven upstream-source metadata so dynamic book fallback stays maintainable as the corpus grows

## 2026-03-19 Iteration 11

Completed this iteration:

- tightened `scripts/acl2_hint_bridge.py` so theorem extraction no longer slices from a whole ACL2 prompt when the target theorem appears inside a larger generated run
- made theorem-local extraction track all `DEFTHM` summary positions, trim to the target theorem's own summary block, and respect non-`ACL2` package prompts such as `MODAPP !>>>`
- added regression coverage for both failure modes: multiple theorem summaries in one prompt and package-specific prompts inside generated output
- updated `README.md`, `ACL2_SPEC.md`, and `docs/acl-proof-mode.md` to document the stronger theorem-local dynamic bridge behavior
- tracked this slice in Linear as `ALOK-550`

Verification:

- research branch commit `cae43a2`: `uv run python scripts/test_acl2_hint_bridge.py`
- research branch commit `cae43a2`: `LAKE_NO_CACHE=1 lake build acl2lean`
- research branch commit `cae43a2`: `uv run python Verify.py`
- research branch commit `cae43a2`: `./.lake/build/bin/acl2lean hints acl2_samples/die-hard-work.lisp make-prog-correct | sed -n '1,120p'`
- research branch commit `cae43a2`: `uv run python scripts/acl2_hint_bridge.py --book acl2_samples/apply-model-apply-prim.lisp --theorem 'n-car-cadr-caddr-etc-opener'`
- pushed research branch commit `cae43a2` to `origin/autoresearch/mar19-acl2lean`
- after the push, `gh run list --branch autoresearch/mar19-acl2lean --limit 8` showed GitHub Actions run `23326881659` for `Tighten theorem-local ACL2 hint extraction` as `in_progress`

Outcome:

- keep
- not promoted to `main` yet

Notes:

- the key acceptance check was the real `apply-model` theorem `n-car-cadr-caddr-etc-opener`: its dynamic artifact now starts at the target theorem's `MODAPP !>>>` prompt and `DEFTHM` form instead of inheriting enclosing `IN-THEORY` / `ENCAPSULATE` summaries or unrelated warning kinds
- `make-prog-correct` on the `die-hard` path still renders the expected theorem-local warnings and raw goal/subgoal checkpoints through the built `acl2lean hints` CLI, so the tighter slicing did not regress the already-working dynamic path

Next best ideas:

1. turn theorem-local dynamic checkpoints and warning kinds into replayable Lean-side actions instead of only panel/CLI metadata
2. replace the hardcoded Python sample-resolution table with data-driven upstream-source metadata so more excerpted books can be loaded and scoped consistently
3. start decomposing dynamic ACL2 warning kinds like `Disable` / `Double-rewrite` into Lean proof-search heuristics or theory-adjustment suggestions

## 2026-03-19 Iteration 12

Completed this iteration:

- added a structured dynamic replay-action layer to `scripts/acl2_hint_bridge.py`, so theorem-local ACL2 output now produces typed candidate actions instead of leaving `:USE` hints, disable advice, rewrite-overlap warnings, and induction choices trapped inside raw text blocks
- taught the bridge to extract concrete actions from real ACL2 output shapes: `:USE` / generic hint-events, `consider disabling ...` warning text, `Subsume` rewrite-overlap warnings, and induction term/rule summaries
- extended `ACL2Lean.HintBridge` with `DynamicAction`, threaded the new JSON field through Lean deserialization, and updated the CLI renderer plus `ACL2Lean.ProofMode` so proof-mode snapshots now count and surface candidate replay actions in `Next Moves` / notes
- switched `ACL2Lean/ProofModeDemo.lean` to `nbr-calls-flog2-is-logarithmic`, which exercises the new action path with real `:USE`, disable-rule, and rewrite-overlap guidance from ACL2
- updated the README / ACL2 spec / proof-mode notes and tracked the slice in Linear as `ALOK-551`

Verification:

- research branch commit `d1b308e`: `uv run python scripts/test_acl2_hint_bridge.py`
- research branch commit `d1b308e`: `uv run python scripts/acl2_hint_bridge.py --book acl2_samples/2009-log2.lisp --theorem nbr-calls-flog2-is-logarithmic`
- research branch commit `d1b308e`: `uv run python scripts/acl2_hint_bridge.py --book acl2_samples/2009-log2.lisp --theorem natp-clog2`
- research branch commit `d1b308e`: `lean-lsp-mcp` diagnostics on `ACL2Lean/HintBridge.lean`, `ACL2Lean/ProofMode.lean`, and `ACL2Lean/ProofModeDemo.lean`
- research branch commit `d1b308e`: `LAKE_NO_CACHE=1 lake build ACL2Lean.HintBridge ACL2Lean.ProofMode ACL2Lean.ProofModeDemo Main`
- research branch commit `d1b308e`: `LAKE_NO_CACHE=1 lake build`
- research branch commit `d1b308e`: `./.lake/build/bin/acl2lean hints acl2_samples/2009-log2.lisp nbr-calls-flog2-is-logarithmic | sed -n '1,200p'`
- research branch commit `d1b308e`: `./.lake/build/bin/acl2lean hints acl2_samples/2009-log2.lisp natp-clog2 | sed -n '1,160p'`
- research branch commit `d1b308e`: `uv run python Verify.py`
- pushed research branch commit `d1b308e` to `origin/autoresearch/mar19-acl2lean`
- after the push, `gh run list --branch autoresearch/mar19-acl2lean --limit 8` showed GitHub Actions run `23327251026` for `Extract structured actions from ACL2 hint bridge` as `in_progress`

Outcome:

- keep
- not promoted to `main` yet

Notes:

- `nbr-calls-flog2-is-logarithmic` now reaches Lean with four concrete candidate replay actions: one `use`, one `disable-rule`, and two rewrite-overlap actions derived from ACL2 `Subsume` warnings
- `natp-clog2` now surfaces an explicit induction action (`induct on (CLOG2 N) using rule CLOG2`) through the same bridge, which is the first time the dynamic path has emitted a typed induction candidate instead of only a prose block
- this is a real bridge advance, but I did not promote it to `main` yet because the proof-mode consumer for dynamic actions still lives on the research branch alongside the earlier hint-bridge/UI slices

Next best ideas:

1. execute the new dynamic replay actions against real Lean goals, starting with `use`, disable-rule/theory adjustments, and induction candidates
2. replace the hardcoded Python sample-resolution table with data-driven upstream-source metadata so dynamic fallback remains maintainable as the corpus grows
3. parse additional dynamic ACL2 guidance such as `Double-rewrite`, richer `:in-theory` hint-events, and other warning forms into typed Lean-side actions

## 2026-03-19 Iteration 13

Completed this iteration:

- extended `scripts/acl2_hint_bridge.py` so theorem-local dynamic actions now also cover ACL2 splitter notes and `Non-rec` warnings instead of leaving both as display-only text
- taught the bridge to turn summary-time splitter guidance like `if-intro: ((:DEFINITION GCD-PROG!))` into typed `split-goal` actions and to turn `Non-rec` warnings into typed `disable-definition` actions that preserve the suggested definition rune
- added parser regression coverage for both new action families and updated the README / ACL2 spec / proof-mode notes so the documented dynamic bridge surface matches the richer action extraction
- tracked this slice in Linear as `ALOK-552`

Verification:

- research branch commit `b2647a3`: `uv run python scripts/test_acl2_hint_bridge.py`
- research branch commit `b2647a3`: `uv run python scripts/acl2_hint_bridge.py --book acl2_samples/die-hard-work.lisp --theorem next-unique`
- research branch commit `b2647a3`: `uv run python scripts/acl2_hint_bridge.py --book acl2_samples/die-hard-work.lisp --theorem exists-gcd-prog`
- research branch commit `b2647a3`: `./.lake/build/bin/acl2lean hints acl2_samples/die-hard-work.lisp next-unique | sed -n '1,220p'`
- research branch commit `b2647a3`: `./.lake/build/bin/acl2lean hints acl2_samples/die-hard-work.lisp exists-gcd-prog | sed -n '1,260p'`
- research branch commit `b2647a3`: `LAKE_NO_CACHE=1 lake build ACL2Lean.HintBridge ACL2Lean.ProofMode Main`
- research branch commit `b2647a3`: `LAKE_NO_CACHE=1 lake build`
- research branch commit `b2647a3`: `uv run python Verify.py`
- pushed research branch commit `b2647a3` to `origin/autoresearch/mar19-acl2lean`
- after the push, `gh run list --branch autoresearch/mar19-acl2lean --limit 8` showed GitHub Actions run `23327539592` for `Capture splitter and Non-rec hint actions` as `in_progress`

Outcome:

- keep
- not promoted to `main` yet

Notes:

- `next-unique` now reaches Lean with ACL2’s theory advice preserved as a typed `disable-definition` action for `(:DEFINITION NEXT)` rather than only a prose `Non-rec` warning
- `exists-gcd-prog` now surfaces both the ACL2 splitter note and the matching non-recursive-definition advice as typed candidate replay actions, which is the first time the dynamic bridge has carried split guidance from ACL2 into the Lean-visible action layer
- I did not promote this slice to `main` yet because it extends the still-research-only dynamic hint/action workflow instead of a mainline-supported surface

Next best ideas:

1. parse richer dynamic theory guidance such as emitted `:in-theory`, `:expand`, and `:do-not-induct` hint-events into structured Lean-side actions instead of flat strings
2. execute the accumulated dynamic replay actions against real Lean goals, starting with `use`, split, and disable-definition/theory adjustments
3. replace the Python-side hardcoded sample-resolution table with data-driven upstream-source metadata so broader theorem-local dynamic extraction stays maintainable

## 2026-03-19 Iteration 14

Completed this iteration:

- extended `scripts/acl2_hint_bridge.py` so ACL2 `:TYPED-TERM` observations now become typed dynamic replay actions instead of remaining inert observation text
- fixed induction-block collection so the dynamic bridge preserves ACL2's emitted subgoal-count line (`... produces eight nontautological subgoals.`) instead of truncating the induction guidance just before that proof-search summary
- strengthened the existing `natp-clog2` regression to assert both behaviors, and updated `README.md`, `ACL2_SPEC.md`, and `docs/acl-proof-mode.md` so the documented dynamic hint surface matches the richer observation/induction capture
- tracked this slice in Linear as `ALOK-553`

Verification:

- research branch commit `33ed8f0`: `uv run python scripts/test_acl2_hint_bridge.py`
- research branch commit `33ed8f0`: `uv run python scripts/acl2_hint_bridge.py --book acl2_samples/2009-log2.lisp --theorem natp-clog2`
- research branch commit `33ed8f0`: `LAKE_NO_CACHE=1 lake build ACL2Lean.HintBridge ACL2Lean.ProofMode Main`
- research branch commit `33ed8f0`: `./.lake/build/bin/acl2lean hints acl2_samples/2009-log2.lisp natp-clog2 | sed -n '1,220p'`
- research branch commit `33ed8f0`: `LAKE_NO_CACHE=1 lake build`
- research branch commit `33ed8f0`: `uv run python Verify.py`
- pushed research branch commit `33ed8f0` to `origin/autoresearch/mar19-acl2lean`
- after the push, `gh run list --branch autoresearch/mar19-acl2lean --limit 8` showed GitHub Actions run `23327747480` for `Capture typed-term observation guidance in hint bridge` as `queued`

Outcome:

- keep
- not promoted to `main` yet

Notes:

- `natp-clog2` now reaches Lean with two distinct typed action candidates from ACL2's own proof search: the existing induction choice and a new `typed-term` focus action for `(CLOG2 N)`
- the preserved induction block now carries ACL2's own subgoal-count forecast into the CLI/panel path, which is more faithful to the hint-oracle role than the earlier truncated block
- I did not promote this slice to `main` yet because it extends the still-research-only dynamic hint/action workflow rather than a mainline-supported surface

Next best ideas:

1. parse richer dynamic theory guidance such as emitted `:in-theory`, `:expand`, and `:do-not-induct` hint-events into structured Lean-side actions instead of flat strings
2. capture lifecycle lines like `*1 ... is pushed for proof by induction` and `Thus key checkpoint Goal is COMPLETED!` as structured progress metadata instead of leaving them only in `raw_excerpt`
3. execute the accumulated dynamic replay actions against real Lean goals, starting with `use`, split, disable-definition/theory adjustments, and typed-term-guided induction setup

## 2026-03-19 Iteration 15

Completed this iteration:

- hardened `scripts/acl2_hint_bridge.py` against two real ACL2 transcript quirks from the dynamic hint-generator path: prompt-adjacent proof markers like `ACL2 !>>Goal'` and multiline splitter/hint payloads that ACL2 pretty-prints across several lines
- added transcript normalization before theorem slicing so `renaming-hack-lemma` now preserves the first `Goal'` checkpoint instead of dropping it when ACL2 prints it on the prompt line
- replaced line-based summary parsing with grouped multiline entry parsing for summary rules, hint-events, and splitter rules, so `nonneg-int-gcd-0` now carries one coherent `if-intro` splitter action instead of two bogus fragments
- added regression coverage for both real failure modes plus synthetic multiline `:IN-THEORY`, `:EXPAND`, and `:DO-NOT-INDUCT` hint-events, and updated `README.md`, `ACL2_SPEC.md`, and `docs/acl-proof-mode.md` to document the more robust dynamic bridge surface
- tracked this slice in Linear as `ALOK-554`

Verification:

- research branch commit `560bcb3`: `uv run python scripts/test_acl2_hint_bridge.py`
- research branch commit `560bcb3`: `uv run python scripts/acl2_hint_bridge.py --book acl2_samples/die-hard-work.lisp --theorem nonneg-int-gcd-0 | sed -n '1,180p'`
- research branch commit `560bcb3`: `uv run python scripts/acl2_hint_bridge.py --book acl2_samples/die-hard-work.lisp --theorem renaming-hack-lemma | sed -n '1,160p'`
- research branch commit `560bcb3`: `uv run python scripts/acl2_hint_bridge.py --book acl2_samples/die-hard-work.lisp --theorem exists-gcd-prog | sed -n '1,200p'`
- research branch commit `560bcb3`: `LAKE_NO_CACHE=1 lake build`
- research branch commit `560bcb3`: `uv run python Verify.py`
- research branch commit `560bcb3`: `./.lake/build/bin/acl2lean hints acl2_samples/die-hard-work.lisp nonneg-int-gcd-0 | sed -n '1,120p'`
- research branch commit `560bcb3`: `./.lake/build/bin/acl2lean hints acl2_samples/die-hard-work.lisp renaming-hack-lemma | sed -n '1,120p'`
- research branch commit `560bcb3`: `./.lake/build/bin/acl2lean ci autoresearch/mar19-acl2lean`

Outcome:

- keep
- not promoted to `main` yet

Notes:

- `nonneg-int-gcd-0` is now a concrete dynamic-bridge acceptance test for grouped theory/split guidance: the CLI and JSON paths both surface a single `split-goal` action with the full `if-intro` payload instead of inventing a second fake splitter entry
- `renaming-hack-lemma` now reaches Lean with the full leading `Goal'`, `Goal''`, and `Goal'''` checkpoint chain even though ACL2 printed the first one directly on the prompt line
- this is a real advance on the ACL2-oracle path because it fixes fidelity bugs in the emitted proof trace itself, but I did not promote it to `main` yet because it still extends the research-branch-only dynamic hint/action workflow rather than a mainline-supported surface

Next best ideas:

1. find one real ACL2 theorem whose dynamic summary emits multiline `:IN-THEORY`, `:EXPAND`, or `:DO-NOT-INDUCT` hint-events so the new grouped parser is exercised on non-synthetic theory guidance from the binary
2. capture lifecycle lines like `*1 ... is pushed for proof by induction` and `Thus key checkpoint Goal is COMPLETED!` as structured dynamic progress metadata instead of leaving them only in `raw_excerpt`
3. start executing the accumulated dynamic replay actions against Lean goals, beginning with `use`, split, disable-definition/theory adjustments, and typed-term-guided induction setup

## 2026-03-19 Iteration 16

Completed this iteration:

- fixed the dynamic load-plan fallback for `acl2_samples/apply-model-apply.lisp` so the bridge now preloads both the upstream `MODAPP` portcullis and `apply-constraints.lisp` instead of stopping after package setup
- taught `scripts/acl2_hint_bridge.py` to recover theorem-local `:HINTS` directives from ACL2-emitted `DEFTHM` transcript forms when summary `Hint-events:` are absent or incomplete, including nested `LOCAL (DEFTHM ...)` wrappers
- merged those recovered hint directives into the existing `hint_events` / structured action path, which now exposes real `:EXPAND` and `:IN-THEORY` guidance from the `apply-model/apply` corpus instead of only synthetic tests or summary-time `:USE` lines
- added parser regression coverage for both transcript-echoed hint recovery and the new `apply-model/apply` prelude chain, and updated the README / ACL2 spec / proof-mode notes to document the broader dynamic bridge surface
- tracked this slice in Linear as `ALOK-555`

Verification:

- research branch commit `391e6a2`: `uv run python scripts/test_acl2_hint_bridge.py`
- research branch commit `391e6a2`: `uv run python scripts/acl2_hint_bridge.py --book acl2_samples/apply-model-apply.lisp --theorem 'ev$-def-fact'`
- research branch commit `391e6a2`: `uv run python scripts/acl2_hint_bridge.py --book acl2_samples/apply-model-apply.lisp --theorem 'apply$-badgep-hons-get-lemma'`
- research branch commit `391e6a2`: `LAKE_NO_CACHE=1 lake build`
- research branch commit `391e6a2`: `uv run python Verify.py`
- research branch commit `391e6a2`: `./.lake/build/bin/acl2lean hints acl2_samples/apply-model-apply.lisp 'ev$-def-fact' | sed -n '1,200p'`
- research branch commit `391e6a2`: `./.lake/build/bin/acl2lean hints acl2_samples/apply-model-apply.lisp 'apply$-badgep-hons-get-lemma' | sed -n '1,120p'`

Outcome:

- keep
- not promoted to `main` yet

Notes:

- `ev$-def-fact` is now a concrete dynamic-bridge acceptance test for transcript-echoed theory guidance: ACL2 does not emit a summary `Hint-events:` block for it, but the bridge still recovers the emitted `:EXPAND ((EV$ X A))` directive from the echoed `DEFTHM` form and exposes it as a typed `expand` action
- `apply$-badgep-hons-get-lemma` now loads through the same `apply-model/apply` path and reaches Lean with a real theorem-local `:IN-THEORY (ENABLE HONS-ASSOC-EQUAL)` action plus the existing warning / splitter / induction guidance
- this is a real hint-generator-path advance because the bridge now relies on more of ACL2's actual emitted transcript for theory guidance and unlocks a much richer sample corpus than the earlier `apply-prim`-only fallback

Next best ideas:

1. capture lifecycle lines such as `*1 ... is pushed for proof by induction`, `*1 is COMPLETED!`, and `Thus key checkpoint ... is COMPLETED!` as structured dynamic progress metadata instead of leaving them only inside checkpoint text blocks
2. extend transcript-echo recovery beyond `:HINTS` to other proof-relevant directives ACL2 echoes in theorem-local forms when summary metadata is sparse
3. start executing the accumulated dynamic replay actions against Lean goals, beginning with `use`, `expand`, split, disable-definition/theory adjustments, and typed-term-guided induction setup

## 2026-03-19 Iteration 17

Completed this iteration:

- taught `scripts/acl2_hint_bridge.py` to turn ACL2 `Free` warnings into structured `bind-free-variable` actions that preserve the free variable, the searched hypothesis pattern, and the trigger term when ACL2 emits it
- generalized `Non-rec` warning parsing beyond the old single-`:REWRITE` / single-symbol shape, so plural `function symbols ... have non-recursive definitions` output now yields one `disable-definition` action per suggested rune and `:LINEAR` warnings carry their rule class through the action summary
- added focused bridge regressions for both `Free` warning variants plus singular/plural/non-`:REWRITE` `Non-rec` wording, and updated `README.md`, `ACL2_SPEC.md`, and `docs/acl-proof-mode.md` so the documented dynamic bridge surface matches the new warning-action coverage
- tracked this slice in Linear as `ALOK-556`

Verification:

- research branch commit `9c3e8c7`: `uv run python scripts/test_acl2_hint_bridge.py`
- research branch commit `9c3e8c7`: `uv run python scripts/acl2_hint_bridge.py --book acl2_samples/die-hard-work.lisp --theorem INV-INITIAL-STATE | rg -n 'disable-definition|INV-INITIAL-STATE|INITIAL-STATE|DEFINITION INV'`
- research branch commit `9c3e8c7`: `uv run python scripts/acl2_hint_bridge.py --book acl2_samples/die-hard-work.lisp --theorem NATP-/-GCD-LITTLE-LEMMA | rg -n 'bind-free-variable|NONNEG-INT-MOD J GCD|free variable J'`
- research branch commit `9c3e8c7`: `./.lake/build/bin/acl2lean hints acl2_samples/die-hard-work.lisp POSITIVE-FLOOR-LITTLE-LEMMA | sed -n '1,220p'`
- research branch commit `9c3e8c7`: `lake build`
- research branch commit `9c3e8c7`: `uv run python Verify.py`
- pushed research branch commit `9c3e8c7` to `origin/autoresearch/mar19-acl2lean`
- after the push, `gh run list --branch autoresearch/mar19-acl2lean --limit 4` showed GitHub Actions run `23328601450` completed `success`

Outcome:

- keep
- not promoted to `main` yet

Notes:

- `INV-INITIAL-STATE` is now a concrete acceptance test for plural `Non-rec` extraction: one ACL2 warning about `INV` and `INITIAL-STATE` becomes two separate `disable-definition` actions instead of no structured guidance
- `NATP-/-GCD-LITTLE-LEMMA` now reaches Lean with a typed `bind-free-variable` action that tells the replay layer exactly which free variable (`J`) and searched hypothesis pattern (`(EQUAL (NONNEG-INT-MOD J GCD) 0)`) ACL2 relied on
- `POSITIVE-FLOOR-LITTLE-LEMMA` now shows both new warning families at once through the CLI: a `:LINEAR`-class `disable-definition` action for `(:DEFINITION FLOOR)` and a trigger-aware `bind-free-variable` action tied to `(FLOOR I GCD)`
- this is a real advance on the hint-oracle path because the bridge now preserves more of ACL2's proof-search constraints as typed data instead of dropping them into raw warning prose, but I did not promote it to `main` yet because the dynamic action workflow still lives on the research branch

Next best ideas:

1. start executing the accumulated dynamic replay actions against Lean goals, beginning with `use`, `disable-definition`, `bind-free-variable`, split, and theory-adjustment steps
2. capture lifecycle lines such as `*1 ... is pushed for proof by induction`, `*1 is COMPLETED!`, and `Thus key checkpoint ... is COMPLETED!` as structured dynamic progress metadata instead of leaving them only inside checkpoint text blocks
3. extend warning parsing to other replay-relevant ACL2 guidance families once a real sample surfaces them, but keep execution of the already-extracted action set ahead of pure schema growth

## 2026-03-19 Iteration 18

Completed this iteration:

- taught `scripts/acl2_hint_bridge.py` to recover ACL2 lifecycle/progress lines as structured dynamic metadata, starting with induction-push markers, subproof completion lines, and `Thus key checkpoint ... is COMPLETED!` notices
- extended `ACL2Lean.HintBridge` with a first-class `DynamicProgress` stream and updated the CLI rendering so lifecycle events show up distinctly from checkpoint text in `acl2lean hints ...`
- updated `ACL2Lean.ProofMode` so dynamic hint snapshots count lifecycle events separately, render them as dedicated proof-mode cards, and mark matching emitted checkpoints as `done` when ACL2 reports checkpoint completion
- added focused parser regression coverage for the new lifecycle extraction path and updated `README.md`, `ACL2_SPEC.md`, and `docs/acl-proof-mode.md` so the documented dynamic bridge surface includes lifecycle progress capture
- tracked this slice in Linear as `ALOK-557`

Verification:

- research branch commit `ae66f35`: `uv run python scripts/test_acl2_hint_bridge.py`
- research branch commit `ae66f35`: `lean-lsp-mcp` diagnostics on `ACL2Lean/HintBridge.lean` and `ACL2Lean/ProofMode.lean`
- research branch commit `ae66f35`: `lake build ACL2Lean.HintBridge ACL2Lean.ProofMode Main`
- research branch commit `ae66f35`: `./.lake/build/bin/acl2lean hints acl2_samples/2009-log2.lisp natp-clog2 | sed -n '65,75p'`
- research branch commit `ae66f35`: `lake build`
- research branch commit `ae66f35`: `uv run python Verify.py`
- pushed research branch commit `ae66f35` to `origin/autoresearch/mar19-acl2lean`
- after the push, `gh run list --branch autoresearch/mar19-acl2lean --limit 6` showed GitHub Actions run `23328938391` for `Capture ACL2 lifecycle progress metadata` as `in_progress`

Outcome:

- keep
- not promoted to `main` yet

Notes:

- `natp-clog2` is now a concrete acceptance test for emitted ACL2 lifecycle state: the dynamic bridge surfaces `[induction-push]`, `[subproof-complete]`, and `[checkpoint-complete]` entries even when ACL2 does not print a full `A key checkpoint` block for the initial goal
- the CLI now keeps lifecycle lines visible ahead of the long subgoal list, and the proof-mode panel can distinguish static checkpoint structure from emitted progress transitions instead of flattening everything into checkpoint text or `raw_excerpt`
- this is a real hint-generator-path advance because it captures more of ACL2's proof search behavior as typed Lean-visible state, but I did not promote it to `main` yet because the dynamic action/progress workflow still lives entirely on the research branch

Next best ideas:

1. start executing the accumulated dynamic replay actions against Lean goals, beginning with `use`, `disable-definition`, `bind-free-variable`, split, theory-adjustment, and typed-term-guided induction setup
2. use the new lifecycle/progress events to drive actual replay-state transitions in proof mode instead of only displaying them as emitted metadata
3. extend transcript-echo recovery beyond `:HINTS` or add new warning/action families only when a real ACL2 sample proves they are needed

## 2026-03-19 Iteration 19

Completed this iteration:

- added a canonical upstream fallback for `acl2_samples/2009-tri-sq.lisp`, so the dynamic hint bridge now loads the real workshop `tri-sq.lisp` book instead of failing on the excerpt's missing local `log2.lisp`
- taught `scripts/acl2_hint_bridge.py` to turn ACL2 `[Use]` warnings into explicit goal-targeted `use` actions in addition to the existing disable advice, preserving which emitted subgoal the `:USE` guidance applies to
- added regression coverage for both the new `tri-sq` fallback and warning-derived goal targeting, and updated `README.md`, `ACL2_SPEC.md`, and `docs/acl-proof-mode.md` so the documented dynamic bridge surface matches the new behavior
- tracked this slice in Linear as `ALOK-558`

Verification:

- research branch commit `4751d4d`: `uv run python scripts/test_acl2_hint_bridge.py`
- research branch commit `4751d4d`: `uv run python scripts/acl2_hint_bridge.py --book acl2_samples/2009-tri-sq.lisp --theorem pair-pow-log-is-correct`
- research branch commit `4751d4d`: `./.lake/build/bin/acl2lean hints acl2_samples/2009-tri-sq.lisp pair-pow-log-is-correct | sed -n '1,180p'`
- research branch commit `4751d4d`: `LAKE_NO_CACHE=1 lake build ACL2Lean.HintBridge ACL2Lean.ProofMode Main`
- research branch commit `4751d4d`: `LAKE_NO_CACHE=1 lake build`
- research branch commit `4751d4d`: `uv run python Verify.py`

Outcome:

- keep
- not promoted to `main` yet

Notes:

- `pair-pow-log-is-correct` is now a concrete dynamic-oracle acceptance test for subgoal-specific `:USE` guidance: the bridge resolves the excerpted repo sample to the upstream workshop book and surfaces separate `use PAIR-POW-2N-2N+1 in Subgoal *1/2` and `use ... in Subgoal *1/1` actions instead of only one collapsed summary hint-event
- this is a real hint-generator-path advance because it keeps more of ACL2's emitted replay intent attached to the checkpoints where ACL2 actually used it, but I did not promote it to `main` yet because the broader dynamic hint-bridge stack still lives only on the research branch

Next best ideas:

1. start executing the accumulated dynamic replay actions against Lean goals, especially now that `use` guidance can carry checkpoint-local targeting from the oracle path
2. enrich the dynamic bridge with more checkpoint-local structure only when ACL2 emits it in real transcripts, keeping theorem/sample coverage ahead of speculative schema growth
3. decide when the recent dynamic hint-bridge slices are coherent enough to promote together to `main` as one stable replay-infrastructure batch

## 2026-03-19 Iteration 20

Completed this iteration:

- taught `scripts/acl2_hint_bridge.py` to preserve ACL2 goal targets for transcript-recovered hint actions instead of flattening recovered `:HINTS` clauses into goal-less replay suggestions
- split summary `Hint-events:` action extraction from transcript-echoed `DEFTHM` hint extraction, so summary events still yield generic actions while transcript-only guidance now surfaces as `transcript-hint` actions targeted at `Goal`, `Goal'''`, or `Subgoal ...`
- added focused regressions for goal-targeted transcript hints, including a synthetic multi-goal transcript plus real transcript-echoed `ev$-def-fact` / `apply$-badgep-hons-get-lemma` coverage
- updated `README.md`, `ACL2_SPEC.md`, and `docs/acl-proof-mode.md` so the documented dynamic bridge surface matches the new goal-aware transcript-hint behavior
- tracked this slice in Linear as `ALOK-559`

Verification:

- research branch commit `078c8ec`: `uv run python scripts/test_acl2_hint_bridge.py`
- research branch commit `078c8ec`: `uv run python scripts/acl2_hint_bridge.py --book acl2_samples/die-hard-work.lisp --theorem nonnegative-integer-quotient-gcd-exceeds-1 | sed -n '20,70p'`
- research branch commit `078c8ec`: `uv run python scripts/acl2_hint_bridge.py --book acl2_samples/apply-model-apply.lisp --theorem 'ev$-def-fact' | rg -n 'transcript-hint|expand|actions|hint_events|Goal'`
- research branch commit `078c8ec`: `./.lake/build/bin/acl2lean hints acl2_samples/die-hard-work.lisp nonnegative-integer-quotient-gcd-exceeds-1 | sed -n '1,120p'`
- research branch commit `078c8ec`: `lake build`
- research branch commit `078c8ec`: `uv run python Verify.py`
- pushed research branch commit `078c8ec` to `origin/autoresearch/mar19-acl2lean`
- after the push, `gh run list --branch autoresearch/mar19-acl2lean --limit 6` showed GitHub Actions run `23329505758` for `Preserve goal-targeted transcript hint actions` as `in_progress`

Outcome:

- keep
- not promoted to `main` yet

Notes:

- `nonnegative-integer-quotient-gcd-exceeds-1` is now a concrete acceptance test for transcript-goal preservation: Lean sees the summary `:USE` action plus transcript-targeted `adjust theory ... in Goal` and instance-specific `use ... in Goal` actions that ACL2 only exposed in the echoed `DEFTHM`
- `ev$-def-fact` no longer degrades to a goal-less transcript recovery result: its transcript-only `:EXPAND ((EV$ X A))` guidance now reaches Lean as `expand ((EV$ X A)) in Goal`
- this is a real hint-generator-path advance because the bridge now keeps more of ACL2's theorem-local proof intent attached to the goal where ACL2 emitted it, but I did not promote it to `main` yet because the broader dynamic hint-action workflow still lives on the research branch

Next best ideas:

1. start executing the newly goal-targeted transcript actions against Lean replay state, beginning with `use`, `in-theory`, `expand`, and `do-not-induct`
2. look for a real ACL2 sample that echoes multi-goal `DEFTHM` hints at runtime so transcript-goal preservation is exercised on more than the synthetic regression path
3. recover additional theorem-level proof-search directives such as `:otf-flg` only when they can be surfaced cleanly as replay-relevant Lean metadata instead of adding more flat transcript text

## 2026-03-19 Iteration 21

Completed this iteration:

- taught `scripts/acl2_hint_bridge.py` to split multi-item ACL2 `:USE` payloads into one replay action per cited theorem or `(:INSTANCE ...)` form instead of collapsing the whole payload into one giant `use ...` action
- applied that splitting to both summary `Hint-events:` parsing and goal-targeted transcript-echoed `DEFTHM` hints, so theorem-local `Goal` / `Subgoal ...` targets survive even when ACL2 emits a list of `:USE` items
- added focused bridge regressions for summary `:USE` lists and transcript goal-targeted `:USE` bundles, and updated `README.md`, `ACL2_SPEC.md`, and `docs/acl-proof-mode.md` to document the finer-grained replay surface
- tracked this slice in Linear as `ALOK-560`

Verification:

- research branch commit `6b87cde`: `uv run python scripts/test_acl2_hint_bridge.py`
- research branch commit `6b87cde`: `uv run python scripts/acl2_hint_bridge.py --book acl2_samples/die-hard-work.lisp --theorem nonnegative-integer-quotient-gcd-relatively-prime | sed -n '1,220p'`
- research branch commit `6b87cde`: `./.lake/build/bin/acl2lean hints acl2_samples/die-hard-work.lisp nonnegative-integer-quotient-gcd-relatively-prime | sed -n '1,220p'`
- research branch commit `6b87cde`: `lake build`
- research branch commit `6b87cde`: `uv run python Verify.py`
- pushed research branch commit `6b87cde` to `origin/autoresearch/mar19-acl2lean`
- after the push, `gh run watch 23329725832 --exit-status` succeeded for GitHub Actions run `23329725832`

Outcome:

- keep
- not promoted to `main` yet

Notes:

- `NONNEGATIVE-INTEGER-QUOTIENT-GCD-RELATIVELY-PRIME` is now a concrete dynamic-oracle acceptance test for multi-item `:USE` replay guidance: its theorem-local transcript `:USE` bundle surfaces as five separate `use ... in Goal` actions instead of one flattened blob
- this is a real bridge advance because the next replay layer can schedule each ACL2 use item independently instead of reparsing a giant payload string before it can even start matching Lean lemmas
- I did not promote this slice to `main` yet because it still improves the research-branch-only dynamic hint/action workflow rather than a surface that already exists on `main`

Next best ideas:

1. start executing checkpoint-local `use` actions against Lean replay state now that multi-item bundles no longer need extra normalization before scheduling
2. group dynamic actions by ACL2 goal/subgoal inside `ACL2Lean.ProofMode` so the panel follows theorem-local replay targeting instead of presenting one flat action list in notes
3. only then extend transcript recovery to additional theorem-level directives such as `:otf-flg`, and only if real ACL2 transcripts expose them consistently enough to justify a new replay surface

## 2026-03-19 Iteration 22

Completed this iteration:

- added an explicit `goal_target` field to dynamic ACL2 replay actions, so Lean-side consumers no longer have to infer checkpoint scoping from the tail of an ad hoc `targets` list
- taught `scripts/acl2_hint_bridge.py` to recover checkpoint-local splitter-note targets from real ACL2 transcript lines such as `Splitter note ... for Goal''`, and to prefer those targeted splitter actions over goal-less summary fallbacks
- threaded the new goal-target metadata through `ACL2Lean.HintBridge` CLI rendering and `ACL2Lean.ProofMode`, which now attaches targeted ACL2 actions back onto the matching emitted `Goal` / `Subgoal ...` checkpoints instead of leaving them only in flat notes/next-move text
- strengthened bridge regressions to assert explicit goal targets on splitter, warning-derived, and transcript-recovered actions, and documented the new replay-facing targeting in `README.md`, `ACL2_SPEC.md`, and `docs/acl-proof-mode.md`
- tracked this slice in Linear as `ALOK-561`

Verification:

- research branch commit `afedca8`: `uv run python scripts/test_acl2_hint_bridge.py`
- research branch commit `afedca8`: `uv run python scripts/acl2_hint_bridge.py --book acl2_samples/die-hard-work.lisp --theorem exists-gcd-prog | rg -n 'split using|goal_target|Goal''|splitter'`
- research branch commit `afedca8`: `lean-lsp-mcp` diagnostics on `ACL2Lean/HintBridge.lean` and `ACL2Lean/ProofMode.lean`
- research branch commit `afedca8`: `LAKE_NO_CACHE=1 lake build ACL2Lean.HintBridge ACL2Lean.ProofMode Main`
- research branch commit `afedca8`: `lake build`
- research branch commit `afedca8`: `uv run python Verify.py`
- research branch commit `afedca8`: `./.lake/build/bin/acl2lean hints acl2_samples/die-hard-work.lisp exists-gcd-prog | sed -n '1,140p'`
- pushed research branch commit `afedca8` to `origin/autoresearch/mar19-acl2lean`
- `gh run watch 23330076848 --exit-status` succeeded for GitHub Actions run `23330076848`

Outcome:

- keep
- not promoted to `main` yet

Notes:

- `exists-gcd-prog` is now a concrete acceptance test for checkpoint-local replay targeting: its `if-intro` splitter guidance reaches Lean as a `split-goal` action targeted at `Goal''`, and the CLI/proof-mode surfaces that target explicitly
- this is a real replay-infrastructure advance because the next executor no longer needs to reverse-engineer checkpoint scoping from free-form summaries or the last element of `targets`
- I did not promote this slice to `main` yet because it still extends the research-branch-only dynamic hint/action/proof-mode workflow rather than a surface already carried on `main`

Next best ideas:

1. start executing checkpoint-local `use`, `split-goal`, and `in-theory` actions against Lean replay state now that dynamic actions carry explicit goal targets
2. preserve checkpoint-local targeting on any other ACL2-emitted guidance that still degrades to goal-less actions, but only when real transcripts exhibit the shape
3. decide when the recent dynamic hint-bridge/proof-mode slices are coherent enough to promote together to `main` as one stable replay-infrastructure batch

## 2026-03-19 Iteration 23

Completed this iteration:

- taught `scripts/acl2_hint_bridge.py` to recognize ACL2's forward-chaining trigger-term `Non-rec` warning shape, where ACL2 says a concrete trigger term is unlikely to arise unless a non-recursive definition is disabled
- emitted a typed `disable-definition` action for that warning family, preserving the relevant definition rune, theorem name, and trigger term instead of leaving the guidance trapped in raw warning text
- added a focused parser regression for the `BADGE-TYPE` transcript shape from the `apply-model` corpus and updated `README.md`, `ACL2_SPEC.md`, and `docs/acl-proof-mode.md` so the documented dynamic bridge surface now includes forward-chaining trigger-term guidance
- tracked this slice in Linear as `ALOK-562`

Verification:

- research branch commit `462025a`: `PYTHONPATH=scripts uv run python scripts/test_acl2_hint_bridge.py`
- research branch commit `462025a`: `PYTHONPATH=scripts uv run python -m unittest scripts.test_acl2_hint_bridge.HintBridgeParsingTests.test_non_rec_forward_chaining_warning_becomes_disable_definition_action`
- research branch commit `462025a`: `uv run python scripts/acl2_hint_bridge.py --book acl2_samples/apply-model-apply.lisp --theorem badge-type | rg -n 'disable-definition|BADGE-TYPE|BADGE FN|actions|warning_kinds|targets'`
- research branch commit `462025a`: `./.lake/build/bin/acl2lean hints acl2_samples/apply-model-apply.lisp badge-type | rg -n 'disable \\(:DEFINITION BADGE\\)|trigger term|warning-kinds|actions'`
- research branch commit `462025a`: `lake build`
- research branch commit `462025a`: `uv run python Verify.py`
- pushed research branch commit `462025a` to `origin/autoresearch/mar19-acl2lean`
- `gh run watch 23330347467 --exit-status` succeeded for GitHub Actions run `23330347467`

Outcome:

- keep
- not promoted to `main` yet

Notes:

- `badge-type` from `acl2_samples/apply-model-apply.lisp` is now a concrete acceptance test for a previously dropped ACL2 oracle signal: Lean sees `disable (:DEFINITION BADGE) so trigger term (BADGE FN) can arise for BADGE-TYPE` instead of only `warning-kinds: Non-rec`
- this is a real hint-generator-path advance because it preserves theorem-local ACL2 theory guidance for a warning family that appears outside the existing rewrite/linear `Non-rec` regexes, which makes the bridge less biased toward one narrow ACL2 rule-class wording
- I did not promote this slice to `main` yet because it still extends the research-branch-only dynamic hint/action workflow rather than a surface already carried on `main`

Next best ideas:

1. start executing checkpoint-local `disable-definition`, `use`, and `in-theory` actions against Lean replay state so the recovered oracle guidance affects checked replay instead of only display
2. scan for any other real ACL2 warning families that still surface only as `warning-kinds` or raw text, especially trigger-oriented advice outside the current rewrite/linear patterns
3. decide when the recent dynamic hint-bridge slices are coherent enough to promote together to `main` as one stable replay-infrastructure batch

## 2026-03-19 Iteration 24

Completed this iteration:

- taught `scripts/acl2_hint_bridge.py` to recover ACL2's combined `Free`/`Non-rec` warning shape from `2009-tri-sq`, where ACL2 says the searched-for free-variable hypothesis mentions a non-recursive function symbol and that disabling the definition is necessary for the search to succeed
- threaded earlier `Free` warning context through the warning pass so the new `disable-definition` action can retain the searched hypothesis, yielding Lean-visible guidance like `disable (:DEFINITION POSP) so free-variable search for Y via (POSP Y) can succeed in LEMMA-2`
- generalized `Subsume` warning parsing to accept ACL2 quoted rune names such as `|(+ y x)|` and plural prior-rule lists such as `|(* x (+ y z))|, |(* (* x y) z)| and |(* y x)|`, emitting one `watch-rune-overlap` action per cited existing rule
- added focused parser regressions for the combined free/non-rec warning, a quoted single-rule subsume warning, and a plural quoted-rule subsume warning, and updated `README.md`, `ACL2_SPEC.md`, and `docs/acl-proof-mode.md` so the documented bridge surface matches the new warning coverage
- tracked this slice in Linear as `ALOK-563`

Verification:

- research branch commit `19877c4`: `PYTHONPATH=scripts uv run python scripts/test_acl2_hint_bridge.py`
- research branch commit `19877c4`: `uv run python scripts/acl2_hint_bridge.py --book acl2_samples/2009-tri-sq.lisp --theorem 'Lemma-2' | rg -n 'free-variable search|LEMMA-2-N|disable \\(:DEFINITION POSP\\)'`
- research branch commit `19877c4`: `uv run python scripts/acl2_hint_bridge.py --book acl2_samples/2009-tri-sq.lisp --theorem 'Lemma-3' | rg -n 'free-variable search|watch-rune-overlap|\\|\\(\\* x \\(\\+ y z\\)\\)\\||\\|\\(\\* y x\\)\\|'`
- research branch commit `19877c4`: `uv run python scripts/acl2_hint_bridge.py --book acl2_samples/2009-tri-sq.lisp --theorem 'Lemma-4' | rg -n '\\|\\(\\+ y x\\)\\||watch-rune-overlap|compare generated rewrite'`
- research branch commit `19877c4`: `./.lake/build/bin/acl2lean hints acl2_samples/2009-tri-sq.lisp Lemma-2 | rg -n 'free-variable search|LEMMA-2-N|disable \\(:DEFINITION POSP\\)'`
- research branch commit `19877c4`: `./.lake/build/bin/acl2lean hints acl2_samples/2009-tri-sq.lisp Lemma-4 | rg -n '\\|\\(\\+ y x\\)\\||watch-rune-overlap|compare generated rewrite'`
- research branch commit `19877c4`: `lake build`
- research branch commit `19877c4`: `uv run python Verify.py`
- pushed research branch commit `19877c4` to `origin/autoresearch/mar19-acl2lean`
- `gh run watch 23330667126 --exit-status` succeeded for GitHub Actions run `23330667126`

Outcome:

- keep
- not promoted to `main` yet

Notes:

- on a real `2009-tri-sq` scan, the number of warning blocks with no structured warning action dropped from 26 to 2, and the remaining two are dedup-equivalent subsume warnings rather than still-unparsed guidance
- this is a real hint-generator-path advance because Lean now sees more of ACL2's theorem-local theory advice from the oracle, especially when ACL2 ties free-variable instantiation success to disabling a non-recursive definition or when it names quoted/plural overlap runes that were previously lost
- I did not promote this slice to `main` yet because it still extends the research-branch-only dynamic hint/action workflow rather than a surface already carried on `main`

Next best ideas:

1. start executing checkpoint-local `disable-definition`, `use`, and `in-theory` actions against Lean replay state so the newly recovered warning guidance affects checked replay instead of only display
2. decide whether action deduplication should preserve multiple ACL2 warning provenance entries when the resulting replay action is identical, so warning counts stay faithful without reintroducing flat duplicate actions
3. keep scanning real ACL2 books for any remaining warning families that still survive only as `warning-kinds` or raw text, especially outside the already covered `Free` / `Non-rec` / `Subsume` / `Use` families

## 2026-03-19 Iteration 25

Completed this iteration:

- widened the dynamic `Warning [Use]` matcher so `scripts/acl2_hint_bridge.py` keeps the entire ACL2 multi-rune disable payload instead of treating `(:REWRITE A) and (:REWRITE B)` as one malformed pseudo-rule
- added parenthesized-form extraction for ACL2 warning payloads and split combined `Warning [Use]` advice into one warning-derived `use` action plus one `disable-rule` action per cited rune
- added a focused regression for the real `2009-tri-sq` multi-rule warning shape and confirmed that 11 affected theorems now emit clean per-rule actions instead of summaries like `use LEMMA-5-A) and (:REWRITE LEMMA-5-C in Goal`
- tracked this slice in Linear as `ALOK-564`

Verification:

- research branch commit `52c6694`: `PYTHONPATH=scripts uv run python -m unittest scripts.test_acl2_hint_bridge.HintBridgeParsingTests.test_use_warning_with_multiple_rules_splits_actions`
- research branch commit `52c6694`: `PYTHONPATH=scripts uv run python scripts/test_acl2_hint_bridge.py`
- research branch commit `52c6694`: `lake build`
- research branch commit `52c6694`: `uv run python Verify.py`
- research branch commit `52c6694`: `./.lake/build/bin/acl2lean hints acl2_samples/2009-tri-sq.lisp Lemma-5-d | rg -n 'use LEMMA-5-A in Goal|use LEMMA-5-C in Goal|disable \\(:REWRITE LEMMA-5-A\\) in Goal|disable \\(:REWRITE LEMMA-5-C\\) in Goal'`
- pushed research branch commit `52c6694` to `origin/autoresearch/mar19-acl2lean`
- `gh run watch 23330954514 --exit-status` succeeded for GitHub Actions run `23330954514`

Outcome:

- keep
- not promoted to `main` yet

Notes:

- the affected `2009-tri-sq` theorems now include `Exists-pair-pow-Find-smallest-y`, `Find-smallest-y->-2`, `Lemma-5-d`, `Lemma-2-h`, `Theorem-2`, and six similar theorems that previously surfaced malformed combined `use` summaries from ACL2's multi-rune warning text
- this is a real hint-generator-path advance because ACL2 warning lines that mention multiple enabled runes are now replayable one rune at a time, which is the same granularity the later Lean executor will need for `use` and theory-adjustment scheduling
- I did not promote this slice to `main` yet because it still extends the research-branch-only dynamic hint/action workflow rather than a surface already carried on `main`

Next best ideas:

1. start executing checkpoint-local `use` and `disable-rule` actions against Lean replay state now that both transcript multi-item hints and warning-derived multi-rune guidance arrive one action at a time
2. decide whether the dynamic panel should collapse duplicate guidance when the same theorem/rune arrives from transcript hints and warnings, while still preserving ACL2 provenance somewhere in notes
3. keep scanning real ACL2 transcripts for any remaining theorem-local guidance that still degrades into display-only strings despite the action extractor improvements

## 2026-03-19 Iteration 26

Completed this iteration:

- reused the existing ACL2 parser and `TheoryExpr` model on the Lean side so dynamic ACL2 `in-theory` actions are no longer trapped as opaque strings inside `ACL2Lean.HintBridge`
- taught the `acl2lean hints` CLI renderer to show structured theory trees under dynamic `in-theory` actions, so emitted guidance like `(DISABLE FLOOR NONNEG-INT-GCD-IS-COMMON-DIVISOR)` now prints as decomposed `theory: disable` entries instead of only `adjust theory ...`
- updated `ACL2Lean.ProofMode` so dynamic hint snapshots thread those parsed theory items into checkpoint-local action details, the rune pane, and the notes stream, reusing the same theory-summary path that imported static metadata already used
- documented the new dynamic theory-normalization behavior in `README.md`, `ACL2_SPEC.md`, and `docs/acl-proof-mode.md`
- tracked this slice in Linear as `ALOK-565`

Verification:

- research branch commit `062e3b5`: `lake build ACL2Lean.HintBridge ACL2Lean.ProofMode Main`
- research branch commit `062e3b5`: `lake build acl2lean`
- research branch commit `062e3b5`: `lake build`
- research branch commit `062e3b5`: `uv run python Verify.py`
- research branch commit `062e3b5`: `./.lake/build/bin/acl2lean hints acl2_samples/apply-model-apply.lisp 'apply$-badgep-hons-get-lemma' | rg -n 'theory: enable|hons-assoc-equal'`
- research branch commit `062e3b5`: `./.lake/build/bin/acl2lean hints acl2_samples/die-hard-work.lisp nonnegative-integer-quotient-gcd-exceeds-1 | rg -n 'theory: disable|disable floor|disable nonneg-int-gcd-is-common-divisor'`
- research branch commit `062e3b5`: `lean_run_code` on `ACL2Lean.ProofMode` confirmed `snapshotOfDynamicHints` exposes dynamic runes `disable floor` / `disable nonneg-int-gcd-is-common-divisor` plus matching `action-theory ...` notes for `nonnegative-integer-quotient-gcd-exceeds-1`
- pushed research branch commit `062e3b5` to `origin/autoresearch/mar19-acl2lean`
- `gh run watch 23331468243 --exit-status` succeeded for GitHub Actions run `23331468243`

Outcome:

- keep
- not promoted to `main` yet

Notes:

- this directly advances the preferred attack order in `program.md`: the ACL2 binary is already emitting theory guidance, and Lean now parses that emitted `:IN-THEORY` payload back into the shared structural representation instead of stopping at flat display text
- the static imported-metadata path and the dynamic hint-oracle path now share one theory-language normalization surface, which should make later replay execution of dynamic `in-theory` actions less ad hoc
- I did not promote this slice to `main` yet because it still deepens the research-branch-only dynamic hint/proof-mode workflow rather than a surface already carried on `main`

Next best ideas:

1. start executing checkpoint-local dynamic `use`, `disable-rule` / `disable-definition`, and `in-theory` actions against Lean replay state so the parsed oracle guidance changes checked replay instead of only display
2. normalize other dynamic hint payloads such as `:expand` and `:do-not-induct` more structurally on the Lean side, so replay consumers do not have to peel those strings apart later
3. decide whether the accumulated dynamic hint/proof-mode slices are coherent enough to promote together to `main` as one stable replay-infrastructure batch

## 2026-03-19 Iteration 27

Completed this iteration:

- tightened `scripts/acl2_hint_bridge.py` so a target theorem excerpt now stops before later helper-theorem summaries or other foreign `DEFTHM` blocks that appear after the target summary in one ACL2 prompt
- added a second theorem-name filter on collected `ACL2 Warning` / `ACL2 Observation` blocks, so helper `DEFTHM`s inside macro-generated proof runs cannot pollute the target theorem artifact even if they share the same prompt
- added a focused parser regression that simulates the bad shape: target summary first, then helper-theorem warning/observation noise before ACL2 returns to the prompt
- verified the real `apply-model/apply` flag-lemma path now keeps only target-local dynamic guidance: `FLAG-LEMMA-FOR-GUESS-ILKS-ALIST-CORRECT` no longer inherits `GUESS-ILKS-ALIST-CORRECT` / `GUESS-ILKS-ALIST-LIST-CORRECT` warning actions, while still preserving its own clause-processor, `:use`, splitter, and induction data
- tracked this slice in Linear as `ALOK-566`

Verification:

- research branch commit `730bc57`: `PYTHONPATH=scripts uv run python -m unittest scripts.test_acl2_hint_bridge.HintBridgeParsingTests.test_theorem_section_ignores_helper_theorems_after_target_summary`
- research branch commit `730bc57`: `PYTHONPATH=scripts uv run python -m unittest scripts.test_acl2_hint_bridge`
- research branch commit `730bc57`: `uv run python scripts/acl2_hint_bridge.py --book acl2_samples/apply-model-apply.lisp --theorem 'FLAG-LEMMA-FOR-GUESS-ILKS-ALIST-CORRECT'`
- research branch commit `730bc57`: `./.lake/build/bin/acl2lean hints acl2_samples/apply-model-apply.lisp 'FLAG-LEMMA-FOR-GUESS-ILKS-ALIST-CORRECT' | sed -n '1,160p'`
- research branch commit `730bc57`: one-off leak scan over `acl2_samples/apply-model-apply.lisp` confirmed no remaining warning/observation blocks are attributed to foreign `DEFTHM`s
- research branch commit `730bc57`: `lake build`
- research branch commit `730bc57`: `uv run python Verify.py`
- pushed research branch commit `730bc57` to `origin/autoresearch/mar19-acl2lean`
- `gh run watch 23331811502 --exit-status` succeeded for GitHub Actions run `23331811502`

Outcome:

- keep
- not promoted to `main` yet

Notes:

- this fixes a real theorem-locality bug in the ACL2 hint-generator path rather than adding another display-only parser case: Lean-side replay consumers now stop seeing disable/bind-free-variable advice for helper theorems when the user asked for the outer flag lemma
- the `apply-model/apply` corpus was the main offender; a post-fix scan of that book found no remaining warning/observation blocks whose `DEFTHM` header disagrees with the target theorem artifact
- GitHub Actions stayed green on the code push; the only CI annotation was the existing Node.js 20 deprecation warning from upstream GitHub actions, not a failure in this repo

Next best ideas:

1. make dynamic checkpoint/progress extraction equally theorem-local in macro-generated transcripts where helper subproofs can still appear without explicit warning/observation headers
2. start executing the cleaned checkpoint-local dynamic `use`, `disable-rule` / `disable-definition`, and `in-theory` actions against Lean replay state so theorem-local oracle guidance affects checked replay
3. decide whether newly surfaced dynamic hint kinds like `:CLAUSE-PROCESSOR` should become first-class Lean-side replay actions rather than remaining generic action records

## 2026-03-19 Iteration 28

Completed this iteration:

- added Lean-side `DynamicAction` payload parsing helpers in `ACL2Lean.HintBridge` for dynamic `:EXPAND` and `:DO-NOT-INDUCT` guidance, reusing the ACL2 parser instead of leaving those payloads stringly typed after import into Lean
- taught `acl2lean hints` action rendering to print structured payload lines such as `expand: (ev$ x a)` and `do-not-induct: T` under real ACL2-emitted actions
- updated `ACL2Lean.ProofMode` so checkpoint-local action details and snapshot notes now surface parsed expand/do-not-induct payloads as structured note entries (`action-expand ...`, `action-do-not-induct ...`) rather than only flat summaries
- added guard-style Lean regressions for the new structured payload helpers and updated `README.md`, `ACL2_SPEC.md`, and `docs/acl-proof-mode.md` to document the broader dynamic payload normalization surface
- tracked this slice in Linear as `ALOK-567`

Verification:

- research branch commit `a32515d`: `lean-lsp-mcp` diagnostics on `ACL2Lean/HintBridge.lean`
- research branch commit `a32515d`: `lake build ACL2Lean.HintBridge ACL2Lean.ProofMode Main`
- research branch commit `a32515d`: `./.lake/build/bin/acl2lean hints acl2_samples/apply-model-apply.lisp 'ev$-def-fact' | rg -n 'expand:'`
- research branch commit `a32515d`: `./.lake/build/bin/acl2lean hints acl2_samples/die-hard-work.lisp nonnegative-integer-quotient-gcd-relatively-prime | rg -n 'do-not-induct:'`
- research branch commit `a32515d`: `lake env lean <tmp proofmode debug>` confirmed `snapshotOfDynamicHints` emits `action-expand transcript-hint/expand: (ev$ x a)` and `action-do-not-induct transcript-hint/do-not-induct: T` on the real artifacts
- research branch commit `a32515d`: `uv run python Verify.py`
- research branch commit `a32515d`: `LAKE_NO_CACHE=1 lake build acl2lean`
- research branch commit `a32515d`: `LAKE_NO_CACHE=1 lake build`
- pushed research branch commit `a32515d` to `origin/autoresearch/mar19-acl2lean`
- `gh run watch 23332255723 --exit-status` succeeded for GitHub Actions run `23332255723`

Outcome:

- keep
- not promoted to `main` yet

Notes:

- a plain `lake build` initially failed on a local Lake artifact-cache permission error under `~/.elan/.../lake/cache/artifacts`; rerunning with `LAKE_NO_CACHE=1` restored full-build verification without changing repo behavior
- this directly advances the preferred attack order in `program.md`: dynamic ACL2 payloads emitted by the oracle no longer stop as flat strings once they cross into Lean, which reduces the amount of ad hoc re-parsing the eventual replay executor will need
- I did not promote this slice to `main` yet because it still deepens the research-branch-only dynamic hint/proof-mode workflow rather than a surface already carried on `main`

Next best ideas:

1. start executing the newly parsed dynamic `expand` and `do-not-induct` actions against Lean replay state, alongside the existing `use` / theory guidance
2. surface and normalize real dynamic `:cases` payloads once a corpus theorem emits them or another ACL2 path exposes them cleanly
3. decide whether the recent dynamic hint/proof-mode slices are coherent enough to promote together to `main` as one stable replay-infrastructure batch

## 2026-03-20 Iteration 29

Completed this iteration:

- added Lean-side `DynamicAction` helpers in `ACL2Lean.HintBridge` for dynamic clause-processor and induction payloads, so those actions now expose structured `clause-processor`, `induct-term`, and `induction-rule` views instead of only flat summaries plus ad hoc targets
- taught `acl2lean hints` action rendering to print the new structured lines on real ACL2 artifacts, including `FLAG::FLAG-IS-CP` from `FLAG-LEMMA-FOR-GUESS-ILKS-ALIST-CORRECT` and `MAKE-PROG1-INDUCTION` guidance from `MAKE-PROG1-CORRECT`
- updated `ACL2Lean.ProofMode` so dynamic hint snapshots record clause-processor and induction payloads as explicit note entries (`action-clause-processor ...`, `action-induct-term ...`, `action-induction-rule ...`) instead of burying them inside prose summaries
- added transcript regression coverage for echoed `:CLAUSE-PROCESSOR` and `:INDUCT` hint events and documented the broader dynamic payload-normalization surface in `README.md`, `ACL2_SPEC.md`, and `docs/acl-proof-mode.md`
- tracked this slice in Linear as `ALOK-568`

Verification:

- research branch commit `e460995`: `lean-lsp-mcp` diagnostics on `ACL2Lean/HintBridge.lean`
- research branch commit `e460995`: `lean-lsp-mcp` diagnostics on `ACL2Lean/ProofMode.lean`
- research branch commit `e460995`: `PYTHONPATH=scripts uv run python -m unittest scripts.test_acl2_hint_bridge.HintBridgeParsingTests.test_transcript_echoed_clause_processor_hint_event_is_recovered scripts.test_acl2_hint_bridge.HintBridgeParsingTests.test_transcript_echoed_induct_hint_event_is_recovered`
- research branch commit `e460995`: `PYTHONPATH=scripts uv run python -m unittest scripts.test_acl2_hint_bridge`
- research branch commit `e460995`: `lake build ACL2Lean.HintBridge ACL2Lean.ProofMode Main`
- research branch commit `e460995`: `LAKE_NO_CACHE=1 lake build acl2lean`
- research branch commit `e460995`: `./.lake/build/bin/acl2lean hints acl2_samples/apply-model-apply.lisp 'FLAG-LEMMA-FOR-GUESS-ILKS-ALIST-CORRECT' | sed -n '96,122p'`
- research branch commit `e460995`: `./.lake/build/bin/acl2lean hints acl2_samples/die-hard-work.lisp make-prog1-correct | sed -n '52,72p'`
- research branch commit `e460995`: `uv run python Verify.py`
- research branch commit `e460995`: `lake build` passed after restoring user-write permissions on `~/.elan/toolchains/leanprover--lean4---v4.29.0-rc6/lake/cache/artifacts`
- pushed research branch commit `e460995` to `origin/autoresearch/mar19-acl2lean`
- `gh run watch 23332652386 --exit-status` succeeded for GitHub Actions run `23332652386`

Outcome:

- keep
- not promoted to `main` yet

Notes:

- this advances the hint-generator path directly: real ACL2 oracle artifacts that already mention clause processors and induction schemes now cross into Lean as structured payloads, which removes another layer of summary-scraping before replay execution
- `FLAG-LEMMA-FOR-GUESS-ILKS-ALIST-CORRECT` now shows `clause-processor: FLAG::flag-is-cp` in the CLI, while `MAKE-PROG1-CORRECT` now shows both `induct-term: (make-prog1-induction i n)` and `induction-rule: MAKE-PROG1-INDUCTION`
- I also repaired the stale local Lake artifact-cache permissions that had been making plain `lake build` flaky on this machine; this was an environment fix, not a repo change, but it restored the expected baseline build check
- I did not promote this slice to `main` yet because it still deepens the research-branch-only dynamic hint/proof-mode workflow rather than a surface already carried on `main`

Next best ideas:

1. start executing dynamic `use`, theory, induction, and clause-processor actions against Lean replay state instead of only surfacing them structurally
2. chase the remaining theorem-locality gap for checkpoints/progress inside macro-generated ACL2 transcripts where helper subproofs can still share one prompt
3. surface and normalize real dynamic `:cases` payloads once a corpus theorem emits them or another ACL2 path exposes them cleanly

## 2026-03-20 Iteration 30

Completed this iteration:

- taught `scripts/acl2_hint_bridge.py` to recover transcript-echoed theorem-level ACL2 directives outside `:HINTS`, starting with `:OTF-FLG`, by reading the echoed `DEFTHM` form and emitting a dedicated `transcript-option/otf-flg` dynamic action instead of dropping that proof-search guidance completely
- added focused parser coverage for the new path, proving that an echoed `(DEFTHM ... :OTF-FLG T ...)` transcript now yields `set otf-flg T` as a structured action
- extended `ACL2Lean.HintBridge` with Lean-side `otf-flg` payload parsing and structured rendering, so the CLI no longer treats that directive as an opaque flat summary when ACL2 exposes it
- updated `ACL2Lean.ProofMode` so dynamic hint snapshots record `action-otf-flg ...` notes alongside the existing theory / clause-processor / induction payload surfaces
- documented the broader dynamic hint surface in `README.md`, `ACL2_SPEC.md`, and `docs/acl-proof-mode.md`, and tracked the slice in Linear as `ALOK-569`

Verification:

- research branch commit `94814e2`: `lean-lsp-mcp` diagnostics on `ACL2Lean/HintBridge.lean`
- research branch commit `94814e2`: `lean-lsp-mcp` diagnostics on `ACL2Lean/ProofMode.lean`
- research branch commit `94814e2`: `PYTHONPATH=scripts uv run python -m unittest scripts.test_acl2_hint_bridge.HintBridgeParsingTests.test_transcript_echoed_otf_flg_option_is_recovered scripts.test_acl2_hint_bridge.HintBridgeParsingTests.test_transcript_echoed_induct_hint_event_is_recovered scripts.test_acl2_hint_bridge.HintBridgeParsingTests.test_transcript_echoed_hint_actions_preserve_goal_targets`
- research branch commit `94814e2`: `PYTHONPATH=scripts uv run python -m unittest scripts.test_acl2_hint_bridge`
- research branch commit `94814e2`: `lake build ACL2Lean.HintBridge ACL2Lean.ProofMode Main`
- research branch commit `94814e2`: `./.lake/build/bin/acl2lean hints acl2_samples/die-hard-work.lisp 'mod-+-*-floor-gcd' | sed -n '1,160p'`
- research branch commit `94814e2`: `uv run python scripts/acl2_hint_bridge.py --book acl2_samples/die-hard-work.lisp --theorem 'mod-+-*-floor-gcd' | rg -n 'otf-flg|OTF-FLG|transcript-option|actions|summary'`
- research branch commit `94814e2`: `uv run python Verify.py`
- research branch commit `94814e2`: `lake build`
- pushed research branch commit `94814e2` to `origin/autoresearch/mar19-acl2lean`
- research branch commit `94814e2`: `lake exe acl2lean ci autoresearch/mar19-acl2lean` showed GitHub Actions run `23333045123` in progress for the pushed feature commit
- `gh run watch 23333045123 --exit-status` succeeded for GitHub Actions run `23333045123`

Outcome:

- keep
- not promoted to `main` yet

Notes:

- this closes one of the explicitly deferred hint-generator follow-ups from the previous notes: at least one real ACL2 transcript (`mod-+-*-floor-gcd`) does expose theorem-level `:OTF-FLG`, and Lean now keeps that search configuration as structured oracle metadata instead of leaving it buried in `raw_excerpt`
- the new path is intentionally narrow: only transcript-exposed theorem options are surfaced, and only `:OTF-FLG` is normalized so far, because that is the directive the current corpus proves is both real and replay-relevant
- I did not promote this slice to `main` yet because it still deepens the research-branch-only dynamic hint/proof-mode workflow rather than a surface already carried on `main`

Next best ideas:

1. start executing dynamic `use`, theory, induction, clause-processor, and now `otf-flg` actions against Lean replay state instead of only surfacing them structurally
2. scan the corpus for any other theorem-level transcript directives that ACL2 actually echoes consistently enough to justify promotion into first-class dynamic actions
3. decide whether the recent dynamic hint/proof-mode slices are coherent enough to promote together to `main` as one stable replay-infrastructure batch

## 2026-03-20 Iteration 7

Completed this iteration:

- added Lean-side payload decoders for warning-derived dynamic ACL2 actions in `ACL2Lean.HintBridge`: `DisableRulePayload`, `DisableDefinitionPayload`, `FreeVariableBindingPayload`, and `RewriteOverlapPayload`
- taught `DynamicAction.structuredLines` to render those warning payloads as labeled fields, so `acl2lean hints` now shows structured `disable-rule`, `disable-definition`, `theorem`, `variable`, `hypothesis`, `trigger-term`, `generated-theorem`, and `existing-rule` lines instead of only flat summaries plus positional targets
- extended `ACL2Lean.ProofMode` to surface the same warning payload structure in dynamic snapshot notes via `action-disable-rule`, `action-disable-definition`, `action-warning-theorem`, `action-free-variable`, `action-binding-hypothesis`, `action-trigger-term`, `action-generated-theorem`, and `action-existing-rule`
- added Lean guard coverage proving the new payload decoders work on representative warning actions, and documented the richer Lean-side dynamic warning normalization in `README.md`, `ACL2_SPEC.md`, and `docs/acl-proof-mode.md`
- tracked the slice in Linear as `ALOK-570`

Verification:

- research branch commit `20478bf`: `lake build ACL2Lean.HintBridge ACL2Lean.ProofMode Main`
- research branch commit `20478bf`: `lake build acl2lean`
- research branch commit `20478bf`: `./.lake/build/bin/acl2lean hints acl2_samples/2009-log2.lisp nbr-calls-flog2-is-logarithmic | sed -n '34,46p'`
- research branch commit `20478bf`: `./.lake/build/bin/acl2lean hints acl2_samples/die-hard-work.lisp 'mod-+-*-floor-gcd' | sed -n '84,98p'`
- research branch commit `20478bf`: `./.lake/build/bin/acl2lean hints acl2_samples/2009-tri-sq.lisp Lemma-2 | sed -n '48,66p'`
- research branch commit `20478bf`: `./.lake/build/bin/acl2lean hints acl2_samples/2009-tri-sq.lisp Lemma-4 | sed -n '44,62p'`
- research branch commit `20478bf`: `lake build`
- research branch commit `20478bf`: `uv run python Verify.py`
- research branch state after `20478bf`: `lake exe acl2lean ci autoresearch/mar19-acl2lean` showed the latest remote branch runs still green before the fresh push

Outcome:

- keep
- not promoted to `main` yet

Notes:

- this closes a Lean-side gap in the hint-generator path: warning guidance was already classified in Python, but Lean replay/UI consumers still had to infer structure from summary strings and target positions
- the new payload decoders make warning guidance as inspectable as the existing theory / expand / clause-processor / induction / `otf-flg` paths, which is the right shape for the next replay step
- the `lean-lsp-mcp` diagnostics for `ACL2Lean.HintBridge` stayed clean after the edit; `ACL2Lean.ProofMode` was validated via successful rebuilds instead because the imported dependency view lagged briefly while the updated `HintBridge` module was recompiling

Next best ideas:

1. execute `disable-rule`, `disable-definition`, and `use` warning actions against Lean replay state instead of only rendering them
2. turn structured free-variable and rewrite-overlap payloads into proof-mode next-move grouping or checkpoint-local heuristics rather than leaving them only in notes
3. decide whether the recent dynamic hint/proof-mode slices are coherent enough to promote together to `main` as one stable replay-infrastructure batch

## 2026-03-20 Iteration 31

Completed this iteration:

- added Lean-side `UsePayload` parsing in `ACL2Lean.HintBridge`, so dynamic ACL2 `use` actions are no longer only flat strings once they cross back into Lean
- taught the new path to distinguish plain theorem refs from `(:THEOREM ...)` payloads and `(:INSTANCE ...)` payloads with explicit substitution bindings
- updated `DynamicAction.structuredLines` so `acl2lean hints ...` now renders `use-instance`, `binding`, and `use-theorem` lines for real emitted ACL2 guidance instead of leaving instance/theorem forms opaque
- extended `ACL2Lean.ProofMode` so dynamic hint snapshots emit matching `action-use-instance`, `action-use-binding`, and `action-use-theorem` notes for downstream replay/UI consumers
- added Lean guard coverage for the new payload parser and documented the richer dynamic `:USE` normalization in `README.md`, `ACL2_SPEC.md`, and `docs/acl-proof-mode.md`
- tracked the slice in Linear as `ALOK-571`

Verification:

- research branch commit `6098e85`: `lean-lsp-mcp` diagnostics on `ACL2Lean/HintBridge.lean`
- research branch commit `6098e85`: `lake build ACL2Lean.HintBridge ACL2Lean.ProofMode Main`
- research branch commit `6098e85`: `lake build acl2lean`
- research branch commit `6098e85`: `./.lake/build/bin/acl2lean hints acl2_samples/die-hard-work.lisp nonnegative-integer-quotient-gcd-relatively-prime | rg -n 'use-instance|binding:|p :=|d :='`
- research branch commit `6098e85`: `./.lake/build/bin/acl2lean hints acl2_samples/2009-tri-sq.lisp Lemma-2-j | rg -n 'use-theorem'`
- research branch commit `6098e85`: `lean-lsp-mcp lean_run_code` confirmed `ACL2.ProofMode.snapshotOfDynamicHints` emits `action-use-instance` / `action-use-binding` notes on `nonnegative-integer-quotient-gcd-relatively-prime` and `action-use-theorem` on `Lemma-2-j`
- research branch commit `6098e85`: `uv run python scripts/test_acl2_hint_bridge.py`
- research branch commit `6098e85`: `uv run python Verify.py`
- research branch commit `6098e85`: `lake build`
- pushed research branch commit `6098e85` to `origin/autoresearch/mar19-acl2lean`
- research branch commit `6098e85`: `lake exe acl2lean ci autoresearch/mar19-acl2lean` still showed the previously completed green runs before the fresh push appeared
- `gh run watch 23334027708 --exit-status` succeeded for GitHub Actions run `23334027708`

Outcome:

- keep
- not promoted to `main` yet

Notes:

- this closes the biggest remaining Lean-side normalization gap in the dynamic hint bridge: `:USE` is the most common replay-oriented hint class in the local sample corpus, and Lean can now inspect theorem-vs-instance shape plus concrete substitutions instead of scraping raw payload text
- the real `die-hard` artifact now surfaces instance bindings such as `p := ...`, `q := ...`, and `d := ...` through the CLI and proof-mode notes, while the real `tri-sq` artifact for `Lemma-2-j` now surfaces a structured `use-theorem` line
- I did not promote this slice to `main` yet because it still deepens the research-branch-only dynamic hint/proof-mode path; it should likely promote together with the broader dynamic replay/UI batch rather than as a standalone mainline patch

Next best ideas:

1. execute structured dynamic `use` actions against Lean replay state, starting with theorem refs and `(:INSTANCE ...)` substitutions rather than only surfacing them in notes
2. give `split-goal` and `typed-term` actions the same Lean-side payload treatment so replay/UI consumers stop relying on flat summaries for those paths too
3. decide whether the recent dynamic hint/proof-mode slices from `:IN-THEORY` through warning payloads and now `:USE` are coherent enough to promote together to `main`

## 2026-03-20 Iteration 32

Completed this iteration:

- added `DynamicReplayState` to `ACL2Lean.HintBridge`, which folds parsed dynamic ACL2 actions into a Lean-side replay summary instead of leaving them as a flat action log
- taught that replay-state layer to accumulate theory adjustments (`:in-theory`, `disable-rule`, `disable-definition`), replay uses, clause-processors, expands, cases, typed terms, selected induction, `do-not-induct`, and `otf-flg`
- updated `acl2lean hints` so real dynamic artifacts now print a `replay-state:` section, including a compact theory timeline / use timeline plus selected induction and theorem-level search toggles when ACL2 emitted them
- updated `ACL2Lean.ProofMode` so dynamic hint snapshots thread the interpreted replay state into the goal summary, rune list, next-move suggestions, and notes instead of only exposing raw action strings
- documented the new interpretation layer in `README.md`, `ACL2_SPEC.md`, and `docs/acl-proof-mode.md`, and tracked the slice in Linear as `ALOK-572`

Verification:

- research branch commit `3a3c1c9`: `lean-lsp-mcp` diagnostics on `ACL2Lean/HintBridge.lean`
- research branch commit `3a3c1c9`: `lean-lsp-mcp` diagnostics on `ACL2Lean/ProofMode.lean`
- research branch commit `3a3c1c9`: `lake build ACL2Lean.HintBridge ACL2Lean.ProofMode Main`
- research branch commit `3a3c1c9`: `./.lake/build/bin/acl2lean hints acl2_samples/die-hard-work.lisp 'mod-+-*-floor-gcd' | rg -n 'replay-state|theory-timeline|use-timeline|do-not-induct:|otf-flg:'`
- research branch commit `3a3c1c9`: `./.lake/build/bin/acl2lean hints acl2_samples/die-hard-work.lisp make-prog1-correct | rg -n 'replay-state|selected-induction'`
- research branch commit `3a3c1c9`: `./.lake/build/bin/acl2lean hints acl2_samples/2009-log2.lisp nbr-calls-flog2-is-logarithmic | sed -n '1,120p'`
- research branch commit `3a3c1c9`: `lake build`
- research branch commit `3a3c1c9`: `uv run python Verify.py`
- pushed research branch commit `3a3c1c9` to `origin/autoresearch/mar19-acl2lean`
- research branch commit `3a3c1c9`: `lake exe acl2lean ci autoresearch/mar19-acl2lean` showed the new GitHub Actions run for that push in progress
- `gh run watch 23334634497 --exit-status` succeeded for GitHub Actions run `23334634497`

Outcome:

- keep
- not promoted to `main` yet

Notes:

- this is the first Lean-side step that interprets the dynamic hint-generator output as replay state rather than only parsing and displaying individual actions
- real `die-hard` artifacts now surface theorem-local theory/use timelines plus `do-not-induct` / `otf-flg`, while `make-prog1-correct` surfaces ACL2's chosen induction candidate as a first-class summary instead of burying it in notes
- I did not promote this slice to `main` yet because it still depends on the research-branch dynamic proof-mode path; the likely promotion boundary is a coherent batch that includes dynamic extraction, structured payload decoding, and this first replay-state interpretation layer

Next best ideas:

1. execute the interpreted replay state against Lean goals, starting with theory disables and simple theorem/instance `use` steps instead of only surfacing them in the CLI/UI
2. add the same replay-state treatment for `split-goal` and `typed-term` actions so those dynamic hints also stop relying on flat summaries
3. decide whether the current dynamic hint stack from ACL2 extraction through replay-state interpretation is now coherent enough for a `main` promotion batch

## 2026-03-20 Iteration 33

Completed this iteration:

- added dedicated Lean-side `SplitGoalPayload` and `TypedTermPayload` decoding in `ACL2Lean.HintBridge`, so dynamic ACL2 splitter notes and typed-term observations no longer stop at flat action summaries once they cross back into Lean
- extended `DynamicAction.structuredLines` and `DynamicArtifact.replayState` to normalize `split-goal` into a checkpoint-local split timeline and `typed-term` into parsed typed-term foci, instead of leaving both paths outside the interpreted replay summary
- updated `acl2lean hints` to render `splitter` / `split-term` fields on actions plus `split-timeline` and normalized `typed-terms` entries under `replay-state:`
- updated `ACL2Lean.ProofMode` to surface the same structure through dynamic checkpoint/action notes and next-move guidance, including `action-splitter`, `action-split-term`, and `action-typed-term`
- added Lean guard coverage for the new payload parsers and replay-state/proof-mode surfaces, and updated `README.md`, `ACL2_SPEC.md`, and `docs/acl-proof-mode.md` to describe the wider replay-state model
- tracked the slice in Linear as `ALOK-573`

Verification:

- research branch commit `05a84e6`: `lean-lsp-mcp` diagnostics on `ACL2Lean/HintBridge.lean`
- research branch commit `05a84e6`: `lake build ACL2Lean.HintBridge`
- research branch commit `05a84e6`: `lake build ACL2Lean.ProofMode Main`
- research branch commit `05a84e6`: `lake build acl2lean`
- research branch commit `05a84e6`: `./.lake/build/bin/acl2lean hints acl2_samples/die-hard-work.lisp exists-gcd-prog | sed -n '82,160p'`
- research branch commit `05a84e6`: `./.lake/build/bin/acl2lean hints acl2_samples/2009-log2.lisp natp-clog2 | sed -n '34,90p'`
- research branch commit `05a84e6`: `lake build`
- research branch commit `05a84e6`: `uv run python scripts/test_acl2_hint_bridge.py`
- research branch commit `05a84e6`: `uv run python Verify.py`

Outcome:

- keep
- not promoted to `main` yet

Notes:

- this closes the remaining replay-state/display gap for two theorem-local hint classes that ACL2 emits frequently in the local corpus: splitter guidance and typed-term focus
- real `exists-gcd-prog` output now carries a parsed `splitter: if-intro` plus `split-timeline: splitter @ Goal'' ...`, and real `natp-clog2` output now renders the normalized typed-term directly in both the action details and replay summary
- I did not promote this slice to `main` yet because it still deepens the research-branch dynamic proof-mode stack; the cleaner mainline boundary is likely the whole dynamic hint bridge batch once replay execution begins

Next best ideas:

1. execute the interpreted replay state against Lean goals, starting with checkpoint-local split guidance, theory disables, and simple theorem/instance `use` steps
2. use the new split timeline and typed-term focus to group proof-mode next moves by checkpoint instead of listing all ACL2 suggestions flatly
3. decide whether the dynamic hint bridge from ACL2 extraction through replay-state normalization is now coherent enough for a single `main` promotion batch

## 2026-03-20 Iteration 34

Completed this iteration:

- added a Lean-side `SummaryRule` parser in `ACL2Lean.HintBridge`, so dynamic ACL2 `Rules:` summary entries like `(:REWRITE ...)`, `(:DEFINITION ...)`, `(:TYPE-PRESCRIPTION ...)`, and fake-rune markers no longer stay trapped as opaque strings once they cross back into Lean
- taught `DynamicArtifact` to normalize those summary rules into structured rule-kind/target summaries and updated `acl2lean hints` to print the normalized form on real theorem-local artifacts
- updated `ACL2Lean.ProofMode.dynamicRunes` so the infoview rune pane now carries explicit `summary-rule ...` entries instead of raw ACL2 s-expressions, which is a better bridge toward later Lean-side simp/grind configuration
- added Lean guard coverage for summary-rule parsing and proof-mode rune surfacing, and documented the new oracle surface in `README.md`, `ACL2_SPEC.md`, and `docs/acl-proof-mode.md`
- tracked the slice in Linear as `ALOK-574`

Verification:

- research branch commit `ff8dd19`: `lean-lsp-mcp` diagnostics on `ACL2Lean/HintBridge.lean`
- research branch commit `ff8dd19`: `lean-lsp-mcp` diagnostics on `ACL2Lean/ProofMode.lean`
- research branch commit `ff8dd19`: `lake build ACL2Lean.HintBridge ACL2Lean.ProofMode Main`
- research branch commit `ff8dd19`: `lake build acl2lean`
- research branch commit `ff8dd19`: `./.lake/build/bin/acl2lean hints acl2_samples/2009-log2.lisp nbr-calls-flog2-is-logarithmic | sed -n '1,24p'`
- research branch commit `ff8dd19`: `./.lake/build/bin/acl2lean hints acl2_samples/die-hard-work.lisp 'mod-+-*-floor-gcd' | sed -n '1,24p'`
- research branch commit `ff8dd19`: `./.lake/build/bin/acl2lean hints acl2_samples/apply-model-apply.lisp 'ev$-def-fact' | sed -n '1,24p'`
- research branch commit `ff8dd19`: `lake build`
- research branch commit `ff8dd19`: `uv run python Verify.py`
- pushed research branch commit `ff8dd19` to `origin/autoresearch/mar19-acl2lean`
- research branch commit `ff8dd19`: `lake exe acl2lean ci autoresearch/mar19-acl2lean` reported fresh GitHub Actions run `23335463332` in progress
- `gh run watch 23335463332 --exit-status` succeeded for GitHub Actions run `23335463332`

Outcome:

- keep
- not promoted to `main` yet

Notes:

- this closes another display-only gap in the hint-generator path: ACL2’s own `Rules:` summary is now parsed back into Lean structure instead of being stranded as raw text
- real `2009-log2`, `die-hard`, and `apply-model` outputs now show normalized summary rules such as `rewrite nbr-calls-flog2-upper-bound`, `definition floor`, and `elim car-cdr-elim`, which is a cleaner substrate for future rune-set / simp-set mapping
- I did not promote this slice to `main` yet because it still deepens the research-branch dynamic proof-mode stack; the cleaner promotion boundary remains a coherent batch that starts using these normalized oracle artifacts for checked replay

Next best ideas:

1. fold the normalized summary rules into replay-state or a dedicated active-rune model instead of leaving them only in CLI/proof-mode display surfaces
2. use the parsed summary-rule kinds plus the existing theory timeline to infer which ACL2 rune classes should map to Lean simp lemmas versus grind hints
3. start executing the now-structured oracle data against Lean goals, beginning with simple `use`, theory-disable, and splitter-guided replay steps

## 2026-03-20 Iteration 35

Completed this iteration:

- added a Lean-side `DynamicRuneProfile` in `ACL2Lean.HintBridge` that groups dynamic ACL2 `Rules:` summaries by ACL2 rule class instead of leaving them as flat `summary-rule ...` strings
- taught that rune-profile layer to accumulate concrete theory guidance from parsed dynamic `:IN-THEORY`, `disable-rule`, and `disable-definition` actions, while still preserving opaque theory combinator context when ACL2 does not expose a direct enable/disable delta
- derived heuristic `lean-simp-candidates` and `lean-grind-candidates` from the rune profile so the dynamic hint path now exposes a compact replay-facing bridge toward Lean configuration rather than only display text
- updated `acl2lean hints` to print a new `rune-profile:` block on real theorem-local artifacts, and updated `ACL2Lean.ProofMode` to consume `runeProfile` in the rune pane, notes, and next-move suggestions instead of reusing flat `summary-rule` / `theory-step` strings
- added Lean guard coverage for rune-profile interpretation and updated `README.md`, `ACL2_SPEC.md`, and `docs/acl-proof-mode.md` to document the new state model
- tracked the slice in Linear as `ALOK-575`

Verification:

- research branch commit `3c5fbbe`: `lake build ACL2Lean.HintBridge`
- research branch commit `3c5fbbe`: `lake build ACL2Lean.ProofMode Main`
- research branch commit `3c5fbbe`: `lake build acl2lean`
- research branch commit `3c5fbbe`: `./.lake/build/bin/acl2lean hints acl2_samples/2009-log2.lisp nbr-calls-flog2-is-logarithmic | sed -n '1,120p'`
- research branch commit `3c5fbbe`: `./.lake/build/bin/acl2lean hints acl2_samples/die-hard-work.lisp 'mod-+-*-floor-gcd' | sed -n '1,160p'`
- research branch commit `3c5fbbe`: `./.lake/build/bin/acl2lean hints acl2_samples/apply-model-apply.lisp 'ev$-def-fact' | sed -n '1,150p'`
- research branch commit `3c5fbbe`: `lake build`
- research branch commit `3c5fbbe`: `uv run python scripts/test_acl2_hint_bridge.py`
- research branch commit `3c5fbbe`: `uv run python Verify.py`
- pushed research branch commit `3c5fbbe` to `origin/autoresearch/mar19-acl2lean`
- research branch commit `3c5fbbe`: `lake exe acl2lean ci autoresearch/mar19-acl2lean` reported fresh GitHub Actions run `23335965119` in progress
- `gh run watch 23335965119 --exit-status` succeeded for GitHub Actions run `23335965119`

Outcome:

- keep
- not promoted to `main` yet

Notes:

- this is the first dynamic-hint slice that interprets ACL2 rule usage and theory adjustments into a compact Lean-side rune state instead of leaving them as disconnected display strings
- real `2009-log2`, `die-hard`, and `apply-model` artifacts now show `rune-profile:` sections with ACL2 rule-class buckets, theory enables/disables, and heuristic `lean-simp-candidates` / `lean-grind-candidates`
- I did not promote this slice to `main` yet because it still deepens the research-branch dynamic proof-mode stack; the cleaner promotion boundary remains “first checked replay step that consumes the dynamic oracle state” rather than another display-only improvement

Next best ideas:

1. execute `runeProfile` plus `replayState.useTimeline` against real Lean goals, starting with theory disables and simple theorem/instance `use` steps
2. thread `runeProfile`'s `lean-simp-candidates` / `lean-grind-candidates` into actual Lean replay configuration instead of only surfacing them in the CLI and proof-mode notes
3. decide whether the dynamic hint stack from extraction through `runeProfile` is now coherent enough for a mainline promotion batch once one checked replay action lands

## 2026-03-20 Iteration 36

Completed this iteration:

- extended `ACL2Lean/Imported/Log2Replay.lean` with public imported theorem reconstructions for `nbr-calls-flog2-lower-bound`, `nbr-calls-flog2-upper-bound`, and `nbr-calls-flog2-is-logarithmic`
- added small arithmetic normalization lemmas for `2 + flog2`, `1 + 2 * flog2`, and `2 + 2 * flog2` so the new `flog2` bound proofs stay short and kernel-checked over the existing `Nat` semantic mirror
- connected the checked theorem bundle back to the hint-generator story in `README.md` and `ACL2_SPEC.md`: ACL2's theorem-local `:USE NBR-CALLS-FLOG2-UPPER-BOUND` guidance for `nbr-calls-flog2-is-logarithmic` now has a matching imported Lean theorem instead of only a parsed action record
- tracked the slice in Linear as `ALOK-576`

Verification:

- research branch commit `ef36aa2`: `lean-lsp-mcp` diagnostics on `ACL2Lean/Imported/Log2Replay.lean`
- research branch commit `ef36aa2`: `lake build ACL2Lean.Imported.Log2Replay`
- research branch commit `ef36aa2`: `lake build`
- research branch commit `ef36aa2`: `uv run python Verify.py`
- research branch commit `ef36aa2`: `./.lake/build/bin/acl2lean hints acl2_samples/2009-log2.lisp nbr-calls-flog2-is-logarithmic | sed -n '1,140p'`
- research branch commit `ef36aa2`: `./.lake/build/bin/acl2lean eval-in acl2_samples/2009-log2.lisp "(nbr-calls-flog2 33)"`
- research branch commit `ef36aa2`: `./.lake/build/bin/acl2lean eval-in acl2_samples/2009-log2.lisp "(flog2 33)"`
- research branch commit `ef36aa2`: `printf 'import ACL2Lean.Imported.Log2Replay\n#print axioms ACL2.Imported.Log2Replay.nbr_calls_flog2_lower_bound\n#print axioms ACL2.Imported.Log2Replay.nbr_calls_flog2_upper_bound\n#print axioms ACL2.Imported.Log2Replay.nbr_calls_flog2_is_logarithmic\n' | lake env lean /dev/stdin`
- pushed research branch commit `ef36aa2` to `origin/autoresearch/mar19-acl2lean`
- research branch commit `ef36aa2`: `lake exe acl2lean ci autoresearch/mar19-acl2lean` reported fresh GitHub Actions run `23336875979` in progress
- `gh run watch 23336875979 --exit-status` succeeded for GitHub Actions run `23336875979`
- promoted the stable slice to `main` as `5355624`
- on `main`, a stale `.lake` artifact from the older toolchain blocked the first targeted build; after `lake clean`, both `lake build` and `uv run python Verify.py` passed
- on `main`, `gh run watch 23336843214 --exit-status` succeeded for GitHub Actions run `23336843214`

Outcome:

- keep
- promoted to `main`

Notes:

- this is the first checked imported-theorem slice in the repo that directly lands on a real theorem named by the dynamic ACL2 oracle path, not just on a display-only hint or normalized action payload
- the `2009-log2` bundle now contains the exact `nbr-calls-flog2-upper-bound` theorem that ACL2 recommends via `:USE` when proving `nbr-calls-flog2-is-logarithmic`, which makes that oracle output immediately more actionable for later replay work
- I left the actual dynamic-action-to-Lean-goal execution step for a follow-up iteration; this batch makes the target theorem available and checked first, which is a cleaner promotion boundary

Next best ideas:

1. resolve dynamic `useTimeline` theorem names against imported Lean declarations automatically so `acl2lean hints` and proof-mode can distinguish available replay targets from merely named ACL2 guidance
2. execute the `nbr-calls-flog2-is-logarithmic` dynamic `:USE` action against a real Lean proof state as the first checked replay experiment driven by oracle data
3. generalize the `Log2Replay` import pattern so more ACL2 theorem clusters can expose oracle-named support lemmas before the full generic replay engine lands
