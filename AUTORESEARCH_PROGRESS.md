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
