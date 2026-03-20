#!/usr/bin/env python3

from pathlib import Path
from tempfile import TemporaryDirectory
from textwrap import dedent
import unittest

import acl2_hint_bridge as bridge


class HintBridgeParsingTests(unittest.TestCase):
    def test_multiline_warnings_and_summary_rules(self) -> None:
        transcript = dedent(
            """
            ACL2 !>>
            ACL2 Warning [Subsume] in ( DEFTHM CLOG2-IS-CORRECT ...):  A newly
            proposed :REWRITE rule generated from CLOG2-IS-CORRECT probably subsumes
            the previously added :REWRITE rule CLOG2-IS-CORRECT-LOWER.

            Goal'

            Q.E.D.

            Summary
            Form:  ( DEFTHM CLOG2-IS-CORRECT ...)
            Rules: ((:COMPOUND-RECOGNIZER NATP-COMPOUND-RECOGNIZER)
                    (:COMPOUND-RECOGNIZER POSP-COMPOUND-RECOGNIZER)
                    (:REWRITE CLOG2-IS-CORRECT-LOWER)
                    (:REWRITE CLOG2-IS-CORRECT-UPPER))
            Warnings:  Subsume
            Time:  0.00 seconds (prove: 0.00, print: 0.00, other: 0.00)
            Prover steps counted:  183
             CLOG2-IS-CORRECT
            ACL2 !>>
            """
        ).splitlines()

        artifact = bridge.theorem_section(transcript, "clog2-is-correct")
        self.assertEqual(artifact["status"], "proved")
        self.assertEqual(
            artifact["summary_rules"],
            [
                "(:COMPOUND-RECOGNIZER NATP-COMPOUND-RECOGNIZER)",
                "(:COMPOUND-RECOGNIZER POSP-COMPOUND-RECOGNIZER)",
                "(:REWRITE CLOG2-IS-CORRECT-LOWER)",
                "(:REWRITE CLOG2-IS-CORRECT-UPPER)",
            ],
        )
        self.assertEqual(artifact["warning_kinds"], ["Subsume"])
        self.assertEqual(artifact["prover_steps"], 183)
        self.assertIn(
            "proposed :REWRITE rule generated from CLOG2-IS-CORRECT probably subsumes",
            artifact["warnings"][0],
        )

    def test_hint_events_and_warning_kinds(self) -> None:
        transcript = dedent(
            """
            ACL2 !>>
            ACL2 Warning [Use] in ( DEFTHM NBR-CALLS-FLOG2-IS-LOGARITHMIC ...):
            It is unusual to :USE the formula of an enabled :REWRITE or :DEFINITION
            rule, so you may want to consider disabling
            (:REWRITE NBR-CALLS-FLOG2-UPPER-BOUND) in the hint provided for Goal.

            Goal'''

            Q.E.D.

            Summary
            Form:  ( DEFTHM NBR-CALLS-FLOG2-IS-LOGARITHMIC ...)
            Rules: ((:REWRITE NBR-CALLS-FLOG2-LOWER-BOUND)
                    (:REWRITE NBR-CALLS-FLOG2-UPPER-BOUND))
            Hint-events: ((:USE NBR-CALLS-FLOG2-UPPER-BOUND))
            Warnings:  Use and Subsume
            Time:  0.00 seconds (prove: 0.00, print: 0.00, other: 0.00)
            Prover steps counted:  966
             NBR-CALLS-FLOG2-IS-LOGARITHMIC
            ACL2 !>>
            """
        ).splitlines()

        artifact = bridge.theorem_section(transcript, "nbr-calls-flog2-is-logarithmic")
        self.assertEqual(artifact["hint_events"], ["(:USE NBR-CALLS-FLOG2-UPPER-BOUND)"])
        self.assertEqual(artifact["warning_kinds"], ["Use", "Subsume"])
        self.assertIn("consider disabling", artifact["warnings"][0])

    def test_observations_checkpoints_and_induction_blocks(self) -> None:
        transcript = dedent(
            """
            ACL2 !>>
            ACL2 Observation in ( DEFTHM NATP-CLOG2 ...):  Our heuristics choose
            (CLOG2 N) as the :TYPED-TERM.

            Goal'

            ([ A key checkpoint:

            Goal'
            (IMPLIES (INTEGERP N)
                     (<= 0 (CLOG2 N)))

            *1 (Goal') is pushed for proof by induction.

            ])

            We will induct according to a scheme suggested by (CLOG2 N).
            This suggestion was produced using the :induction rule CLOG2.
            When applied to the goal at hand the above induction scheme produces
            eight nontautological subgoals.
            Subgoal *1/8

            *1 is COMPLETED!
            Thus key checkpoint Goal' is COMPLETED!

            Q.E.D.

            Summary
            Form:  ( DEFTHM NATP-CLOG2 ...)
            Rules: ((:INDUCTION CLOG2)
                    (:TYPE-PRESCRIPTION CLOG2))
            Time:  0.00 seconds (prove: 0.00, print: 0.00, other: 0.00)
            Prover steps counted:  1018
             NATP-CLOG2
            ACL2 !>>
            """
        ).splitlines()

        artifact = bridge.theorem_section(transcript, "natp-clog2")
        self.assertEqual(len(artifact["observations"]), 1)
        self.assertIn(":TYPED-TERM", artifact["observations"][0])
        self.assertEqual(len(artifact["checkpoints"]), 2)
        self.assertEqual(artifact["checkpoints"][0]["kind"], "key-checkpoint")
        self.assertEqual(artifact["checkpoints"][0]["label"], "Goal'")
        self.assertEqual(artifact["checkpoints"][1]["kind"], "subgoal")
        self.assertEqual(artifact["checkpoints"][1]["label"], "Subgoal *1/8")
        self.assertEqual(len(artifact["inductions"]), 1)
        self.assertIn(":induction rule CLOG2", artifact["inductions"][0])

    def test_raw_goal_and_subgoal_lines_become_checkpoints(self) -> None:
        transcript = dedent(
            """
            ACL2 !>>
            Goal'
            Goal''
            Subgoal 2
            Subgoal 1.1''

            Q.E.D.

            Summary
            Form:  ( DEFTHM MAKE-PROG-CORRECT ...)
            Rules: NIL
            Time:  0.00 seconds (prove: 0.00, print: 0.00, other: 0.00)
             MAKE-PROG-CORRECT
            ACL2 !>>
            """
        ).splitlines()

        artifact = bridge.theorem_section(transcript, "make-prog-correct")
        self.assertEqual(
            artifact["checkpoints"],
            [
                {"kind": "goal", "label": "Goal'", "text": "Goal'"},
                {"kind": "goal", "label": "Goal''", "text": "Goal''"},
                {"kind": "subgoal", "label": "Subgoal 2", "text": "Subgoal 2"},
                {"kind": "subgoal", "label": "Subgoal 1.1''", "text": "Subgoal 1.1''"},
            ],
        )

    def test_theorem_section_stays_local_with_multiple_summaries_in_one_prompt(self) -> None:
        transcript = dedent(
            """
            ACL2 !>>
            ACL2 Warning [Use] in ( DEFTHM FIRST-THM ...):
            Earlier theorem warning.

            Goal'

            Q.E.D.

            Summary
            Form:  ( DEFTHM FIRST-THM ...)
            Rules: ((:REWRITE FIRST-RULE))
            Warnings:  Use
            Time:  0.00 seconds (prove: 0.00, print: 0.00, other: 0.00)
            Prover steps counted:  7
             FIRST-THM
            ACL2 Observation in ( DEFTHM SECOND-THM ...):  Second theorem note.

            Subgoal 1

            Q.E.D.

            Summary
            Form:  ( DEFTHM SECOND-THM ...)
            Rules: ((:REWRITE SECOND-RULE))
            Time:  0.00 seconds (prove: 0.00, print: 0.00, other: 0.00)
            Prover steps counted:  11
             SECOND-THM
            ACL2 !>>
            """
        ).splitlines()

        artifact = bridge.theorem_section(transcript, "second-thm")
        self.assertEqual(artifact["status"], "proved")
        self.assertEqual(artifact["summary_form"], "( DEFTHM SECOND-THM ...)")
        self.assertEqual(artifact["summary_rules"], ["(:REWRITE SECOND-RULE)"])
        self.assertEqual(artifact["warning_kinds"], [])
        self.assertEqual(artifact["prover_steps"], 11)
        self.assertEqual(artifact["observations"], ["ACL2 Observation in ( DEFTHM SECOND-THM ...):  Second theorem note."])
        self.assertEqual(
            artifact["checkpoints"],
            [{"kind": "subgoal", "label": "Subgoal 1", "text": "Subgoal 1"}],
        )
        self.assertNotIn("Earlier theorem warning.", "\n".join(artifact["raw_excerpt"]))

    def test_theorem_section_respects_non_acl2_package_prompts(self) -> None:
        transcript = dedent(
            """
            ACL2 !>>
            Summary
            Form:  ( DEFTHM FIRST-THM ...)
            Rules: NIL
            Time:  0.00 seconds (prove: 0.00, print: 0.00, other: 0.00)
             FIRST-THM
            MODAPP !>>>(LOCAL
            ACL2 Observation in ( DEFTHM SECOND-THM ...):  Second theorem note.

            Goal'

            Q.E.D.

            Summary
            Form:  ( DEFTHM SECOND-THM ...)
            Rules: NIL
            Time:  0.00 seconds (prove: 0.00, print: 0.00, other: 0.00)
             SECOND-THM
            MODAPP !>>
            """
        ).splitlines()

        artifact = bridge.theorem_section(transcript, "second-thm")
        self.assertEqual(artifact["summary_form"], "( DEFTHM SECOND-THM ...)")
        self.assertEqual(artifact["observations"], ["ACL2 Observation in ( DEFTHM SECOND-THM ...):  Second theorem note."])
        self.assertEqual(
            artifact["checkpoints"],
            [{"kind": "goal", "label": "Goal'", "text": "Goal'"}],
        )
        self.assertTrue(artifact["raw_excerpt"][0].startswith("MODAPP !>>>"))

    def test_load_failure_is_reported(self) -> None:
        transcript = dedent(
            """
            ACL2 !>>
            ACL2 Error in IN-PACKAGE:  The argument to IN-PACKAGE must be a known
            package name, but "MODAPP" is not.
            ******** FAILED ********
            ACL2 !>
            """
        ).splitlines()

        artifact = bridge.theorem_section(transcript, "apply$-prim-meta-fn-correct")
        self.assertEqual(artifact["status"], "failed")
        self.assertIn("IN-PACKAGE", artifact["summary_form"])
        self.assertTrue(artifact["raw_excerpt"])

    def test_resolve_load_plans_for_excerpted_samples(self) -> None:
        with TemporaryDirectory() as tmp_dir:
            tmp = Path(tmp_dir)
            repo_root = tmp / "repo"
            sample_dir = repo_root / "acl2_samples"
            sample_dir.mkdir(parents=True)

            die_hard_sample = sample_dir / "die-hard-work.lisp"
            die_hard_sample.write_text("; excerpted sample\n", encoding="utf-8")

            apply_sample = sample_dir / "apply-model-apply-prim.lisp"
            apply_sample.write_text("; excerpted sample\n", encoding="utf-8")

            system_root = tmp / "acl2-books"
            die_hard_book = system_root / "projects" / "die-hard-bottle-game" / "work.lisp"
            die_hard_book.parent.mkdir(parents=True)
            die_hard_book.write_text("; canonical work book\n", encoding="utf-8")

            apply_dir = system_root / "projects" / "apply-model"
            apply_dir.mkdir(parents=True)
            portcullis = apply_dir / "portcullis.acl2"
            portcullis.write_text("; portcullis\n", encoding="utf-8")
            apply_book = apply_dir / "apply-prim.lisp"
            apply_book.write_text("; canonical apply-prim book\n", encoding="utf-8")

            die_hard_plans = bridge.resolve_load_plans(str(die_hard_sample), system_root=system_root)
            self.assertEqual(die_hard_plans[0].book, die_hard_sample.resolve())
            self.assertTrue(any(plan.book == die_hard_book for plan in die_hard_plans))

            apply_plans = bridge.resolve_load_plans(str(apply_sample), system_root=system_root)
            self.assertTrue(
                any(
                    plan.book == apply_sample.resolve() and plan.preludes == (portcullis,)
                    for plan in apply_plans
                )
            )
            self.assertTrue(any(plan.book == apply_book for plan in apply_plans))


if __name__ == "__main__":
    unittest.main()
