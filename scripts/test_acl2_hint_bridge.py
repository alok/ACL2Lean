#!/usr/bin/env python3

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
        self.assertEqual(len(artifact["checkpoints"]), 1)
        self.assertEqual(artifact["checkpoints"][0]["label"], "Goal'")
        self.assertEqual(len(artifact["inductions"]), 1)
        self.assertIn(":induction rule CLOG2", artifact["inductions"][0])


if __name__ == "__main__":
    unittest.main()
