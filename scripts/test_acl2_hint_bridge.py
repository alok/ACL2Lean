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
        self.assertTrue(
            any(
                action["kind"] == "use"
                and action["summary"] == "use NBR-CALLS-FLOG2-UPPER-BOUND"
                and action["goal_target"] is None
                and action["targets"] == ["NBR-CALLS-FLOG2-UPPER-BOUND"]
                for action in artifact["actions"]
            )
        )
        self.assertTrue(
            any(
                action["kind"] == "disable-rule"
                and action["summary"] == "disable (:REWRITE NBR-CALLS-FLOG2-UPPER-BOUND) in Goal"
                and action["goal_target"] == "Goal"
                and action["targets"] == ["(:REWRITE NBR-CALLS-FLOG2-UPPER-BOUND)", "Goal"]
                for action in artifact["actions"]
            )
        )
        self.assertTrue(
            any(
                action["kind"] == "use"
                and action["source"] == "warning"
                and action["summary"] == "use NBR-CALLS-FLOG2-UPPER-BOUND in Goal"
                and action["goal_target"] == "Goal"
                and action["targets"] == ["NBR-CALLS-FLOG2-UPPER-BOUND", "Goal"]
                for action in artifact["actions"]
            )
        )

    def test_use_warnings_preserve_goal_targeting(self) -> None:
        transcript = dedent(
            """
            ACL2 !>>
            ACL2 Warning [Use] in ( DEFTHM PAIR-POW-LOG-IS-CORRECT ...):  It is
            unusual to :USE the formula of an enabled :REWRITE or :DEFINITION rule,
            so you may want to consider disabling (:REWRITE PAIR-POW-2N-2N+1) in
            the hint provided for Subgoal *1/2.  See :DOC using-enabled-rules.

            ACL2 Warning [Use] in ( DEFTHM PAIR-POW-LOG-IS-CORRECT ...):  It is
            unusual to :USE the formula of an enabled :REWRITE or :DEFINITION rule,
            so you may want to consider disabling (:REWRITE PAIR-POW-2N-2N+1) in
            the hint provided for Subgoal *1/1.  See :DOC using-enabled-rules.

            Q.E.D.

            Summary
            Form:  ( DEFTHM PAIR-POW-LOG-IS-CORRECT ...)
            Rules: NIL
            Hint-events: ((:USE PAIR-POW-2N-2N+1))
            Warnings:  Use
            Time:  0.00 seconds (prove: 0.00, print: 0.00, other: 0.00)
             PAIR-POW-LOG-IS-CORRECT
            ACL2 !>>
            """
        ).splitlines()

        artifact = bridge.theorem_section(transcript, "pair-pow-log-is-correct")
        targeted_uses = {
            tuple(action["targets"])
            for action in artifact["actions"]
            if action["kind"] == "use" and action["source"] == "warning"
        }
        self.assertEqual(
            targeted_uses,
            {
                ("PAIR-POW-2N-2N+1", "Subgoal *1/2"),
                ("PAIR-POW-2N-2N+1", "Subgoal *1/1"),
            },
        )

    def test_use_warning_with_multiple_rules_splits_actions(self) -> None:
        transcript = dedent(
            """
            ACL2 !>>
            ACL2 Warning [Use] in ( DEFTHM LEMMA-5-D ...):  It is unusual to :USE
            the formula of an enabled :REWRITE or :DEFINITION rule, so you may
            want to consider disabling (:REWRITE LEMMA-5-A) and (:REWRITE LEMMA-5-C)
            in the hint provided for Goal.  See :DOC using-enabled-rules.

            Q.E.D.

            Summary
            Form:  ( DEFTHM LEMMA-5-D ...)
            Rules: NIL
            Warnings:  Use
            Time:  0.00 seconds (prove: 0.00, print: 0.00, other: 0.00)
             LEMMA-5-D
            ACL2 !>>
            """
        ).splitlines()

        artifact = bridge.theorem_section(transcript, "lemma-5-d")
        warning_uses = {
            tuple(action["targets"])
            for action in artifact["actions"]
            if action["kind"] == "use" and action["source"] == "warning"
        }
        disable_targets = {
            tuple(action["targets"])
            for action in artifact["actions"]
            if action["kind"] == "disable-rule"
        }
        self.assertEqual(
            warning_uses,
            {
                ("LEMMA-5-A", "Goal"),
                ("LEMMA-5-C", "Goal"),
            },
        )
        self.assertEqual(
            disable_targets,
            {
                ("(:REWRITE LEMMA-5-A)", "Goal"),
                ("(:REWRITE LEMMA-5-C)", "Goal"),
            },
        )

    def test_subsume_warnings_become_overlap_actions(self) -> None:
        transcript = dedent(
            """
            ACL2 !>>
            ACL2 Warning [Subsume] in ( DEFTHM NBR-CALLS-FLOG2-IS-LOGARITHMIC ...):
            A newly proposed :REWRITE rule generated from NBR-CALLS-FLOG2-IS-LOGARITHMIC
            probably subsumes the previously added :REWRITE rule
            NBR-CALLS-FLOG2-LOWER-BOUND, in the sense that the new rule will now
            probably be applied whenever the old rule would have been.

            ACL2 Warning [Subsume] in ( DEFTHM NBR-CALLS-FLOG2-IS-LOGARITHMIC ...):
            The previously added rule NBR-CALLS-FLOG2-LOWER-BOUND subsumes a newly
            proposed :REWRITE rule generated from NBR-CALLS-FLOG2-IS-LOGARITHMIC,
            in the sense that the old rule rewrites a more general target.

            ACL2 Warning [Subsume] in ( DEFTHM NBR-CALLS-FLOG2-IS-LOGARITHMIC ...):
            A newly proposed :REWRITE rule generated from NBR-CALLS-FLOG2-IS-LOGARITHMIC
            probably subsumes the previously added :REWRITE rule
            NBR-CALLS-FLOG2-UPPER-BOUND, in the sense that the new rule will now
            probably be applied whenever the old rule would have been.

            Goal'

            Q.E.D.

            Summary
            Form:  ( DEFTHM NBR-CALLS-FLOG2-IS-LOGARITHMIC ...)
            Rules: NIL
            Warnings:  Subsume
            Time:  0.00 seconds (prove: 0.00, print: 0.00, other: 0.00)
             NBR-CALLS-FLOG2-IS-LOGARITHMIC
            ACL2 !>>
            """
        ).splitlines()

        artifact = bridge.theorem_section(transcript, "nbr-calls-flog2-is-logarithmic")
        overlap_targets = {
            tuple(action["targets"])
            for action in artifact["actions"]
            if action["kind"] == "watch-rune-overlap"
        }
        self.assertEqual(
            overlap_targets,
            {
                ("NBR-CALLS-FLOG2-IS-LOGARITHMIC", "NBR-CALLS-FLOG2-LOWER-BOUND"),
                ("NBR-CALLS-FLOG2-IS-LOGARITHMIC", "NBR-CALLS-FLOG2-UPPER-BOUND"),
            },
        )

    def test_subsume_warning_with_quoted_rule_name_becomes_overlap_action(self) -> None:
        transcript = dedent(
            """
            ACL2 !>>
            ACL2 Warning [Subsume] in ( DEFTHM LEMMA-4 ...):  The previously added
            rule |(+ y x)| subsumes a newly proposed :REWRITE rule generated from
            LEMMA-4, in the sense that the old rule rewrites a more general target.
            Because the new rule will be tried first, it may nonetheless find application.

            Goal'

            Q.E.D.

            Summary
            Form:  ( DEFTHM LEMMA-4 ...)
            Rules: NIL
            Warnings:  Subsume
            Time:  0.00 seconds (prove: 0.00, print: 0.00, other: 0.00)
             LEMMA-4
            ACL2 !>>
            """
        ).splitlines()

        artifact = bridge.theorem_section(transcript, "lemma-4")
        self.assertTrue(
            any(
                action["kind"] == "watch-rune-overlap"
                and action["summary"] == "compare generated rewrite from LEMMA-4 with existing rewrite |(+ y x)|"
                and action["targets"] == ["LEMMA-4", "|(+ y x)|"]
                for action in artifact["actions"]
            )
        )

    def test_subsume_warning_with_plural_quoted_rule_names_splits_actions(self) -> None:
        transcript = dedent(
            """
            ACL2 !>>
            ACL2 Warning [Subsume] in ( DEFTHM LEMMA-3 ...):  The previously added
            rules |(* x (+ y z))|, |(* (* x y) z)| and |(* y x)| subsume a newly
            proposed :REWRITE rule generated from LEMMA-3, in the sense that the
            old rules rewrite more general targets.  Because the new rule will
            be tried first, it may nonetheless find application.

            Goal'

            Q.E.D.

            Summary
            Form:  ( DEFTHM LEMMA-3 ...)
            Rules: NIL
            Warnings:  Subsume
            Time:  0.00 seconds (prove: 0.00, print: 0.00, other: 0.00)
             LEMMA-3
            ACL2 !>>
            """
        ).splitlines()

        artifact = bridge.theorem_section(transcript, "lemma-3")
        overlap_targets = {
            tuple(action["targets"])
            for action in artifact["actions"]
            if action["kind"] == "watch-rune-overlap"
        }
        self.assertEqual(
            overlap_targets,
            {
                ("LEMMA-3", "|(* x (+ y z))|"),
                ("LEMMA-3", "|(* (* x y) z)|"),
                ("LEMMA-3", "|(* y x)|"),
            },
        )

    def test_non_rec_warnings_become_disable_definition_actions(self) -> None:
        transcript = dedent(
            """
            ACL2 !>>
            ACL2 Warning [Non-rec] in ( DEFTHM NEXT-UNIQUE ...):  A :REWRITE rule
            generated from NEXT-UNIQUE will be triggered only by terms containing
            the function symbol NEXT, which has a non-recursive definition.  Unless
            this definition is disabled, this rule is unlikely ever to be used.

            Goal'

            Q.E.D.

            Summary
            Form:  ( DEFTHM NEXT-UNIQUE ...)
            Rules: NIL
            Warnings:  Non-rec
            Time:  0.01 seconds (prove: 0.00, print: 0.00, other: 0.01)
             NEXT-UNIQUE
            ACL2 !>>
            """
        ).splitlines()

        artifact = bridge.theorem_section(transcript, "next-unique")
        self.assertTrue(
            any(
                action["kind"] == "disable-definition"
                and action["summary"] == "disable (:DEFINITION NEXT) so rewrite from NEXT-UNIQUE can fire"
                and action["targets"] == ["(:DEFINITION NEXT)", "NEXT-UNIQUE"]
                for action in artifact["actions"]
            )
        )

    def test_non_rec_warning_for_free_variable_search_becomes_disable_definition_action(self) -> None:
        transcript = dedent(
            """
            ACL2 !>>
            ACL2 Warning [Free] in ( DEFTHM LEMMA-2 ...):  A :REWRITE rule generated
            from LEMMA-2 contains the free variable Y.  This variable will be chosen
            by searching for an instance of (POSP Y) in the context of the term
            being rewritten.  This is generally a severe restriction on the applicability
            of a :REWRITE rule.  See :DOC free-variables.

            ACL2 Warning [Non-rec] in ( DEFTHM LEMMA-2 ...):  As noted, we will
            instantiate the free variable, Y, of a :REWRITE rule generated from
            LEMMA-2, by searching for the hypothesis shown above.  However, this
            hypothesis mentions the function symbol POSP, which has a non-recursive
            definition.  Unless this definition is disabled, that function symbol
            is unlikely to occur in the conjecture being proved and hence the search
            for the required hypothesis will likely fail.

            Goal'

            Q.E.D.

            Summary
            Form:  ( DEFTHM LEMMA-2 ...)
            Rules: NIL
            Warnings:  Free and Non-rec
            Time:  0.00 seconds (prove: 0.00, print: 0.00, other: 0.00)
             LEMMA-2
            ACL2 !>>
            """
        ).splitlines()

        artifact = bridge.theorem_section(transcript, "lemma-2")
        self.assertTrue(
            any(
                action["kind"] == "disable-definition"
                and action["summary"] == "disable (:DEFINITION POSP) so free-variable search for Y via (POSP Y) can succeed in LEMMA-2"
                and action["targets"] == ["(:DEFINITION POSP)", "LEMMA-2", "Y", "(POSP Y)"]
                for action in artifact["actions"]
            )
        )

    def test_non_rec_warnings_expand_plural_definition_lists(self) -> None:
        transcript = dedent(
            """
            ACL2 !>>
            ACL2 Warning [Non-rec] in ( DEFTHM INV-INITIAL-STATE ...):  A :REWRITE
            rule generated from INV-INITIAL-STATE will be triggered only by terms
            containing the function symbols INV and INITIAL-STATE, which have non-
            recursive definitions.  Unless these definitions are disabled, this
            rule is unlikely ever to be used.

            Goal'

            Q.E.D.

            Summary
            Form:  ( DEFTHM INV-INITIAL-STATE ...)
            Rules: NIL
            Warnings:  Non-rec
            Time:  0.00 seconds (prove: 0.00, print: 0.00, other: 0.00)
             INV-INITIAL-STATE
            ACL2 !>>
            """
        ).splitlines()

        artifact = bridge.theorem_section(transcript, "inv-initial-state")
        disable_targets = {
            tuple(action["targets"])
            for action in artifact["actions"]
            if action["kind"] == "disable-definition"
        }
        self.assertEqual(
            disable_targets,
            {
                ("(:DEFINITION INV)", "INV-INITIAL-STATE"),
                ("(:DEFINITION INITIAL-STATE)", "INV-INITIAL-STATE"),
            },
        )

    def test_non_rec_linear_warnings_preserve_rule_class(self) -> None:
        transcript = dedent(
            """
            ACL2 !>>
            ACL2 Warning [Non-rec] in ( DEFTHM POSITIVE-FLOOR-LITTLE-LEMMA ...):
            A :LINEAR rule generated from POSITIVE-FLOOR-LITTLE-LEMMA will be triggered
            only by terms containing the function symbol FLOOR, which has a non-
            recursive definition.  Unless this definition is disabled, such triggering
            terms are unlikely to arise and so POSITIVE-FLOOR-LITTLE-LEMMA is unlikely
            to ever be used.

            Goal'

            Q.E.D.

            Summary
            Form:  ( DEFTHM POSITIVE-FLOOR-LITTLE-LEMMA ...)
            Rules: NIL
            Warnings:  Non-rec
            Time:  0.01 seconds (prove: 0.00, print: 0.00, other: 0.01)
             POSITIVE-FLOOR-LITTLE-LEMMA
            ACL2 !>>
            """
        ).splitlines()

        artifact = bridge.theorem_section(transcript, "positive-floor-little-lemma")
        self.assertTrue(
            any(
                action["kind"] == "disable-definition"
                and action["summary"] == "disable (:DEFINITION FLOOR) so :LINEAR from POSITIVE-FLOOR-LITTLE-LEMMA can fire"
                and action["targets"] == ["(:DEFINITION FLOOR)", "POSITIVE-FLOOR-LITTLE-LEMMA"]
                for action in artifact["actions"]
            )
        )

    def test_non_rec_forward_chaining_warning_becomes_disable_definition_action(self) -> None:
        transcript = dedent(
            """
            MODAPP !>>
            ACL2 Observation in ( DEFTHM BADGE-TYPE ...):  The :TRIGGER-TERMS for
            the :FORWARD-CHAINING rule BADGE-TYPE will consist of the list containing
            (BADGE FN).

            ACL2 Warning [Non-rec] in ( DEFTHM BADGE-TYPE ...):  The term (BADGE FN)
            contains the function symbol BADGE, which has a non-recursive definition.
            Unless this definition is disabled, (BADGE FN) is unlikely ever to
            occur as a trigger for BADGE-TYPE.

            Goal'

            Q.E.D.

            Summary
            Form:  ( DEFTHM BADGE-TYPE ...)
            Rules: NIL
            Warnings:  Non-rec
            Time:  0.00 seconds (prove: 0.00, print: 0.00, other: 0.00)
             BADGE-TYPE
            MODAPP !>>
            """
        ).splitlines()

        artifact = bridge.theorem_section(transcript, "badge-type")
        self.assertTrue(
            any(
                action["kind"] == "disable-definition"
                and action["summary"] == "disable (:DEFINITION BADGE) so trigger term (BADGE FN) can arise for BADGE-TYPE"
                and action["targets"] == ["(:DEFINITION BADGE)", "BADGE-TYPE", "(BADGE FN)"]
                for action in artifact["actions"]
            )
        )

    def test_free_warning_becomes_bind_free_variable_action(self) -> None:
        transcript = dedent(
            """
            ACL2 !>>
            ACL2 Warning [Free] in ( DEFTHM NATP-/-GCD-LITTLE-LEMMA ...):  A :REWRITE
            rule generated from NATP-/-GCD-LITTLE-LEMMA contains the free variable
            J.  This variable will be chosen by searching for an instance of
            (EQUAL (NONNEG-INT-MOD J GCD) 0) in the context of the term being rewritten.
            This is generally a severe restriction on the applicability of a :REWRITE
            rule.  See :DOC free-variables.

            Goal'

            Q.E.D.

            Summary
            Form:  ( DEFTHM NATP-/-GCD-LITTLE-LEMMA ...)
            Rules: NIL
            Warnings:  Free
            Time:  0.00 seconds (prove: 0.00, print: 0.00, other: 0.00)
             NATP-/-GCD-LITTLE-LEMMA
            ACL2 !>>
            """
        ).splitlines()

        artifact = bridge.theorem_section(transcript, "natp-/-gcd-little-lemma")
        self.assertTrue(
            any(
                action["kind"] == "bind-free-variable"
                and action["summary"] == "bind free variable J using (EQUAL (NONNEG-INT-MOD J GCD) 0)"
                and action["targets"] == ["J", "(EQUAL (NONNEG-INT-MOD J GCD) 0)"]
                for action in artifact["actions"]
            )
        )

    def test_free_warning_with_trigger_term_becomes_bind_free_variable_action(self) -> None:
        transcript = dedent(
            """
            ACL2 !>>
            ACL2 Warning [Free] in ( DEFTHM POSITIVE-FLOOR-LITTLE-LEMMA ...):
            A :LINEAR rule generated from POSITIVE-FLOOR-LITTLE-LEMMA will be triggered
            by the term (FLOOR I GCD).  When POSITIVE-FLOOR-LITTLE-LEMMA is triggered
            by (FLOOR I GCD) the variable J will be chosen by searching for an
            instance of (EQUAL (NONNEG-INT-MOD J GCD) '0) among the hypotheses
            of the conjecture being rewritten.  This is generally a severe restriction
            on the applicability of the :LINEAR rule.

            Goal'

            Q.E.D.

            Summary
            Form:  ( DEFTHM POSITIVE-FLOOR-LITTLE-LEMMA ...)
            Rules: NIL
            Warnings:  Free
            Time:  0.01 seconds (prove: 0.00, print: 0.00, other: 0.01)
             POSITIVE-FLOOR-LITTLE-LEMMA
            ACL2 !>>
            """
        ).splitlines()

        artifact = bridge.theorem_section(transcript, "positive-floor-little-lemma")
        self.assertTrue(
            any(
                action["kind"] == "bind-free-variable"
                and action["summary"] == "bind free variable J using (EQUAL (NONNEG-INT-MOD J GCD) '0) when rule sees (FLOOR I GCD)"
                and action["targets"] == [
                    "J",
                    "(EQUAL (NONNEG-INT-MOD J GCD) '0)",
                    "(FLOOR I GCD)",
                ]
                for action in artifact["actions"]
            )
        )

    def test_splitter_rules_become_split_actions(self) -> None:
        transcript = dedent(
            """
            ACL2 !>>
            Goal''

            Splitter note (see :DOC splitter) for Goal'' (2 subgoals).
              if-intro: ((:DEFINITION GCD-PROG!))

            Subgoal 2
            Subgoal 1

            Q.E.D.

            Summary
            Form:  ( DEFTHM EXISTS-GCD-PROG ...)
            Rules: NIL
            Splitter rules (see :DOC splitter):
              if-intro: ((:DEFINITION GCD-PROG!))
            Time:  0.06 seconds (prove: 0.06, print: 0.00, other: 0.00)
             EXISTS-GCD-PROG
            ACL2 !>>
            """
        ).splitlines()

        artifact = bridge.theorem_section(transcript, "exists-gcd-prog")
        self.assertEqual(artifact["splitter_rules"], ["if-intro: ((:DEFINITION GCD-PROG!))"])
        self.assertTrue(
            any(
                action["kind"] == "split-goal"
                and action["summary"] == "split using if-intro with ((:DEFINITION GCD-PROG!)) in Goal''"
                and action["goal_target"] == "Goal''"
                and action["targets"] == ["if-intro", "((:DEFINITION GCD-PROG!))", "Goal''"]
                for action in artifact["actions"]
            )
        )

    def test_multiline_splitter_rules_stay_grouped(self) -> None:
        transcript = dedent(
            """
            ACL2 !>>
            Splitter note (see :DOC splitter) for Goal (3 subgoals).
              if-intro: ((:DEFINITION NFIX)
                         (:DEFINITION NONNEG-INT-GCD))

            Subgoal 3
            Subgoal 2
            Subgoal 1

            Q.E.D.

            Summary
            Form:  ( DEFTHM NONNEG-INT-GCD-0 ...)
            Rules: NIL
            Splitter rules (see :DOC splitter):
              if-intro: ((:DEFINITION NFIX)
                         (:DEFINITION NONNEG-INT-GCD))
            Time:  0.00 seconds (prove: 0.00, print: 0.00, other: 0.00)
             NONNEG-INT-GCD-0
            ACL2 !>>
            """
        ).splitlines()

        artifact = bridge.theorem_section(transcript, "nonneg-int-gcd-0")
        self.assertEqual(
            artifact["splitter_rules"],
            ["if-intro: ((:DEFINITION NFIX)\n(:DEFINITION NONNEG-INT-GCD))"],
        )
        self.assertEqual(
            [
                action
                for action in artifact["actions"]
                if action["kind"] == "split-goal"
            ],
            [
                {
                    "kind": "split-goal",
                    "source": "splitter",
                    "summary": "split using if-intro with ((:DEFINITION NFIX) (:DEFINITION NONNEG-INT-GCD)) in Goal",
                    "goal_target": "Goal",
                    "targets": ["if-intro", "((:DEFINITION NFIX) (:DEFINITION NONNEG-INT-GCD))", "Goal"],
                    "detail": "if-intro: ((:DEFINITION NFIX)\n(:DEFINITION NONNEG-INT-GCD))",
                }
            ],
        )

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
        self.assertTrue(
            any(
                action["kind"] == "typed-term"
                and action["summary"] == "focus on typed term (CLOG2 N)"
                and action["targets"] == ["(CLOG2 N)"]
                for action in artifact["actions"]
            )
        )
        self.assertEqual(len(artifact["checkpoints"]), 2)
        self.assertEqual(artifact["checkpoints"][0]["kind"], "key-checkpoint")
        self.assertEqual(artifact["checkpoints"][0]["label"], "Goal'")
        self.assertEqual(artifact["checkpoints"][1]["kind"], "subgoal")
        self.assertEqual(artifact["checkpoints"][1]["label"], "Subgoal *1/8")
        self.assertEqual(
            artifact["progress"],
            [
                {
                    "kind": "induction-push",
                    "label": "*1 (Goal')",
                    "text": "*1 (Goal') is pushed for proof by induction.",
                },
                {
                    "kind": "subproof-complete",
                    "label": "*1",
                    "text": "*1 is COMPLETED!",
                },
                {
                    "kind": "checkpoint-complete",
                    "label": "Goal'",
                    "text": "Thus key checkpoint Goal' is COMPLETED!",
                },
            ],
        )
        self.assertEqual(len(artifact["inductions"]), 1)
        self.assertIn(":induction rule CLOG2", artifact["inductions"][0])
        self.assertIn("eight nontautological subgoals.", artifact["inductions"][0])
        self.assertTrue(
            any(
                action["kind"] == "induct"
                and action["summary"] == "induct on (CLOG2 N) using rule CLOG2"
                and action["targets"] == ["(CLOG2 N)", "CLOG2"]
                for action in artifact["actions"]
            )
        )

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

    def test_prompt_adjacent_goal_lines_become_checkpoints(self) -> None:
        transcript = dedent(
            """
            ACL2 !>>Goal'
            Goal''
            Goal'''    

            Q.E.D.

            Summary
            Form:  ( DEFTHM RENAMING-HACK-LEMMA ...)
            Rules: NIL
            Time:  0.00 seconds (prove: 0.00, print: 0.00, other: 0.00)
             RENAMING-HACK-LEMMA
            ACL2 !>>
            """
        ).splitlines()

        artifact = bridge.theorem_section(transcript, "renaming-hack-lemma")
        self.assertEqual(
            artifact["checkpoints"],
            [
                {"kind": "goal", "label": "Goal'", "text": "Goal'"},
                {"kind": "goal", "label": "Goal''", "text": "Goal''"},
                {"kind": "goal", "label": "Goal'''", "text": "Goal'''"},
            ],
        )
        self.assertEqual(artifact["raw_excerpt"][0], "ACL2 !>>")
        self.assertEqual(artifact["raw_excerpt"][1], "Goal'")

    def test_multiline_hint_events_stay_grouped_and_actionable(self) -> None:
        transcript = dedent(
            """
            ACL2 !>>

            Q.E.D.

            Summary
            Form:  ( DEFTHM THEORY-GUIDANCE ...)
            Rules: NIL
            Hint-events: ((:IN-THEORY (DISABLE FLOOR
                                       NONNEG-INT-GCD-IS-COMMON-DIVISOR))
                          (:EXPAND (NONNEG-INT-GCD 0 Q))
                          (:DO-NOT-INDUCT T))
            Time:  0.00 seconds (prove: 0.00, print: 0.00, other: 0.00)
             THEORY-GUIDANCE
            ACL2 !>>
            """
        ).splitlines()

        artifact = bridge.theorem_section(transcript, "theory-guidance")
        self.assertEqual(
            artifact["hint_events"],
            [
                "(:IN-THEORY (DISABLE FLOOR\nNONNEG-INT-GCD-IS-COMMON-DIVISOR))",
                "(:EXPAND (NONNEG-INT-GCD 0 Q))",
                "(:DO-NOT-INDUCT T)",
            ],
        )
        self.assertTrue(
            any(
                action["kind"] == "in-theory"
                and action["summary"] == "adjust theory (DISABLE FLOOR NONNEG-INT-GCD-IS-COMMON-DIVISOR)"
                and action["targets"] == ["(DISABLE FLOOR NONNEG-INT-GCD-IS-COMMON-DIVISOR)"]
                for action in artifact["actions"]
            )
        )
        self.assertTrue(
            any(
                action["kind"] == "expand"
                and action["summary"] == "expand (NONNEG-INT-GCD 0 Q)"
                and action["targets"] == ["(NONNEG-INT-GCD 0 Q)"]
                for action in artifact["actions"]
            )
        )
        self.assertTrue(
            any(
                action["kind"] == "do-not-induct"
                and action["summary"] == "do-not-induct T"
                and action["targets"] == ["T"]
                for action in artifact["actions"]
            )
        )

    def test_summary_use_lists_split_into_individual_actions(self) -> None:
        transcript = dedent(
            """
            ACL2 !>>

            Q.E.D.

            Summary
            Form:  ( DEFTHM SUMMARY-USE-LIST ...)
            Rules: NIL
            Hint-events: ((:USE (BASE-LEMMA HELPER-LEMMA))
                          (:USE ((:INSTANCE FOO (X A))
                                 (:INSTANCE BAR (Y B)))))
            Time:  0.00 seconds (prove: 0.00, print: 0.00, other: 0.00)
             SUMMARY-USE-LIST
            ACL2 !>>
            """
        ).splitlines()

        artifact = bridge.theorem_section(transcript, "summary-use-list")
        use_targets = [
            tuple(action["targets"])
            for action in artifact["actions"]
            if action["kind"] == "use"
        ]
        self.assertEqual(
            use_targets,
            [
                ("BASE-LEMMA",),
                ("HELPER-LEMMA",),
                ("(:INSTANCE FOO (X A))",),
                ("(:INSTANCE BAR (Y B))",),
            ],
        )

    def test_transcript_echoed_hint_events_are_recovered_from_defthm_form(self) -> None:
        transcript = dedent(
            """
            MODAPP !>>>
            (DEFTHM EV$-DEF-FACT
                     (IMPLIES (TAMEP X)
                              (EQUAL (EV$ X A)
                                     (APPLY$ (CAR X) (EV$-LIST (CDR X) A))))
                     :HINTS (("Goal" :EXPAND ((EV$ X A)))))

            Goal'

            Q.E.D.

            Summary
            Form:  ( DEFTHM EV$-DEF-FACT ...)
            Rules: NIL
            Time:  0.00 seconds (prove: 0.00, print: 0.00, other: 0.00)
             EV$-DEF-FACT
            MODAPP !>>
            """
        ).splitlines()

        artifact = bridge.theorem_section(transcript, "ev$-def-fact")
        self.assertEqual(artifact["hint_events"], ["(:EXPAND ((EV$ X A)))"])
        self.assertTrue(
            any(
                action["kind"] == "expand"
                and action["source"] == "transcript-hint"
                and action["summary"] == "expand ((EV$ X A)) in Goal"
                and action["goal_target"] == "Goal"
                and action["targets"] == ["((EV$ X A))", "Goal"]
                for action in artifact["actions"]
            )
        )

    def test_transcript_echoed_hint_events_recover_nested_local_defthm_hints(self) -> None:
        transcript = dedent(
            """
            MODAPP !>>>
            (LOCAL
             (DEFTHM APPLY$-BADGEP-HONS-GET-LEMMA
               (IMPLIES (AND (BADGE-TABLE-OKP ALIST)
                             (HONS-GET FN ALIST))
                        (APPLY$-BADGEP (CDR (HONS-GET FN ALIST))))
               :HINTS (("Goal" :IN-THEORY (ENABLE HONS-ASSOC-EQUAL)))))

            Goal'

            Q.E.D.

            Summary
            Form:  ( DEFTHM APPLY$-BADGEP-HONS-GET-LEMMA ...)
            Rules: NIL
            Time:  0.00 seconds (prove: 0.00, print: 0.00, other: 0.00)
             APPLY$-BADGEP-HONS-GET-LEMMA
            MODAPP !>>
            """
        ).splitlines()

        artifact = bridge.theorem_section(transcript, "apply$-badgep-hons-get-lemma")
        self.assertEqual(artifact["hint_events"], ["(:IN-THEORY (ENABLE HONS-ASSOC-EQUAL))"])
        self.assertTrue(
            any(
                action["kind"] == "in-theory"
                and action["source"] == "transcript-hint"
                and action["summary"] == "adjust theory (ENABLE HONS-ASSOC-EQUAL) in Goal"
                and action["goal_target"] == "Goal"
                and action["targets"] == ["(ENABLE HONS-ASSOC-EQUAL)", "Goal"]
                for action in artifact["actions"]
            )
        )

    def test_transcript_echoed_use_lists_split_and_keep_goal_targets(self) -> None:
        transcript = dedent(
            """
            ACL2 !>>>
            (DEFTHM TRANSCRIPT-USE-LIST
                     (IMPLIES (P X) (Q X))
                     :HINTS (("Goal" :USE ((:INSTANCE BASE-LEMMA (X X))
                                           (:INSTANCE HELPER-LEMMA (Y Y))))
                             ("Subgoal 2" :USE (SIDE-LEMMA AUX-LEMMA))))

            Goal'

            Q.E.D.

            Summary
            Form:  ( DEFTHM TRANSCRIPT-USE-LIST ...)
            Rules: NIL
            Time:  0.00 seconds (prove: 0.00, print: 0.00, other: 0.00)
             TRANSCRIPT-USE-LIST
            ACL2 !>>
            """
        ).splitlines()

        artifact = bridge.theorem_section(transcript, "transcript-use-list")
        transcript_uses = {
            (action["summary"], tuple(action["targets"]))
            for action in artifact["actions"]
            if action["kind"] == "use" and action["source"] == "transcript-hint"
        }
        self.assertEqual(
            transcript_uses,
            {
                (
                    "use (:INSTANCE BASE-LEMMA (X X)) in Goal",
                    ("(:INSTANCE BASE-LEMMA (X X))", "Goal"),
                ),
                (
                    "use (:INSTANCE HELPER-LEMMA (Y Y)) in Goal",
                    ("(:INSTANCE HELPER-LEMMA (Y Y))", "Goal"),
                ),
                ("use SIDE-LEMMA in Subgoal 2", ("SIDE-LEMMA", "Subgoal 2")),
                ("use AUX-LEMMA in Subgoal 2", ("AUX-LEMMA", "Subgoal 2")),
            },
        )

    def test_transcript_echoed_hint_actions_preserve_goal_targets(self) -> None:
        transcript = dedent(
            """
            ACL2 !>>>
            (DEFTHM TARGETED-TRANSCRIPT-HINTS
                     (IMPLIES (P X) (Q X))
                     :HINTS (("Goal" :USE BASE-LEMMA)
                             ("Goal'''" :EXPAND (FOO X))
                             ("Subgoal 2" :IN-THEORY (ENABLE BAR)
                                           :DO-NOT-INDUCT T)))

            Goal'

            Q.E.D.

            Summary
            Form:  ( DEFTHM TARGETED-TRANSCRIPT-HINTS ...)
            Rules: NIL
            Time:  0.00 seconds (prove: 0.00, print: 0.00, other: 0.00)
             TARGETED-TRANSCRIPT-HINTS
            ACL2 !>>
            """
        ).splitlines()

        artifact = bridge.theorem_section(transcript, "targeted-transcript-hints")
        self.assertEqual(
            artifact["hint_events"],
            [
                "(:USE BASE-LEMMA)",
                "(:EXPAND (FOO X))",
                "(:IN-THEORY (ENABLE BAR))",
                "(:DO-NOT-INDUCT T)",
            ],
        )
        self.assertTrue(
            any(
                action["kind"] == "use"
                and action["source"] == "transcript-hint"
                and action["summary"] == "use BASE-LEMMA in Goal"
                and action["goal_target"] == "Goal"
                and action["targets"] == ["BASE-LEMMA", "Goal"]
                for action in artifact["actions"]
            )
        )
        self.assertTrue(
            any(
                action["kind"] == "expand"
                and action["source"] == "transcript-hint"
                and action["summary"] == "expand (FOO X) in Goal'''"
                and action["goal_target"] == "Goal'''"
                and action["targets"] == ["(FOO X)", "Goal'''"]
                for action in artifact["actions"]
            )
        )
        self.assertTrue(
            any(
                action["kind"] == "in-theory"
                and action["source"] == "transcript-hint"
                and action["summary"] == "adjust theory (ENABLE BAR) in Subgoal 2"
                and action["goal_target"] == "Subgoal 2"
                and action["targets"] == ["(ENABLE BAR)", "Subgoal 2"]
                for action in artifact["actions"]
            )
        )
        self.assertTrue(
            any(
                action["kind"] == "do-not-induct"
                and action["source"] == "transcript-hint"
                and action["summary"] == "do-not-induct T in Subgoal 2"
                and action["goal_target"] == "Subgoal 2"
                and action["targets"] == ["T", "Subgoal 2"]
                for action in artifact["actions"]
            )
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

    def test_theorem_section_ignores_helper_theorems_after_target_summary(self) -> None:
        transcript = dedent(
            """
            ACL2 !>>>
            Goal'

            Q.E.D.

            Summary
            Form:  ( DEFTHM FLAG-LEMMA ...)
            Rules: NIL
            Hint-events: ((:USE FLAG-LEMMA))
            Time:  0.01 seconds (prove: 0.01, print: 0.00, other: 0.00)
            Prover steps counted:  13
            ACL2 Warning [Free] in ( DEFTHM HELPER-ONE ...):  Helper theorem warning.

            ACL2 Observation in ( DEFTHM HELPER-TWO ...):  Helper theorem note.

            Summary
            Form:  ( DEFTHM HELPER-ONE ...)
            Rules: NIL
            Warnings:  Free
            Time:  0.00 seconds (prove: 0.00, print: 0.00, other: 0.00)
             HELPER-ONE
             FLAG-LEMMA
            ACL2 !>>
            """
        ).splitlines()

        artifact = bridge.theorem_section(transcript, "flag-lemma")
        self.assertEqual(artifact["status"], "proved")
        self.assertEqual(artifact["summary_form"], "( DEFTHM FLAG-LEMMA ...)")
        self.assertEqual(artifact["hint_events"], ["(:USE FLAG-LEMMA)"])
        self.assertEqual(artifact["warning_kinds"], [])
        self.assertEqual(artifact["warnings"], [])
        self.assertEqual(artifact["observations"], [])
        self.assertNotIn("HELPER-ONE", "\n".join(artifact["raw_excerpt"]))
        self.assertNotIn("HELPER-TWO", "\n".join(artifact["raw_excerpt"]))

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

            apply_general_sample = sample_dir / "apply-model-apply.lisp"
            apply_general_sample.write_text("; excerpted sample\n", encoding="utf-8")

            tri_sq_sample = sample_dir / "2009-tri-sq.lisp"
            tri_sq_sample.write_text("; excerpted sample\n", encoding="utf-8")

            system_root = tmp / "acl2-books"
            die_hard_book = system_root / "projects" / "die-hard-bottle-game" / "work.lisp"
            die_hard_book.parent.mkdir(parents=True)
            die_hard_book.write_text("; canonical work book\n", encoding="utf-8")

            apply_dir = system_root / "projects" / "apply-model"
            apply_dir.mkdir(parents=True)
            portcullis = apply_dir / "portcullis.acl2"
            portcullis.write_text("; portcullis\n", encoding="utf-8")
            constraints = apply_dir / "apply-constraints.lisp"
            constraints.write_text("; apply constraints\n", encoding="utf-8")
            apply_book = apply_dir / "apply-prim.lisp"
            apply_book.write_text("; canonical apply-prim book\n", encoding="utf-8")
            general_apply_book = apply_dir / "apply.lisp"
            general_apply_book.write_text("; canonical apply book\n", encoding="utf-8")

            tri_sq_dir = system_root / "workshops" / "2009" / "cowles-gamboa-triangle-square" / "materials"
            tri_sq_dir.mkdir(parents=True)
            tri_sq_book = tri_sq_dir / "tri-sq.lisp"
            tri_sq_book.write_text("; canonical tri-sq book\n", encoding="utf-8")

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

            apply_general_plans = bridge.resolve_load_plans(str(apply_general_sample), system_root=system_root)
            self.assertTrue(
                any(
                    plan.book == apply_general_sample.resolve()
                    and plan.preludes == (portcullis, constraints)
                    for plan in apply_general_plans
                )
            )
            self.assertTrue(
                any(
                    plan.book == general_apply_book
                    and plan.preludes == (portcullis, constraints)
                    for plan in apply_general_plans
                )
            )

            tri_sq_plans = bridge.resolve_load_plans(str(tri_sq_sample), system_root=system_root)
            self.assertEqual(tri_sq_plans[0].book, tri_sq_sample.resolve())
            self.assertTrue(any(plan.book == tri_sq_book for plan in tri_sq_plans))


if __name__ == "__main__":
    unittest.main()
