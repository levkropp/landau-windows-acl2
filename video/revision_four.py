"""Preserve draft 03's foundations; revise its transition and conclusion."""
from __future__ import annotations

from foundations_story import *


class LandauRevisionFour(LandauFoundationsStory):
    manifest_file = "manifest-v4.json"
    timing_file = "timing-v4.json"
    review_label = "REVIEW DRAFT 04"

    def lean_rh(self):
        with self.narrate("lean_rh") as n:
            title = self.heading("One essential step, with fewer assumptions")
            proof = lines("A proof of RH", "checked in Lean", size=35).move_to([0, 0.9, 0])
            proof[1].set_color(GOOD)
            foundation = T("Usual universe models: ZFC + inaccessible cardinals", size=25, color=HYPO).move_to([0, -0.45, 0])
            self.play(FadeIn(proof), run_time=0.75)
            n.at(1)
            self.play(FadeIn(foundation), run_time=0.65)
            n.at(2)
            arithmetic = B("RH itself can be stated in arithmetic", size=35, color=TRUTH).move_to([0, -1.65, 0])
            self.play(FadeIn(arithmetic), run_time=0.7)
            n.at(4)
            self.play(FadeOut(proof), FadeOut(foundation), FadeOut(arithmetic), run_time=0.65)
            bridge = B("The classical Landau bridge", size=40, color=PRED).move_to([0, 0.85, 0])
            target = T("Target: prove this conversion in Peano arithmetic", size=28, color=INK).move_to([0, -0.2, 0])
            self.play(FadeIn(bridge), run_time=0.7)
            n.at(5)
            self.play(FadeIn(target), run_time=0.7)
            n.at(6)
            value = B("This step would depend on fewer assumptions", size=30, color=TRUTH).move_to([0, -1.65, 0])
            self.play(FadeIn(value), run_time=0.7)
        self.wipe()

    def focus(self):
        with self.narrate("focus") as n:
            headline = B("This is our part", size=48, color=PRED).move_to([0.3, 1.5, 0])
            bridge = lines("a ceiling on the prime-counting error", "↓", "no zeros in the forbidden region", size=32).move_to([0, -0.3, 0])
            bridge[0].set_color(GOOD)
            bridge[2].set_color(TRUTH)
            note = T("The same conversion, justified in arithmetic", size=27, color=TRUTH).move_to([0, -2.55, 0])
            self.play(*self.light(1), FadeIn(headline), FadeIn(bridge), run_time=0.9)
            n.at(2)
            self.play(FadeIn(note), run_time=0.7)
            n.at(3)
            self.play(self.chips[2].animate.set_opacity(0.2), run_time=0.6)
        self.wipe()

    def goal(self):
        with self.narrate("goal", tail=1.0) as n:
            name = fitted(B("landau-windows-acl2", size=46, color=PRED)).move_to([0, 2.1, 0])
            row = VGroup(B("Compute", size=30, color=TRUTH), T("→", size=33),
                         B("Prove success", size=30, color=GOOD), T("→", size=33),
                         B("Interpret Landau", size=30, color=PRED)).arrange(RIGHT, buff=0.35)
            fitted(row).move_to([0, 0.6, 0])
            self.play(FadeIn(name), FadeIn(row), run_time=0.9)
            n.at(2)
            status = T("The full arithmetic reduction is in progress", size=26, color=DIM).move_to([0, -0.75, 0])
            self.play(FadeIn(status), run_time=0.65)
            n.at(3)
            wider = lines("Landau is our starting point.", "Other steps may also be reducible.", size=29, color=INK).move_to([0, -1.85, 0])
            self.play(FadeIn(wider), run_time=0.8)
            n.at(5)
            question = lines("Could the whole RH argument be carried out in PA?", "This project does not settle that question.", size=26, color=PRED).move_to([0, -1.85, 0])
            self.play(Transform(wider, question), run_time=0.7)
            n.at(7)
            self.play(FadeOut(row), FadeOut(status), FadeOut(wider), run_time=0.6)
            ending = B("Same result. Fewer assumptions.", size=40, color=TRUTH).move_to([0, -0.35, 0])
            credit = fitted(T("Original Landau animations: Hart Traveller’s riemann · narration: tiny-voca M2",
                              size=14, color=DIM)).to_edge(DOWN, buff=0.25)
            self.play(FadeIn(ending), FadeIn(credit), run_time=0.8)
