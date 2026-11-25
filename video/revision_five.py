"""Final overview: preserve the foundations and report the completed reduction."""
from revision_four import *


class LandauRevisionFive(LandauRevisionFour):
    manifest_file="manifest-v5.json"
    timing_file="timing-v5.json"
    review_label="COMPLETED REDUCTION · OVERVIEW 05"

    def lean_rh(self):
        with self.narrate("lean_rh") as n:
            title=self.heading("One essential step, with fewer assumptions")
            proof=lines("A proof of RH","checked in Lean",size=35).move_to([0,.9,0]);proof[1].set_color(GOOD)
            self.play(FadeIn(proof),run_time=.75)
            n.at(1);foundation=fitted(T("Usual universe models: ZFC + inaccessible cardinals",size=25,color=HYPO)).move_to([0,-.45,0]);self.play(FadeIn(foundation),run_time=.65)
            n.at(2);arithmetic=B("RH itself can be stated in arithmetic",size=35,color=TRUTH).move_to([0,-1.65,0]);self.play(FadeIn(arithmetic),run_time=.7)
            n.at(4);self.play(FadeOut(proof),FadeOut(foundation),FadeOut(arithmetic),run_time=.65)
            self.play(FadeIn(B("The windowed Landau ceiling bridge",size=39,color=PRED).move_to([0,.85,0])),run_time=.7)
            n.at(5);self.play(FadeIn(B("PROVED in Peano Arithmetic",size=34,color=GOOD).move_to([0,-.25,0])),run_time=.7)
            n.at(6);self.play(FadeIn(T("Direct arithmetic proof · certified ACL2 development",size=26,color=TRUTH).move_to([0,-1.65,0])),run_time=.7)
        self.wipe()

    def focus(self):
        with self.narrate("focus") as n:
            self.play(*self.light(1),FadeIn(B("The completed conversion",size=43,color=PRED).move_to([.3,1.5,0])),run_time=.9)
            bridge=lines("a ceiling on recurring windows","↓","exclude zeros in the forbidden region",size=31).move_to([0,-.3,0]);bridge[0].set_color(GOOD);bridge[2].set_color(TRUTH);self.play(FadeIn(bridge),run_time=.8)
            n.at(2);self.play(FadeIn(T("Proved in Peano Arithmetic · certified in ACL2",size=26,color=TRUTH).move_to([0,-2.55,0])),run_time=.7)
            n.at(3);self.play(self.chips[2].animate.set_opacity(.2),run_time=.6)
        self.wipe()

    def acl2(self):
        with self.narrate("acl2") as n:
            title=self.heading("ACL2: exact computation and induction")
            self.play(FadeIn(B("A Computational Logic for Applicative Common Lisp",size=32,color=PRED).move_to([0,1,0])),run_time=.8)
            n.at(3);self.play(FadeIn(lines("finite lists · exact fractions","recursive functions · induction",size=32,color=INK).move_to([0,-.25,0])),run_time=.8)
            n.at(4);self.play(FadeIn(B("Certified in vanilla ACL2",size=32,color=GOOD).move_to([0,-1.65,0])),run_time=.75)
            n.at(6);self.play(FadeIn(fitted(T("Direct Peano Arithmetic proof: classical/pa-paper.pdf, Theorem 15.2",size=23,color=TRUTH)).move_to([0,-2.85,0])),run_time=.7)
        self.wipe()

    def goal(self):
        with self.narrate("goal",tail=1) as n:
            name=fitted(B("landau-windows-acl2",size=46,color=PRED)).move_to([0,2.1,0]);self.play(FadeIn(name),run_time=.8)
            row=VGroup(B("Compute",size=29,color=TRUTH),T("→",size=33),B("Prove success",size=29,color=GOOD),T("→",size=33),B("Interpret Landau",size=29,color=PRED)).arrange(RIGHT,buff=.35);fitted(row).move_to([0,.6,0]);self.play(FadeIn(row),run_time=.8)
            n.at(2);status=T("PROVED in Peano Arithmetic",size=31,color=GOOD).move_to([0,-.75,0]);self.play(FadeIn(status),run_time=.75)
            n.at(3);wider=lines("Landau is one completed step.","Other reductions remain possible.",size=28).move_to([0,-1.85,0]);self.play(FadeIn(wider),run_time=.8)
            n.at(5);self.play(Transform(wider,lines("A full RH proof in arithmetic?","This project does not settle that question.",size=27,color=PRED).move_to(wider)),run_time=.7)
            n.at(7);self.play(FadeOut(row),FadeOut(status),FadeOut(wider),run_time=.6)
            self.play(FadeIn(B("Same result. Fewer assumptions.",size=40,color=TRUTH).move_to([0,-.35,0])),run_time=.8)
            credit=fitted(T("Peano Arithmetic proof: classical/pa-paper.pdf · ACL2: lw-euler-window-encoded-zero-reduction",size=15,color=DIM)).to_edge(DOWN,buff=.55)
            self.play(FadeIn(credit),FadeIn(fitted(T("Original Landau animations: Hart Traveller’s riemann · narration: tiny-voca M2",size=14,color=DIM)).to_edge(DOWN,buff=.2)),run_time=.65)
