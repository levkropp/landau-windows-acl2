"""Draft 02: a continuous story using the reference's actual scene methods.

The upstream files remain under ignored .tools/reference. The mirror and
ceiling animations below call S3Plan.mirror/ceiling without rewriting them.
Only narration, platform fonts, and surrounding project scenes are adapted.
"""
from __future__ import annotations

import json
import sys
from pathlib import Path

from manim import *

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT / ".tools/reference"))
import base as reference_base

# Original fonts are platform-specific. Supply installed Windows equivalents
# before importing the upstream scenes, keeping their animation geometry.
def readable_text(s, size=34, color=reference_base.INK, font="Segoe UI", weight=NORMAL, **kw):
    return Text(s, font=font, font_size=size, color=color, weight=weight,
                disable_ligatures=True, **kw)


def readable_markup(s, size=40, color=reference_base.INK, font="Cambria", **kw):
    return MarkupText(s, font=font, font_size=size, color=color, **kw)


reference_base.T = readable_text
reference_base.M = readable_markup
reference_base.mono = lambda s, size=28, color=reference_base.INK, **kw: readable_text(
    s, size=size, color=color, font="Consolas", **kw)
reference_base.SANS = "Segoe UI"
reference_base.SERIF = "Cambria"
reference_base.MONO = "Consolas"

from base import *
from parts import ZeroMap
from s3_plan import CeilingPlot, S3Plan

config.background_color = BG
config.frame_width = 14.2222222222
config.frame_height = 8


class LocalNarration:
    def __init__(self, scene, key, tail=0.65):
        self.scene = scene
        self.segment = scene.script[key]
        self.tail = tail

    def __enter__(self):
        self.start = self.scene.time
        self.t0 = self.start + 0.2
        self.scene.add_sound(str(ROOT / self.segment["audio"]), time_offset=0.2)
        self.scene.timings.append({"id": self.segment["id"], "chapter": self.segment["chapter"],
                                   "start": self.start, "audio_start": self.t0,
                                   "duration": self.segment["duration"], "sentences": self.segment["sentences"]})
        return self

    def at(self, cue, lead=0.0):
        index = self.segment.get("cues", {}).get(cue, cue if isinstance(cue, int) else 0)
        desired = self.t0 + self.segment["sentences"][index]["start"] - lead
        if desired > self.scene.time:
            self.scene.wait(desired - self.scene.time)
        elif self.scene.time - desired > 1.2:
            print(f"Cue late: {self.segment['id']}:{cue} by {self.scene.time-desired:.2f}s")

    def __exit__(self, exc_type, exc, tb):
        if exc_type is None:
            end = self.t0 + self.segment["duration"] + self.tail
            if self.scene.time < end:
                self.scene.wait(end - self.scene.time)
        return False


class LandauRepoStory(S3Plan):
    def construct(self):
        manifest = json.loads((ROOT / "audio/manifest-v2.json").read_text(encoding="utf8"))
        self.script = {segment["id"]: segment for segment in manifest["segments"]}
        self.timings = []
        self.corner_label = T("Landau Windows", size=20, color=DIM).to_corner(UL, buff=0.32)
        self.draft = T("REVIEW DRAFT 02", size=14, color=DIM).to_corner(UR, buff=0.35)
        self.add(self.corner_label, self.draft)
        self.news()
        self.toolkit()
        self.economy()
        self.change_label("The Landau bridge")
        self.chips = self.make_chips()
        # These are the original animation methods and assets, with local
        # narration supplied by the context manager above.
        S3Plan.mirror(self)
        S3Plan.ceiling(self)
        self.focus()
        self.windowed()
        self.acl2()
        self.goal()
        (ROOT / "media/timing-v2.json").write_text(json.dumps(self.timings, indent=2), encoding="utf8")

    def narrate(self, key, tail=0.65):
        return LocalNarration(self, key, tail)

    def wipe(self, *keep, run_time=0.6):
        # Preserve the unobtrusive review label while reusing upstream wipes.
        keep_set = {self.corner_label, self.draft, *keep}
        gone = [m for m in self.mobjects if m not in keep_set]
        if gone:
            self.play(*[FadeOut(m) for m in gone], run_time=run_time)

    def change_label(self, text):
        replacement = T(text, size=20, color=DIM).to_corner(UL, buff=0.32)
        self.play(Transform(self.corner_label, replacement), run_time=0.4)

    def news(self):
        zmap = ZeroMap(corner=[-5.5, -2.6, 0], x_len=4.3, y_len=5.1)
        central = Line(zmap.c2p(0.5, 0), zmap.c2p(0.5, 55), color=TRUTH, stroke_width=3)
        headline = lines("A proof of RH", "checked in Lean", size=44, color=INK).move_to([3.0, 0.8, 0])
        headline[1].set_color(GOOD)
        check = tick_mark(size=0.45).next_to(headline, DOWN, buff=0.35)
        question = lines("How much foundation", "does the proof need?", size=33, color=PRED).move_to([3.0, -1.65, 0])
        source = T("Independent verification: Rubinstein / Sutherland · November 2026", size=15, color=DIM).to_edge(DOWN, buff=0.3)
        with self.narrate("news") as n:
            self.play(FadeIn(zmap), Create(central), FadeIn(headline, shift=UP * 0.12), run_time=1.2)
            n.at(1)
            self.play(Create(check), FadeIn(source), run_time=0.65)
            n.at(3)
            self.play(FadeIn(question, shift=UP * 0.15), run_time=0.8)
        self.wipe()

    def toolkit(self):
        self.change_label("How much foundation?")
        title = B("A powerful mathematical toolkit", size=44).move_to(UP * 2.35)
        blocks = VGroup()
        for y, label, color, width in [(-1.9, "ZFC · ordinary set theory", PRED, 10.9),
                                       (-0.65, "Inaccessible cardinals · larger universes", HYPO, 9.1),
                                       (0.6, "A usual mathematical model of Lean", INK, 7.3)]:
            box = card(width, 0.95, stroke=color).move_to([0, y, 0])
            word = T(label, size=26, color=color).move_to(box)
            blocks.add(VGroup(box, word))
        note = T("A model of the system ≠ assumptions needed by each theorem", size=22, color=DIM).move_to([0, -3.05, 0])
        with self.narrate("toolkit") as n:
            self.play(Write(title), run_time=1)
            n.at(1)
            self.play(LaggedStart(*[FadeIn(b, shift=UP * 0.12) for b in blocks], lag_ratio=0.3), run_time=1.3)
            n.at(3)
            self.play(FadeIn(note), run_time=0.5)
            n.at(4)
            arithmetic = B("RH can be stated using whole numbers", size=36, color=TRUTH).move_to([0, 0.1, 0])
            ingredients = T("Numbers · finite calculations · elementary inequalities", size=25, color=DIM).move_to([0, -0.85, 0])
            self.play(FadeOut(blocks), FadeOut(note), FadeIn(arithmetic), FadeIn(ingredients), run_time=0.8)
            n.at(6)
            question = T("Can the proof be reduced to arithmetic?", size=29, color=PRED).move_to([0, -2.0, 0])
            self.play(FadeIn(question), run_time=0.6)
        self.wipe()

    def economy(self):
        title = B("The same result, fewer assumptions", size=43).move_to(UP * 2.25)
        theorem = B("One theorem", size=38, color=TRUTH).move_to([0, 0.7, 0])
        large = card(5.2, 1.35, stroke=HYPO).move_to([-3.1, -1.05, 0])
        small = card(5.2, 1.35, stroke=PRED).move_to([3.1, -1.05, 0])
        zfc = B("ZFC", size=34, color=HYPO).move_to(large)
        pa = B("Peano arithmetic", size=31, color=PRED).move_to(small)
        arrow = Arrow([-0.45, -1.05, 0], [0.45, -1.05, 0], color=INK, buff=0,
                      max_tip_length_to_length_ratio=0.23)
        relation = T("can prove its consistency", size=22, color=DIM).move_to([0, -2.2, 0])
        conditions = T("PA cannot certify its own consistency · if consistent, under the standard hypotheses", size=17, color=DIM).move_to([0, -3.1, 0])
        with self.narrate("economy") as n:
            self.play(FadeIn(title), FadeIn(theorem), run_time=0.8)
            n.at(2)
            self.play(FadeIn(large), FadeIn(zfc), FadeIn(small), FadeIn(pa), run_time=0.8)
            n.at(3)
            self.play(GrowArrow(arrow), FadeIn(relation), run_time=0.7)
            n.at(4)
            self.play(FadeIn(conditions), run_time=0.6)
            n.at(5)
            self.play(theorem.animate.set_color(GOOD), Circumscribe(theorem, color=GOOD), run_time=0.9)
        self.wipe()

    def focus(self):
        headline = B("This is our part", size=48, color=PRED).move_to([0.3, 1.5, 0])
        bridge = lines("a ceiling on the prime-counting error", "↓", "no zeros in the forbidden region", size=32).move_to([0, -0.3, 0])
        bridge[0].set_color(GOOD)
        bridge[2].set_color(TRUTH)
        note = T("A classical bridge with a clear input and output", size=26, color=DIM).move_to([0, -2.55, 0])
        with self.narrate("focus") as n:
            self.play(*self.light(1), FadeIn(headline), FadeIn(bridge), run_time=0.9)
            n.at(1)
            self.play(FadeIn(note), run_time=0.6)
            n.at(3)
            self.play(self.chips[2].animate.set_opacity(0.2), run_time=0.6)
        self.wipe()

    def windowed(self):
        self.change_label("The windowed version")
        plot = CeilingPlot(center=[0, -0.6, 0], width=11.4, height=4.2)
        curve = plot.curve(plot.gap + plot.rogue, GAPC, 3.3)
        bound = plot.curve(plot.ceiling, GOOD, 4)
        left, right = plot.SPAN / 1.5, plot.SPAN
        band = Polygon(plot.p(left, -2), plot.p(right, -2), plot.p(right, 2), plot.p(left, 2),
                       stroke_width=0, fill_color=PRED, fill_opacity=0.09)
        lo = M("Y", size=26, color=PRED).next_to(plot.p(left, -2), DOWN, buff=0.14)
        hi = M("Y<sup>3/2</sup>", size=26, color=PRED).next_to(plot.p(right, -2), DOWN, buff=0.14)
        title = B("Only a window at a time", size=40).move_to([0, 2.25, 0])
        note = T("Schematic · the proof uses a smoothed prime-counting statistic", size=16, color=DIM).to_edge(DOWN, buff=0.25)
        point = Dot(plot.first_break(), radius=0.08, color=TRUTH)
        address = B("Find x* and certify the violation", size=36, color=TRUTH).move_to([0, 2.25, 0])
        with self.narrate("windowed") as n:
            self.play(FadeIn(title), FadeIn(band), Create(plot.axis), Create(plot.left),
                      Create(curve), Create(bound), FadeIn(lo), FadeIn(hi), FadeIn(note), run_time=1.5)
            n.at(1)
            self.play(Flash(plot.first_break(), color=TRUTH), FadeIn(point), run_time=0.7)
            n.at(2)
            mesh = VGroup(*[Dot(plot.p(u, 0), radius=0.028, color=PRED)
                           for u in np.linspace(left, right, 23)])
            self.play(LaggedStart(*[FadeIn(dot) for dot in mesh], lag_ratio=0.04), Transform(title, address), run_time=1.1)
        self.wipe()

    def acl2(self):
        self.change_label("Meet ACL2")
        name = B("ACL2", size=66, color=PRED).move_to([0, 1.95, 0])
        meaning = lines("A Computational Logic for", "Applicative Common Lisp", size=28).move_to([0, 0.6, 0])
        language = T("Common Lisp is the programming language", size=24, color=DIM).move_to([0, -0.7, 0])
        with self.narrate("acl2") as n:
            self.play(Write(name), run_time=0.8)
            n.at(1)
            self.play(FadeIn(meaning), run_time=0.7)
            n.at(2)
            self.play(FadeIn(language), run_time=0.6)
            n.at(4)
            objects = VGroup(T("[1, 2, 3, …, n]", size=33, color=PRED, font=MONO),
                             M("½ + ⅓ = ⅚", size=41, color=TRUTH),
                             T("solve n using n − 1", size=32, color=GOOD)).arrange(RIGHT, buff=0.8).move_to([0, 0.2, 0])
            if objects.width > 12:
                objects.scale_to_fit_width(12)
            self.play(FadeOut(meaning), FadeOut(language), FadeIn(objects), run_time=0.8)
            n.at(5)
            dominoes = VGroup(*[RoundedRectangle(width=0.34, height=1.0, corner_radius=0.06,
                                                 color=PRED, fill_color=PANEL, fill_opacity=1)
                               for _ in range(10)]).arrange(RIGHT, buff=0.3).move_to([0, -1.6, 0])
            self.play(FadeIn(dominoes), run_time=0.6)
            n.at(6)
            self.play(LaggedStart(*[Rotate(d, angle=-0.9, about_point=d.get_corner(DR))
                                    for d in dominoes], lag_ratio=0.17), run_time=1.8)
            n.at(7)
            self.play(FadeOut(objects), run_time=0.5)
            arithmetic = B("Arithmetic + recursion + induction", size=32, color=GOOD).move_to([0, 0.1, 0])
            self.play(FadeIn(arithmetic), run_time=0.6)
            n.at(8)
            target = T("Target: roughly PA strength, with a precise interpretation", size=24, color=DIM).move_to([0, -2.85, 0])
            self.play(FadeIn(target), run_time=0.6)
        self.wipe()

    def goal(self):
        self.change_label("Landau Windows")
        title = B("Reprove the Landau bridge in ACL2", size=43, color=PRED).move_to([0, 1.6, 0])
        row = VGroup(B("Compute", size=31, color=TRUTH), T("→", size=36),
                     B("Prove success", size=31, color=GOOD), T("→", size=36),
                     B("Connect to Landau", size=31, color=PRED)).arrange(RIGHT, buff=0.3).move_to([0, 0.1, 0])
        if row.width > 12.5:
            row.scale_to_fit_width(12.5)
        status = T("The full arithmetic reduction is in progress", size=25, color=DIM).move_to([0, -1.4, 0])
        ending = B("Same result. Fewer assumptions.", size=41, color=TRUTH).move_to([0, -2.4, 0])
        credit = T("Animations adapted from Hart Traveller’s riemann · narration: tiny-voca M2", size=15, color=DIM).to_edge(DOWN, buff=0.28)
        with self.narrate("goal") as n:
            self.play(FadeIn(title), run_time=0.8)
            n.at(1)
            self.play(FadeIn(row), run_time=0.8)
            n.at(4)
            self.play(FadeIn(status), run_time=0.6)
            n.at(5)
            self.play(FadeIn(ending), FadeIn(credit), run_time=0.8)
