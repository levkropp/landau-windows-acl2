"""Original Manim follow-up to harttraveller/riemann's step-two explanation.

The palette recalls the reference; layouts, animation and narration are new.
No footage or original voice recording is embedded. All curves are schematic.
"""
from __future__ import annotations

import json
import math
from pathlib import Path

import numpy as np
from manim import *

ROOT = Path(__file__).resolve().parent
BG = "#0D0F14"
PANEL = "#161A22"
INK = "#EDEFF3"
DIM = "#8A8F98"
FAINT = "#343B49"
BLUE = "#58C4DD"
YELLOW = "#F2D24B"
CORAL = "#FF7A6B"
GREEN = "#7BD88F"
PURPLE = "#B592F0"
FONT = "Segoe UI"
config.background_color = BG
config.frame_width = 14.2222222222
config.frame_height = 8


def txt(words, size=30, color=INK, weight=NORMAL, **kwargs):
    return Text(words, font=FONT, font_size=size, color=color, weight=weight,
                disable_ligatures=True, **kwargs)


def mathtext(words, size=36, color=INK):
    return MarkupText(words, font="Cambria", font_size=size, color=color)


def card(width, height, color=FAINT, fill=PANEL):
    return RoundedRectangle(width=width, height=height, corner_radius=0.14,
                            stroke_color=color, stroke_width=1.4,
                            fill_color=fill, fill_opacity=1)


def stack(*lines, size=28, color=INK, buff=0.18):
    return VGroup(*[txt(line, size, color) for line in lines]).arrange(DOWN, buff=buff)


class LandauFollowup(Scene):
    def construct(self):
        self.manifest = json.loads((ROOT / "audio/manifest.json").read_text(encoding="utf8"))
        self.timings = []
        self.active = VGroup()
        self.header = txt("LANDAU WINDOWS", 16, DIM).to_corner(UL, buff=0.38)
        self.draft = txt("REVIEW DRAFT 01  /  PROOF IN PROGRESS", 14, DIM).to_corner(UR, buff=0.4)
        self.rule = Line([-6.7, 3.35, 0], [6.7, 3.35, 0], color=FAINT, stroke_width=1)
        self.progress = Rectangle(width=0.01, height=0.025, stroke_width=0, fill_color=BLUE,
                                  fill_opacity=1).move_to([-6.7, -3.87, 0], aligned_edge=LEFT)
        self.add(self.header, self.draft, self.rule, self.progress)
        methods = [self.opening, self.scope, self.windows, self.foundations,
                   self.rh, self.consistency, self.progress_scene, self.destination]
        for index, (segment, method) in enumerate(zip(self.manifest["segments"], methods)):
            self.chapter_index = index
            self.segment = segment
            self.start = self.time
            self.add_sound(str(ROOT / segment["audio"]), time_offset=0.55, gain=-1)
            self.timings.append({"id": segment["id"], "chapter": segment["chapter"],
                                 "start": self.start, "audio_start": self.start + 0.55,
                                 "duration": segment["duration"], "sentences": segment["sentences"]})
            method()
            self.hold_to_end()
            if index < len(methods) - 1:
                self.play(FadeOut(self.active), run_time=0.45)
                self.active = VGroup()
        (ROOT / "media").mkdir(exist_ok=True)
        (ROOT / "media/timing.json").write_text(json.dumps(self.timings, indent=2), encoding="utf8")

    def keep(self, *objects):
        self.active.add(*objects)

    def at_sentence(self, index):
        desired = self.start + 0.55 + self.segment["sentences"][index]["start"]
        if self.time < desired:
            self.wait(desired - self.time)

    def hold_to_end(self):
        target = self.start + 0.55 + self.segment["duration"] + 1.0
        if self.time < target:
            self.wait(target - self.time)
        width = 13.4 * (self.chapter_index + 1) / len(self.manifest["segments"])
        self.play(self.progress.animate.stretch_to_fit_width(width).move_to(
            [-6.7, -3.87, 0], aligned_edge=LEFT), run_time=0.25)

    def heading(self, title, kicker):
        label = txt(kicker.upper(), 16, BLUE).move_to([0, 2.79, 0])
        title_mob = txt(title, 39, INK, SEMIBOLD).move_to([0, 2.13, 0])
        if title_mob.width > 12.8:
            title_mob.scale_to_fit_width(12.8)
        self.play(FadeIn(label), FadeIn(title_mob, shift=UP * 0.12), run_time=0.65)
        self.keep(label, title_mob)

    def opening(self):
        credit = txt("Following Hart Traveller’s explanation of step two", 20, DIM).move_to([0, 2.05, 0])
        quote = txt("“A ceiling alone is enough.”", 49, YELLOW, SEMIBOLD).move_to([0, 0.65, 0])
        underline = Line([-4.5, -0.05, 0], [4.5, -0.05, 0], color=YELLOW, stroke_width=2)
        self.play(FadeIn(credit), Write(quote), Create(underline), run_time=1.5)
        self.keep(credit, quote, underline)
        self.at_sentence(1)
        bridge = txt("One classical bridge. A smaller foundation?", 29, BLUE).move_to([0, -1.15, 0])
        self.play(FadeIn(bridge, shift=UP * 0.18), run_time=0.65)
        self.keep(bridge)
        self.at_sentence(2)
        title = txt("LANDAU WINDOWS", 23, INK, SEMIBOLD).move_to([0, -2.28, 0])
        self.play(FadeIn(title), run_time=0.6)
        self.keep(title)

    def scope(self):
        self.heading("Extract the middle step", "Our scope")
        cards = VGroup()
        for i, (name, detail, color) in enumerate([
            ("Reflect", "the zeros", DIM),
            ("Convert", "ceiling → zero-freeness", BLUE),
            ("Construct", "the ceiling", DIM),
        ]):
            x = -4.5 + 4.5 * i
            box = card(4.0, 2.25, color if i == 1 else FAINT).move_to([x, 0, 0])
            number = txt(f"0{i + 1}", 20, color).move_to([x, 0.72, 0])
            name_mob = txt(name, 34, color, SEMIBOLD).move_to([x, 0.12, 0])
            sub = txt(detail, 19, color).move_to([x, -0.52, 0])
            cards.add(VGroup(box, number, name_mob, sub))
        arrows = VGroup(*[Arrow([x, 0, 0], [x + 0.4, 0, 0], color=FAINT, buff=0,
                                max_tip_length_to_length_ratio=0.3) for x in (-2.45, 2.05)])
        self.play(LaggedStart(*[FadeIn(c, shift=UP * 0.15) for c in cards], lag_ratio=0.3),
                  FadeIn(arrows), run_time=1.2)
        self.keep(cards, arrows)
        self.at_sentence(4)
        focus = SurroundingRectangle(cards[1], color=BLUE, buff=0.10, corner_radius=0.14)
        self.play(Create(focus), cards[0].animate.set_opacity(0.4),
                  cards[2].animate.set_opacity(0.4), run_time=0.7)
        self.keep(focus)
        self.at_sentence(5)
        note = txt("A theorem inside the architecture", 26, INK).move_to([0, -2.0, 0])
        self.play(FadeIn(note), run_time=0.7)
        self.keep(note)

    def windows(self):
        self.heading("A witness needs an address", "The effective target")
        axes = Axes(x_range=[0, 10, 2], y_range=[-2.6, 3, 1], x_length=10.9,
                    y_length=3.5, tips=False, axis_config={"color": FAINT, "stroke_width": 1.5})
        axes.move_to([0, -0.1, 0])
        ceiling = lambda x: 0.72 + 0.08 * x
        signal = lambda x: 0.30 * math.exp(0.22 * x) * math.sin(1.75 * x - 0.7)
        ccurve = axes.plot(ceiling, x_range=[0, 10], color=BLUE, stroke_width=3)
        curve = axes.plot(signal, x_range=[0, 10, 0.025], color=CORAL, stroke_width=3)
        band = Polygon(axes.c2p(4.6, -2.6), axes.c2p(8.5, -2.6),
                       axes.c2p(8.5, 3), axes.c2p(4.6, 3), stroke_width=0,
                       fill_color=BLUE, fill_opacity=0.09)
        ymark = mathtext("Y", 26, BLUE).next_to(axes.c2p(4.6, -2.6), DOWN, buff=0.13)
        topmark = mathtext("Y<sup>3/2</sup>", 26, BLUE).next_to(axes.c2p(8.5, -2.6), DOWN, buff=0.13)
        clabel = mathtext("C x<sup>θ</sup>", 25, BLUE).next_to(axes.c2p(9.4, ceiling(9.4)), UP, buff=0.13)
        glabel = mathtext("G(x)", 25, CORAL).next_to(axes.c2p(2.0, signal(2.0)), DOWN, buff=0.3)
        disclaimer = txt("Schematic signal and window · not numerical zeta data", 15, DIM).move_to([0, -3.26, 0])
        self.play(FadeIn(band), Create(axes), Create(ccurve), Create(curve),
                  FadeIn(ymark), FadeIn(topmark), FadeIn(clabel), FadeIn(glabel), FadeIn(disclaimer), run_time=1.7)
        self.keep(axes, band, ccurve, curve, ymark, topmark, clabel, glabel, disclaimer)
        self.at_sentence(2)
        mesh = VGroup(*[Dot(axes.c2p(x, signal(x)), radius=0.025, color=DIM)
                       for x in np.linspace(4.6, 8.5, 31)])
        self.play(LaggedStart(*[FadeIn(dot) for dot in mesh], lag_ratio=0.025), run_time=0.9)
        self.keep(mesh)
        self.at_sentence(3)
        # The illustrated signal crosses its illustrated ceiling within this window.
        choices = np.linspace(4.6, 8.5, 301)
        witness = max(choices, key=lambda x: signal(x) - ceiling(x))
        point = Dot(axes.c2p(witness, signal(witness)), radius=0.075, color=YELLOW)
        enclosure = Line(axes.c2p(witness, signal(witness) - 0.10),
                         axes.c2p(witness, signal(witness) + 0.10), color=YELLOW, stroke_width=4)
        label = txt("computed x* + certified interval", 22, YELLOW).move_to([1.4, 1.37, 0])
        self.play(FadeIn(point), Create(enclosure), FadeIn(label), run_time=0.8)
        self.keep(point, enclosure, label)

    def foundations(self):
        self.heading("The ambient system can be stronger", "Foundational extraction")
        left_box = card(5.8, 2.55, PURPLE).move_to([-3.35, -0.1, 0])
        right_box = card(5.8, 2.55, BLUE).move_to([3.35, -0.1, 0])
        left_text = VGroup(txt("Lean correctness layer", 29, PURPLE, SEMIBOLD),
                          txt("Universes + classical analysis", 23, INK),
                          txt("Usual models: inaccessible cardinals", 18, DIM)).arrange(DOWN, buff=0.32).move_to(left_box)
        right_text = VGroup(txt("ACL2 arithmetic target", 29, BLUE, SEMIBOLD),
                           txt("Rationals + finite data + induction", 21, INK),
                           txt("Roughly PA strength · interpretation required", 17, DIM)).arrange(DOWN, buff=0.32).move_to(right_box)
        arrow = Arrow([-0.4, -0.1, 0], [0.4, -0.1, 0], buff=0, color=INK,
                      max_tip_length_to_length_ratio=0.2)
        self.play(FadeIn(left_box), FadeIn(left_text), run_time=0.8)
        self.keep(left_box, left_text)
        self.at_sentence(2)
        note = txt("A proof’s setting does not determine the theorem’s needs.", 25, YELLOW).move_to([0, -2.15, 0])
        self.play(FadeIn(note), run_time=0.7)
        self.keep(note)
        self.at_sentence(3)
        self.play(FadeIn(right_box), FadeIn(right_text), GrowArrow(arrow), run_time=0.9)
        self.keep(right_box, right_text, arrow)

    def rh(self):
        self.heading("A formulation is a starting point", "RH and arithmetic")
        upper = card(10.8, 1.45, GREEN).move_to([0, 0.7, 0])
        upper_text = stack("RH has elementary arithmetic formulations", "Lagarias’s criterion is one example", size=28, buff=0.19).move_to(upper)
        upper_text[0].set_color(GREEN)
        self.play(FadeIn(upper), FadeIn(upper_text), run_time=0.8)
        self.keep(upper, upper_text)
        self.at_sentence(2)
        lower = card(10.8, 1.45, YELLOW).move_to([0, -1.25, 0])
        lower_text = stack("A PA proof still has to be constructed", "The equivalence and the proof both need justification", size=27, buff=0.2).move_to(lower)
        lower_text[0].set_color(YELLOW)
        self.play(FadeIn(lower), FadeIn(lower_text), run_time=0.8)
        self.keep(lower, lower_text)
        source = txt("Source: J. C. Lagarias, An Elementary Problem Equivalent to RH (2002)", 15, DIM).move_to([0, -3.0, 0])
        self.play(FadeIn(source), run_time=0.45)
        self.keep(source)

    def consistency(self):
        self.heading("The same conclusion, fewer assumptions", "Why this is valuable")
        left = card(5.7, 2.6, YELLOW).move_to([-3.25, -0.05, 0])
        right = card(5.7, 2.6, PURPLE).move_to([3.25, -0.05, 0])
        left_title = txt("Inside PA", 25, DIM).move_to([-3.25, 0.72, 0])
        left_formula = mathtext("PA ⊬ Con(PA)", 40, YELLOW).move_to([-3.25, 0.03, 0])
        left_note = txt("if PA is consistent", 21, DIM).move_to([-3.25, -0.74, 0])
        right_title = txt("From a stronger theory", 25, DIM).move_to([3.25, 0.72, 0])
        right_formula = mathtext("ZFC ⊢ Con(PA)", 40, PURPLE).move_to([3.25, 0.03, 0])
        right_note = txt("a relative consistency argument", 20, DIM).move_to([3.25, -0.74, 0])
        self.play(FadeIn(left), FadeIn(left_title), FadeIn(left_formula), FadeIn(left_note), run_time=0.85)
        self.keep(left, left_title, left_formula, left_note)
        qualifier = txt("Gödel II: usual effectiveness, arithmetic and derivability hypotheses", 17, DIM).move_to([0, -2.9, 0])
        self.play(FadeIn(qualifier), run_time=0.5)
        self.keep(qualifier)
        self.at_sentence(2)
        self.play(FadeIn(right), FadeIn(right_title), FadeIn(right_formula), FadeIn(right_note), run_time=0.85)
        self.keep(right, right_title, right_formula, right_note)
        self.at_sentence(4)
        takeaway = txt("Fewer foundational commitments for the theorem", 27, BLUE).move_to([0, -2.02, 0])
        self.play(FadeIn(takeaway), run_time=0.7)
        self.keep(takeaway)

    def progress_scene(self):
        self.heading("Progress toward the full reduction", "Current proof status")
        established = card(6.0, 3.25, GREEN).move_to([-3.3, -0.45, 0])
        remaining = card(6.0, 3.25, YELLOW).move_to([3.3, -0.45, 0])
        established_title = txt("ESTABLISHED", 18, GREEN, SEMIBOLD).move_to([-3.3, 0.68, 0])
        remaining_title = txt("STILL TO PROVE", 18, YELLOW, SEMIBOLD).move_to([3.3, 0.68, 0])
        checked = stack("Lean: classical Landau theorem", "ACL2: exact evaluators + search",
                        "Explicit thresholds + transport", size=24, buff=0.35).move_to([-3.3, -0.5, 0])
        pending = stack("Analytic coefficient estimates", "General zero covers",
                        "Full composition + interpretation", size=24, buff=0.35).move_to([3.3, -0.5, 0])
        self.play(FadeIn(established), FadeIn(established_title), FadeIn(checked), run_time=0.9)
        self.keep(established, established_title, checked)
        self.at_sentence(2)
        self.play(FadeIn(remaining), FadeIn(remaining_title), FadeIn(pending), run_time=0.9)
        self.keep(remaining, remaining_title, pending)
        self.at_sentence(3)
        status = txt("Full ACL2 Landau theorem: work in progress", 25, YELLOW).move_to([0, -2.85, 0])
        self.play(FadeIn(status), run_time=0.7)
        self.keep(status)

    def destination(self):
        self.heading("Same theorem. Fewer assumptions.", "The destination")
        row = VGroup()
        for x, title, detail in [(-4.5, "Compute", "explicit witness"),
                                  (0, "Prove", "general success"),
                                  (4.5, "Interpret", "Landau’s theorem")]:
            box = card(3.95, 1.85, BLUE).move_to([x, 0.1, 0])
            name = txt(title, 32, BLUE, SEMIBOLD).move_to([x, 0.4, 0])
            sub = txt(detail, 23, INK).move_to([x, -0.23, 0])
            row.add(VGroup(box, name, sub))
        self.play(LaggedStart(*[FadeIn(item, shift=UP * 0.15) for item in row], lag_ratio=0.3), run_time=1.3)
        self.keep(row)
        self.at_sentence(3)
        final = txt("One theorem at a time.", 35, YELLOW, SEMIBOLD).move_to([0, -1.8, 0])
        self.play(FadeIn(final), run_time=0.7)
        self.keep(final)
        credit = stack("Reference: harttraveller/riemann · Step two: the ceiling",
                       "Original follow-up · Manim Community · tiny-voca M2",
                       "Review draft 01 · Full ACL2 proof remains in progress", size=16, color=DIM, buff=0.12).move_to([0, -2.95, 0])
        self.play(FadeIn(credit), run_time=0.6)
        self.keep(credit)
