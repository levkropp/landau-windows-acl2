"""Draft 03: teach the foundations before extracting the Landau bridge.

The persistent repository name is separate from chapter headings. Original
mirror/ceiling methods and assets are loaded by repo_story's pinned adapter.
"""
from __future__ import annotations

from repo_story import *


def fitted(mobject, width=12.3):
    if mobject.width > width:
        mobject.scale_to_fit_width(width)
    return mobject


def rulebook(name, color=PRED, width=2.5, height=2.25):
    box = card(width, height, stroke=color)
    title = B(name, size=31, color=color).move_to(box.get_top() + DOWN * 0.45)
    rules = VGroup(*[Line(LEFT * (width / 2 - 0.35), RIGHT * (width / 2 - 0.35),
                         color=FAINT, stroke_width=2.5) for _ in range(4)])
    rules.arrange(DOWN, buff=0.18).move_to(DOWN * 0.2)
    return VGroup(box, title, rules)


def number_model():
    frame = card(10.5, 2.8, stroke=PRED)
    title = B("The whole numbers, built as sets", size=28, color=PRED).move_to(UP * 0.86)
    entries = VGroup(M("0 = ∅", size=34), M("1 = {0}", size=34),
                     M("2 = {0, 1}", size=34), M("…", size=34))
    entries.arrange(RIGHT, buff=0.65).move_to(DOWN * 0.1)
    operations = T("next number · addition · multiplication", size=22, color=DIM).move_to(DOWN * 0.95)
    return VGroup(frame, title, entries, operations)


class LandauFoundationsStory(LandauRepoStory):
    manifest_file = "manifest-v3.json"
    timing_file = "timing-v3.json"
    review_label = "REVIEW DRAFT 03"

    def construct(self):
        manifest = json.loads((ROOT / "audio" / self.manifest_file).read_text(encoding="utf8"))
        self.script = {segment["id"]: segment for segment in manifest["segments"]}
        self.timings = []
        self.corner_label = T("landau-windows-acl2", size=16, color=DIM).to_corner(UL, buff=0.2)
        self.draft = T(self.review_label, size=13, color=DIM).to_corner(UR, buff=0.2)
        self.add(self.corner_label, self.draft)
        self.news()
        self.pa()
        self.zfc()
        self.godel()
        self.model_pa()
        self.inaccessible()
        self.lean_rh()
        self.chips = self.make_chips().shift(DOWN * 0.26)
        S3Plan.mirror(self)
        S3Plan.ceiling(self)
        self.focus()
        self.windowed()
        self.acl2()
        self.goal()
        self.wait(2.0)
        (ROOT / "media" / self.timing_file).write_text(json.dumps(self.timings, indent=2), encoding="utf8")

    def narrate(self, key, tail=0.85):
        return LocalNarration(self, key, tail)

    def change_label(self, text):
        # The repository name stays fixed; individual scenes supply headings.
        self.current_chapter = text

    def heading(self, text, color=INK):
        title = fitted(B(text, size=42, color=color)).move_to([0, 2.5, 0])
        self.play(FadeIn(title, shift=UP * 0.12), run_time=0.7)
        return title

    def news(self):
        zmap = ZeroMap(corner=[-5.5, -2.6, 0], x_len=4.3, y_len=5.1)
        central = Line(zmap.c2p(0.5, 0), zmap.c2p(0.5, 55), color=TRUTH, stroke_width=3)
        headline = lines("A proof of RH", "checked in Lean", size=44).move_to([3.0, 0.9, 0])
        headline[1].set_color(GOOD)
        check = tick_mark(size=0.45).move_to([3, -0.3, 0])
        question = lines("How much foundation", "does this argument need?", size=31, color=PRED).move_to([3, -1.7, 0])
        credit = fitted(T("Alpöge / Claude · independent checks: Rubinstein / Sutherland · November 2026",
                          size=14, color=DIM)).to_edge(DOWN, buff=0.25)
        with self.narrate("news") as n:
            self.play(FadeIn(zmap), Create(central), FadeIn(headline), run_time=1.3)
            n.at(1)
            self.play(Create(check), FadeIn(credit), run_time=0.65)
            n.at(4)
            self.play(FadeIn(question), run_time=0.8)
        self.wipe()

    def pa(self):
        with self.narrate("pa") as n:
            title = self.heading("Peano arithmetic: rules about whole numbers")
            numbers = VGroup(*[B(s, size=43, color=PRED) for s in ("0", "1", "2", "3", "4", "…")])
            numbers.arrange(RIGHT, buff=0.7).move_to([0, 1.1, 0])
            self.play(LaggedStart(*[FadeIn(x) for x in numbers], lag_ratio=0.18), run_time=1.0)
            n.at(3)
            arithmetic = VGroup(M("2 + 3 = 5", size=40, color=TRUTH),
                                M("2 × 3 = 6", size=40, color=TRUTH)).arrange(RIGHT, buff=1.2)
            arithmetic.move_to([0, -0.1, 0])
            self.play(FadeIn(arithmetic), run_time=0.7)
            n.at(4)
            induction = B("Induction", size=32, color=GOOD).move_to([0, -0.1, 0])
            self.play(FadeOut(arithmetic), FadeIn(induction), run_time=0.65)
            n.at(5)
            dominoes = VGroup(*[RoundedRectangle(width=0.34, height=0.95, corner_radius=0.05,
                                                 stroke_color=PRED, fill_color=PANEL, fill_opacity=1)
                               for _ in range(11)])
            dominoes.arrange(RIGHT, buff=0.3).move_to([0, -1.45, 0])
            self.play(FadeIn(dominoes), run_time=0.65)
            n.at(6)
            first = T("first case", size=23, color=GOOD).next_to(dominoes[0], DOWN, buff=0.3)
            step = T("each case gives the next", size=24, color=GOOD).move_to([0.7, -2.5, 0])
            self.play(dominoes[0].animate.set_color(GOOD), FadeIn(first), run_time=0.55)
            self.play(FadeIn(step), run_time=0.45)
            n.at(7)
            self.play(LaggedStart(*[Rotate(d, angle=-0.9, about_point=d.get_corner(DR)) for d in dominoes],
                                 lag_ratio=0.16), run_time=2.0)
            all_numbers = T("A finite proof about every whole number", size=26, color=TRUTH).move_to([0, -3.1, 0])
            self.play(FadeIn(all_numbers), run_time=0.6)
            n.at(9)
            data = fitted(T("finite lists · fractions · calculations", size=30, color=PRED)).move_to(numbers)
            self.play(Transform(numbers, data), run_time=0.7)
        self.wipe()

    def zfc(self):
        with self.narrate("zfc") as n:
            title = self.heading("ZFC: rules for sets")
            circle = Circle(radius=1.05, stroke_color=HYPO, fill_color=PANEL, fill_opacity=1)
            dots = VGroup(*[Dot(p, color=c, radius=0.09) for p, c in
                           (([-0.4, 0.2, 0], TRUTH), ([0.35, 0.3, 0], PRED), ([0, -0.4, 0], GOOD))])
            collection = VGroup(circle, dots).move_to([0, -0.1, 0])
            label = T("a collection of objects", size=26, color=DIM).move_to([0, -1.75, 0])
            n.at(2)
            self.play(Create(circle), FadeIn(dots), FadeIn(label), run_time=0.9)
            n.at(3)
            bigger = Circle(radius=1.75, stroke_color=PRED).move_to(collection)
            extra = Circle(radius=0.4, stroke_color=GOOD).move_to([1.1, -0.8, 0])
            self.play(Create(bigger), Create(extra), label.animate.shift(DOWN * 0.6), run_time=0.9)
            n.at(4)
            model = number_model().move_to([0, -0.15, 0])
            self.play(FadeOut(collection), FadeOut(bigger), FadeOut(extra), FadeOut(label), FadeIn(model), run_time=0.8)
            n.at(6)
            more = lines("functions", "real numbers", "spaces", size=28, color=HYPO).move_to([3.8, 0, 0])
            self.play(model.animate.scale(0.64).move_to([-2.2, 0, 0]), FadeIn(more), run_time=0.8)
            n.at(7)
            summary = T("A larger framework can justify more", size=28, color=TRUTH).move_to([0, -2.4, 0])
            self.play(FadeIn(summary), run_time=0.7)
        self.wipe()

    def godel(self):
        with self.narrate("godel") as n:
            title = self.heading("Can the rules certify themselves?")
            book = rulebook("PA").move_to([-4.4, -0.1, 0])
            proof_box = card(2.5, 2.2).move_to([0, -0.1, 0])
            proof_lines = lines("0 + 1 = 1", "1 + 1 = 2", "…", size=26).move_to(proof_box)
            proof = VGroup(proof_box, proof_lines)
            check = tick_mark(size=0.55).move_to([4.1, -0.1, 0])
            n.at(1)
            consistency = T("Consistency: no proof of a contradiction", size=28, color=TRUTH).move_to([0, 1.3, 0])
            self.play(FadeIn(consistency), FadeIn(book), run_time=0.8)
            n.at(3)
            self.play(FadeIn(proof), GrowArrow(Arrow(book.get_right(), proof.get_left(), buff=0.25, color=DIM)),
                      Create(check), run_time=0.9)
            n.at(4)
            every = T("every possible proof", size=27, color=PRED).move_to([0, -2.1, 0])
            infinity = M("∞", size=58, color=PRED).move_to([4.1, -1.5, 0])
            self.play(FadeIn(every), FadeIn(infinity), run_time=0.7)
            n.at(6)
            code = T("417 … 029", size=36, color=TRUTH, font=MONO).move_to(proof)
            self.play(FadeOut(proof_box), Transform(proof_lines, code), run_time=0.8)
            n.at(7)
            question = T("Does this number encode a contradiction?", size=27, color=PRED).move_to([0, -2.1, 0])
            self.play(Transform(every, question), run_time=0.7)
            n.at(8)
            self.wipe()
            theorem = self.heading("Gödel’s second incompleteness theorem", color=TRUTH)
            condition = T("If the rules are consistent…", size=33).move_to([0, 0.9, 0])
            conclusion = fitted(T("…they cannot prove their own consistency.", size=33, color=TRUTH)).move_to([0, -0.05, 0])
            qualifier = fitted(T("Mechanically specified rules · enough arithmetic · standard formal consistency",
                                 size=17, color=DIM)).move_to([0, -3.1, 0])
            n.at(9)
            self.play(FadeIn(condition), FadeIn(conclusion), FadeIn(qualifier), run_time=1.0)
            n.at(10)
            pa = rulebook("PA", width=2.1, height=1.65).scale(0.8).move_to([-2.0, -1.85, 0])
            zfc = rulebook("ZFC", color=HYPO, width=2.1, height=1.65).scale(0.8).move_to([2.0, -1.85, 0])
            self.play(FadeIn(pa), FadeIn(zfc), run_time=0.7)
        self.wipe()

    def model_pa(self):
        with self.narrate("model_pa") as n:
            title = self.heading("ZFC can build a model of PA")
            book = rulebook("PA").scale(0.9).move_to([-4.8, -0.15, 0])
            model = number_model().scale(0.67).move_to([1.5, -0.05, 0])
            n.at(2)
            self.play(FadeIn(book), FadeIn(model), run_time=0.9)
            n.at(3)
            meaning = T("A model is a world where the rules hold", size=27, color=PRED).move_to([0, 1.45, 0])
            checked = VGroup(tick_mark(size=0.25), T("arithmetic axioms hold", size=23, color=GOOD)).arrange(RIGHT, buff=0.18)
            checked.move_to([1.5, -1.5, 0])
            self.play(FadeIn(meaning), FadeIn(checked), run_time=0.7)
            n.at(4)
            arrow = Arrow([-3.45, -0.15, 0], [-2.2, -0.15, 0], color=GOOD, buff=0.1)
            self.play(GrowArrow(arrow), run_time=0.7)
            n.at(5)
            impossible = M("0 = 1", size=38, color=GAPC).move_to([1.5, -2.3, 0])
            cross = cross_mark(size=0.28).next_to(impossible, RIGHT, buff=0.25)
            self.play(FadeIn(impossible), Create(cross), run_time=0.65)
            n.at(6)
            result = T("PA is consistent — relative to ZFC", size=28, color=GOOD).move_to([0, -3.05, 0])
            self.play(FadeIn(result), run_time=0.7)
        self.wipe()

    def inaccessible(self):
        with self.narrate("inaccessible") as n:
            title = self.heading("One level beyond ZFC")
            ladder = VGroup(T("whole numbers", size=25, color=PRED), T("→", size=28),
                            T("larger infinities", size=25, color=HYPO), T("→", size=28),
                            M("κ", size=46, color=TRUTH)).arrange(RIGHT, buff=0.4).move_to([0, 0.3, 0])
            n.at(1)
            self.play(FadeIn(ladder), run_time=0.8)
            n.at(2)
            name = B("An inaccessible cardinal", size=34, color=TRUTH).move_to([0, 1.35, 0])
            self.play(FadeIn(name), run_time=0.65)
            n.at(3)
            world_box = card(7.8, 2.5, stroke=TRUTH)
            world_label = lines("sets below κ", "a world satisfying ZFC", size=30, color=HYPO).move_to(world_box)
            world = VGroup(world_box, world_label).move_to([0, -0.55, 0])
            self.play(FadeOut(ladder), FadeIn(world), run_time=0.8)
            n.at(4)
            result = T("This supplies a consistency proof for ZFC", size=27, color=GOOD).move_to([0, -2.45, 0])
            self.play(FadeIn(result), run_time=0.7)
            n.at(6)
            self.play(FadeOut(name), world.animate.scale(0.65).move_to([-3.1, -0.15, 0]), FadeOut(result), run_time=0.8)
            book = rulebook("ZFC", color=HYPO).move_to([3.8, 0.0, 0])
            statement = lines("cannot prove its", "own consistency", size=23, color=TRUTH).move_to([0.6, -2.3, 0])
            self.play(FadeIn(book), FadeIn(statement), run_time=0.7)
            n.at(7)
            missing = lines("cannot prove:", "‘an inaccessible exists’", size=22, color=TRUTH).move_to([3.7, -2.25, 0])
            self.play(FadeOut(statement), FadeIn(missing), run_time=0.7)
            n.at(8)
            arrow = CurvedArrow([2.35, 0.25, 0], [-0.4, 0.25, 0], angle=0.65, color=TRUTH)
            back = CurvedArrow([-0.4, -0.7, 0], [2.35, -0.7, 0], angle=0.65, color=GOOD)
            self.play(Create(arrow), Create(back), run_time=1.1)
            n.at(9)
            self.wipe()
            title = self.heading("An additional foundational assumption")
            theories = VGroup()
            for x, label, color in [(-4.3, "PA", PRED), (0, "ZFC", HYPO), (4.3, "ZFC + inaccessible", TRUTH)]:
                box = card(3.8, 1.3, stroke=color).move_to([x, 0.05, 0])
                word = fitted(B(label, size=26, color=color), width=3.4).move_to(box)
                theories.add(VGroup(box, word))
            arrows = VGroup(*[Arrow([x, 0.05, 0], [x - 0.42, 0.05, 0], buff=0, color=GOOD,
                                    max_tip_length_to_length_ratio=0.3) for x in (-1.92, 2.38)])
            self.play(FadeIn(theories), FadeIn(arrows), run_time=0.9)
            summary = T("Stronger rules can justify consistency below", size=27, color=GOOD).move_to([0, -1.5, 0])
            qualifier = fitted(T("Assuming ZFC is consistent · here ‘inaccessible’ means strongly inaccessible",
                                 size=16, color=DIM)).move_to([0, -3.1, 0])
            self.play(FadeIn(summary), FadeIn(qualifier), run_time=0.7)
        self.wipe()

    def lean_rh(self):
        with self.narrate("lean_rh") as n:
            title = self.heading("How much of this background is needed?")
            blocks = VGroup()
            for y, label, color, width in [(-1.8, "ZFC", PRED, 10.8),
                                           (-0.55, "Suitable inaccessible cardinals", HYPO, 9),
                                           (0.7, "A standard model of Lean’s universes", INK, 7.2)]:
                box = card(width, 0.95, stroke=color).move_to([0, y, 0])
                word = fitted(T(label, size=25, color=color), width=width - 0.4).move_to(box)
                blocks.add(VGroup(box, word))
            n.at(1)
            self.play(LaggedStart(*[FadeIn(block) for block in blocks], lag_ratio=0.25), run_time=1.2)
            n.at(3)
            arithmetic = B("RH can be expressed in arithmetic", size=38, color=TRUTH).move_to([0, 0.65, 0])
            explanation = T("Statements about whole numbers", size=27, color=DIM).move_to([0, -0.25, 0])
            self.play(FadeOut(blocks), FadeIn(arithmetic), FadeIn(explanation), run_time=0.8)
            n.at(5)
            question = lines("How much of the proof can be", "brought down to that level?", size=31, color=PRED).move_to([0, -1.7, 0])
            self.play(FadeIn(question), run_time=0.7)
        self.wipe()

    def acl2(self):
        with self.narrate("acl2") as n:
            title = self.heading("ACL2: computation and induction", color=PRED)
            meaning = lines("A Computational Logic for", "Applicative Common Lisp", size=29).move_to([0, 0.9, 0])
            language = T("Common Lisp is the programming language", size=25, color=DIM).move_to([0, -0.35, 0])
            self.play(FadeIn(meaning), run_time=0.7)
            n.at(1)
            self.play(FadeIn(language), run_time=0.65)
            n.at(3)
            examples = VGroup(T("[1, 2, …, n]", size=32, color=PRED, font=MONO),
                              M("½ + ⅓ = ⅚", size=40, color=TRUTH),
                              T("n uses n − 1", size=30, color=GOOD)).arrange(RIGHT, buff=0.8)
            fitted(examples).move_to([0, 0.3, 0])
            self.play(FadeOut(meaning), FadeOut(language), FadeIn(examples), run_time=0.8)
            induction = T("first case  +  each case gives the next", size=27, color=GOOD).move_to([0, -1.3, 0])
            self.play(FadeIn(induction), run_time=0.6)
            n.at(4)
            self.play(Indicate(induction, color=GOOD), run_time=0.8)
            n.at(5)
            target = T("Target: roughly PA strength, with a precise interpretation", size=24, color=DIM).move_to([0, -2.7, 0])
            self.play(FadeIn(target), run_time=0.65)
        self.wipe()

    def goal(self):
        with self.narrate("goal", tail=1.0) as n:
            name = fitted(B("landau-windows-acl2", size=46, color=PRED)).move_to([0, 2.0, 0])
            title = B("The Landau reduction in ACL2", size=33).move_to([0, 1.0, 0])
            self.play(FadeIn(name), FadeIn(title), run_time=0.9)
            n.at(1)
            row = VGroup(B("Compute", size=30, color=TRUTH), T("→", size=33),
                         B("Prove success", size=30, color=GOOD), T("→", size=33),
                         B("Interpret Landau", size=30, color=PRED)).arrange(RIGHT, buff=0.35)
            fitted(row).move_to([0, -0.15, 0])
            self.play(FadeIn(row), run_time=0.8)
            n.at(3)
            status = T("The full arithmetic reduction is in progress", size=25, color=DIM).move_to([0, -1.45, 0])
            self.play(FadeIn(status), run_time=0.65)
            n.at(4)
            ending = B("Same result. Fewer assumptions.", size=40, color=TRUTH).move_to([0, -2.4, 0])
            credit = fitted(T("Original Landau animations: Hart Traveller’s riemann · narration: tiny-voca M2",
                              size=14, color=DIM)).to_edge(DOWN, buff=0.25)
            self.play(FadeIn(ending), FadeIn(credit), run_time=0.8)
