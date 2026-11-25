"""Shared lesson layout and phrase-synchronized local narration."""
from foundations_story import *


def tiles(n, unit=0.48, corner=(-4.7, -1.6, 0), color=PRED):
    corner = np.array(corner)
    return VGroup(*[Square(side_length=unit, stroke_color=color, stroke_width=1.8,
                          fill_color=color, fill_opacity=0.12).move_to(
                              corner + RIGHT * (i + 0.5) * unit + UP * (j + 0.5) * unit)
                    for j in range(n) for i in range(n)])


class PhraseNarration(LocalNarration):
    def at_phrase(self, sentence, phrase):
        cue = self.segment["sentences"][sentence]["phrases"][phrase]
        desired = self.t0 + cue["start"]
        if desired > self.scene.time:
            self.scene.wait(desired - self.scene.time)
        elif self.scene.time - desired > 1.2:
            print(f"Phrase late: {self.segment['id']}:{sentence}:{phrase} "
                  f"by {self.scene.time - desired:.2f}s")


class LessonScene(LandauFoundationsStory):
    def construct(self):
        manifest = json.loads((ROOT / "audio" / self.manifest_file).read_text(encoding="utf8"))
        self.script = {s["id"]: s for s in manifest["segments"]}
        self.timings = []
        self.corner_label = T("landau-windows-acl2", size=16, color=DIM).to_corner(UL, buff=0.2)
        self.draft = T(self.review_label, size=13, color=DIM).to_corner(UR, buff=0.2)
        self.add(self.corner_label, self.draft)
        for method in self.lesson_methods:
            getattr(self, method)()
        self.wait(2)
        (ROOT / "media" / self.timing_file).write_text(json.dumps(self.timings, indent=2), encoding="utf8")

    def narrate(self, key, tail=0.85):
        return PhraseNarration(self, key, tail)

    @staticmethod
    def code(text, size=28, color=PRED):
        return fitted(T(text, size=size, color=color, font="Consolas"), 12.0)

    def caption(self, text, y=-3.15, color=DIM, size=24):
        return fitted(T(text, size=size, color=color), 12.2).move_to([0, y, 0])

    def chip(self, text, color=PRED, width=3.2):
        frame = RoundedRectangle(width=width, height=1.05, corner_radius=0.13,
                                 stroke_color=color, fill_color=PANEL, fill_opacity=1)
        label = fitted(T(text, size=25, color=color), width-0.3).move_to(frame)
        return VGroup(frame, label)
