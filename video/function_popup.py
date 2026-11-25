"""Show exact checked function definitions before using compact call names."""
import re
from foundations_story import *


def read_form(book, kind, name):
    source = (ROOT / book).read_text(encoding="utf8")
    match = re.search(r"\(" + re.escape(kind) + r"\s+" + re.escape(name) + r"\s", source, re.I)
    if not match:
        raise ValueError(f"No {kind} named {name} in {book}")
    depth = 0
    in_string = in_comment = escaped = False
    for index in range(match.start(), len(source)):
        char = source[index]
        if in_comment:
            if char == "\n": in_comment = False
            continue
        if in_string:
            if escaped: escaped = False
            elif char == "\\": escaped = True
            elif char == '"': in_string = False
            continue
        if char == ";": in_comment = True
        elif char == '"': in_string = True
        elif char == "(": depth += 1
        elif char == ")":
            depth -= 1
            if depth == 0: return source[match.start():index+1]
    raise ValueError(f"Unclosed definition of {name}")


def read_defun(book, name):
    return read_form(book, "defun", name)


class FunctionPopup(VGroup):
    def __init__(self, book, name, note="", kind="defun", **kwargs):
        super().__init__(**kwargs)
        self.source_text = read_form(book, kind, name)
        background = RoundedRectangle(width=12.5, height=6.1, corner_radius=.2,
                                      stroke_color=PRED, stroke_width=2.5,
                                      fill_color=PANEL, fill_opacity=1).move_to([0,-.05,0])
        label = "function definition" if kind == "defun" else "theorem"
        heading = fitted(T("ACL2 " + label + " · " + name, size=25, color=TRUTH),11.5).move_to([0,2.1,0])
        self.body = fitted(T(self.source_text,size=30,color=INK,font="Consolas"),11.3)
        if self.body.height > 3.25: self.body.scale_to_fit_height(3.25)
        self.body.move_to([0,-.1,0])
        self.footer = fitted(T(note,size=22,color=DIM),11.5).move_to([0,-2.35,0])
        self.add(background,heading,self.body,self.footer)

    def focus(self, line):
        count = len(self.source_text.splitlines())
        if not 0 <= line < count: raise ValueError("Function line outside definition")
        height = self.body.height / count
        return Rectangle(width=self.body.width+.35,height=height+.12,
                         stroke_color=TRUTH,stroke_width=1.6,
                         fill_color=TRUTH,fill_opacity=.055).move_to(
                             [self.body.get_center()[0],self.body.get_top()[1]-(line+.5)*height,0])

    def badge(self, text, position=(0,0,0), width=7.4):
        frame=RoundedRectangle(width=width,height=.82,corner_radius=.13,
                               stroke_color=PRED,fill_color=PANEL,fill_opacity=1)
        name=fitted(T(text,size=25,color=PRED,font="Consolas"),width-.35).move_to(frame)
        return VGroup(frame,name).move_to(position)
