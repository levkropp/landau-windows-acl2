"""Readable source cards for longer definitions and theorem statements."""
import textwrap
from function_popup import *


class PagedSourcePopup(FunctionPopup):
    def __init__(self, book, name, note="", kind="defun", page_size=7):
        super().__init__(book,name,note,kind=kind)
        self[0].stretch_to_fit_height(6.65)
        self.display_lines=[]
        self.origins=[]
        for origin,line in enumerate(self.source_text.splitlines()):
            indent=len(line)-len(line.lstrip())
            wrapped=textwrap.wrap(line,width=72,subsequent_indent=" "*(indent+2),
                                  break_long_words=False,break_on_hyphens=False,
                                  replace_whitespace=False) or [""]
            self.display_lines.extend(wrapped)
            self.origins.extend([origin]*len(wrapped))
        self.page_size=page_size
        self.page_count=(len(self.display_lines)+page_size-1)//page_size
        self.page_index=0
        self.body.become(self.page_body(0))
        self.page_tag=self.page_label(0)
        self.add(self.page_tag)

    def page_body(self,index):
        lines=self.display_lines[index*self.page_size:(index+1)*self.page_size]
        body=fitted(T("\n".join(lines),size=30,color=INK,font="Consolas"),11.3)
        if body.height>3.25:body.scale_to_fit_height(3.25)
        return body.move_to([0,-.1,0])

    def page_label(self,index):
        suffix="complete source" if self.page_count==1 else "same source, continued across cards"
        return T(f"Page {index+1} of {self.page_count} · {suffix}",
                 size=17,color=DIM).move_to([0,-2.95,0])

    def turn_page(self,scene,index):
        if not 0<=index<self.page_count:raise ValueError("Source page outside definition")
        scene.play(Transform(self.body,self.page_body(index)),
                   Transform(self.page_tag,self.page_label(index)),run_time=.65)
        self.page_index=index

    def focus(self,source_line):
        start=self.page_index*self.page_size
        end=min(start+self.page_size,len(self.display_lines))
        rows=[i-start for i in range(start,end) if self.origins[i]==source_line]
        if not rows:raise ValueError("Source line is not on the displayed page")
        height=self.body.height/(end-start)
        return Rectangle(width=self.body.width+.35,height=len(rows)*height+.12,
                         stroke_color=TRUTH,stroke_width=1.6,
                         fill_color=TRUTH,fill_opacity=.055).move_to(
            [0,self.body.get_top()[1]-(sum(rows)/len(rows)+.5)*height,0])
