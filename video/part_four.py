"""Part Four: prime powers, rational primitive bounds, and the centered sum."""
import math
from fractions import Fraction
from lesson_scene import *
from lesson_source import PagedSourcePopup
from part_two import RationalRuler
from part_three import math_label


SOURCE_FILES={
    "landau-bounds":["lw-rational-power"],
    "prime-powers":["lw-no-divisor","lw-primep","lw-power-exponent","lw-prime-power-search","lw-prime-power-data","lw-mangoldt-bounds"],
    "rational-window":["lw-precision-fuel"],
    "log-bounds":["lw-log-rectangles","lw-log-count","lw-log-bounds"],
    "euler-bounds":["lw-harmonic","lw-euler-count","lw-euler-from-log","lw-euler-bounds"],
    "signal-bounds":["lw-ramp","lw-smoothed-sum-bounds","lw-gz-bounds-raw","lw-signal-count","lw-interval-width"]}
SOURCE_LOOKUP={name:".tools/acl2-part04/acl2/"+file+".lisp" for file,names in SOURCE_FILES.items() for name in names}
PRIME_BASES={2:2,3:3,4:2,5:5,7:7,8:2,9:3,11:11,13:13,16:2}


class LogArea(VGroup):
    def __init__(self,count=4,**kwargs):
        super().__init__(**kwargs)
        self.count=count
        self.axes=VGroup(Line(self.point(1,0),self.point(2,0),color=DIM),
                         math_label("1",size=25,color=DIM).move_to(self.point(1,0)+DOWN*.32),
                         math_label("2",size=25,color=DIM).move_to(self.point(2,0)+DOWN*.32),
                         math_label("1/t",size=28,color=TRUTH).move_to([-4.9,.7,0]))
        self.curve=VMobject(color=TRUTH,stroke_width=3).set_points_as_corners([self.point(t,1/t) for t in np.linspace(1,2,100)])
        self.lower=VGroup();self.upper=VGroup()
        for i in range(count):
            left=1+i/count;right=1+(i+1)/count
            self.lower.add(self.rectangle(left,right,1/right,PRED))
            self.upper.add(self.rectangle(left,right,1/left,GOOD))
        self.add(self.axes,self.curve)

    def point(self,x,y):return np.array([-4.2+(x-1)*8.4,-1.6+2.3*y,0])

    def rectangle(self,left,right,height,color):
        return Polygon(self.point(left,0),self.point(right,0),self.point(right,height),self.point(left,height),
                       stroke_color=color,stroke_width=1.5,fill_color=color,fill_opacity=.22)


class PartFour(LessonScene):
    manifest_file="manifest-part04.json"
    timing_file="timing-part04.json"
    review_label="PART FOUR · REVIEW 01"
    lesson_methods=("opening","powers","integer_power","primality","power_search","log_area",
                    "rectangles","log_precision","mangoldt","ramps","smoothed","padding",
                    "sum_code","continuity","gamma","gamma_code","centered","gz_code","budget","next")

    def popup(self,name,note="",kind="defun",page_size=8):
        book="teaching-part04.lisp" if name.startswith("video-") else SOURCE_LOOKUP[name]
        popup=PagedSourcePopup(book,name,note,kind=kind,page_size=page_size)
        self.play(FadeIn(popup,scale=.96),run_time=.8)
        return popup

    def weight_table(self):
        cells=VGroup()
        for n in range(1,17):
            base=PRIME_BASES.get(n);color=PRED if base else DIM
            frame=RoundedRectangle(width=2.45,height=.75,corner_radius=.07,stroke_color=FAINT,fill_color=PANEL,fill_opacity=1)
            number=math_label(str(n),size=24).move_to([-.65,0,0])
            weight=math_label("ln "+str(base) if base else "0",size=25,color=color).move_to([.55,0,0])
            cells.add(VGroup(frame,number,weight))
        return cells.arrange_in_grid(rows=4,cols=4,buff=.15).move_to([0,.1,0])

    def opening(self):
        with self.narrate("opening") as n:
            title=self.heading("Build the signal that the search will inspect")
            self.play(FadeIn(self.chip("justified sample intervals",GOOD,width=7).move_to([0,.7,0])),run_time=.7)
            n.at(2);self.play(FadeIn(math_label("1, 2, 3, 4, 5, 6, …",size=43,color=PRED).move_to([0,-.6,0])),run_time=.7)
            n.at(3)
            self.wipe(title)
            pipeline=VGroup(*[self.chip(s,c,width=3.5) for s,c in [("prime powers",PRED),("weighted ramps",TRUTH),("centered signal",GOOD)]]).arrange(RIGHT,buff=.35).move_to([0,.25,0]);self.play(FadeIn(pipeline),run_time=.9)
            n.at(6);self.play(FadeIn(self.caption("Finite arithmetic + explicit real interpretation",color=TRUTH,size=28)),run_time=.7)
            n.at(7);self.play(Transform(title,fitted(B("Part Four · Prime powers and a smoothed signal",size=40)).move_to(title)),run_time=.8)
        self.wipe()

    def powers(self):
        with self.narrate("powers") as n:
            title=self.heading("A prime base and a positive integer exponent")
            self.play(FadeIn(math_label("prime: at least 2; no proper divisor",size=36,color=PRED).move_to([0,1,0])),run_time=.7)
            n.at(2)
            chain=VGroup(*[self.chip(s,PRED,width=2.5) for s in ["2¹ = 2","2² = 4","2³ = 8","2⁴ = 16"]]).arrange(RIGHT,buff=.35).move_to([0,-.2,0]);self.play(LaggedStart(*[FadeIn(c) for c in chain],lag_ratio=.25),run_time=1.1)
            n.at(3);self.play(FadeIn(self.caption("13 = 13¹ also counts",y=-1.6,color=GOOD,size=29)),run_time=.65)
            n.at(4)
            self.wipe(title)
            cases=VGroup(math_label("6 = 2 × 3     two distinct prime factors",size=33,color=GAPC),math_label("1 is excluded: exponent must be positive",size=33,color=GAPC),math_label("16 = 4² = 2⁴     use the prime base 2",size=33,color=GOOD)).arrange(DOWN,buff=.65).move_to([0,.05,0])
            self.play(FadeIn(cases[0]),run_time=.7)
            n.at(5);self.play(FadeIn(cases[1]),run_time=.7)
            n.at(6);self.play(FadeIn(cases[2]),run_time=.7)
            n.at(8)
            self.wipe(title)
            weight=VGroup(math_label("von Mangoldt weight  Λ(n)",size=40,color=TRUTH),math_label("ln p  when n = pᵏ, p prime, k ≥ 1",size=34,color=PRED),math_label("0 otherwise",size=34,color=DIM)).arrange(DOWN,buff=.5).move_to([0,.05,0]);self.play(FadeIn(weight),run_time=.9)
            n.at(11);self.play(FadeIn(self.caption("Λ(2) = Λ(4) = Λ(8) = Λ(16) = ln 2",color=GOOD,size=28)),run_time=.7)
        self.wipe()

    def integer_power(self):
        with self.narrate("integer_power") as n:
            title=self.heading("Natural-number exponents: multiply repeatedly")
            factors=math_label("2",size=55,color=PRED).move_to([0,.5,0]);self.play(FadeIn(factors),run_time=.65)
            n.at(2)
            for phrase,formula in [(0,"2 = 2"),(1,"2 × 2 = 4"),(2,"2 × 2 × 2 = 8"),(3,"2 × 2 × 2 × 2 = 16")]:
                n.at_phrase(2,phrase);self.play(Transform(factors,math_label(formula,size=46,color=PRED).move_to(factors)),run_time=.65)
            zero_power=math_label("base⁰ = 1",size=39,color=TRUTH).move_to([0,-1,0])
            n.at(3);self.play(FadeIn(zero_power),run_time=.65)
            n.at(4)
            popup=self.popup("lw-rational-power","A rational base; a natural exponent · repeated multiplication")
            self.remove(factors,zero_power)
            n.at(7);focus=popup.focus(4);self.play(Create(focus),run_time=.65)
            n.at(8);self.play(Transform(focus,popup.focus(1)),run_time=.65)
            n.at(9)
            self.play(FadeOut(focus),ReplacementTransform(popup,popup.badge("(lw-rational-power 2 4) → 16",(0,.1,0),width=10)),run_time=.9)
        self.wipe()

    def primality(self):
        with self.narrate("primality") as n:
            title=self.heading("A remainder test checks trial divisibility")
            n.at(1);self.play(FadeIn(math_label("divides exactly  ⇔  remainder = 0",size=37,color=TRUTH).move_to([0,.7,0])),run_time=.7)
            n.at(3);self.play(FadeIn(self.code("(mod 16 2) → 0",size=36).move_to([0,-.6,0])),FadeIn(self.caption("16 has a proper divisor, so it is not prime",color=GAPC,size=27)),run_time=.8)
            n.at(4)
            popup=self.popup("lw-no-divisor","nfix keeps a natural number unchanged and returns zero for anything else.")
            n.at(5);focus=popup.focus(4);self.play(Create(focus),run_time=.65)
            n.at(6);self.play(Transform(focus,popup.focus(5)),run_time=.65)
            n.at(7)
            prime=self.popup("lw-primep","Integer ≥ 2 · every trial divisor from value − 1 down to 2")
            n.at(8);self.play(Transform(prime.footer,T("For 2: the trial bound is 1, so the no-divisor base case applies",size=21,color=GOOD).move_to(prime.footer)),run_time=.7)
            n.at(9);self.play(Transform(prime.footer,T("For 13: none of 12, 11, …, 2 divides it",size=24,color=GOOD).move_to(prime.footer)),run_time=.7)
            n.at(10)
            self.wipe(title)
            self.play(FadeIn(self.code("(lw-primep 2) → t\n(lw-primep 13) → t\n(lw-primep 16) → nil",size=32).move_to([0,.15,0])),run_time=.8)
            self.play(FadeIn(self.caption("Soundness: a reported prime has no proper divisor",color=GOOD,size=25)),run_time=.65)
        self.wipe()

    def power_search(self):
        with self.narrate("power_search") as n:
            title=self.heading("A bounded search returns a prime-power certificate")
            n.at(1)
            exponent=self.popup("lw-power-exponent","Try positive exponents downwards; return a matching exponent or nil")
            n.at(2);self.play(Indicate(exponent.body,color=TRUTH),run_time=.9)
            n.at(4)
            search=self.popup("lw-prime-power-search","Check a candidate prime base, then its possible exponents",page_size=6)
            n.at(6);self.play(Indicate(search.body,color=TRUTH),run_time=.9)
            n.at(7);search.turn_page(self,1)
            n.at(8);self.play(Transform(search.footer,T("Success: (prime-base . exponent) · otherwise decrease the candidate",size=21,color=GOOD).move_to(search.footer)),run_time=.7)
            n.at(10)
            self.wipe(title)
            limits=math_label("p ≤ pᵏ     and     k ≤ pᵏ",size=44,color=TRUTH).move_to([0,.7,0])
            limit_note=self.caption("p prime, k a positive integer",y=-.55,color=PRED,size=28)
            self.play(FadeIn(limits),FadeIn(limit_note),run_time=.85)
            n.at(12)
            wrapper=self.popup("lw-prime-power-data","Begin the base and exponent searches with the natural target as bound")
            self.remove(limits,limit_note)
            n.at(13)
            self.play(ReplacementTransform(wrapper,wrapper.badge("(lw-prime-power-data value)",(0,1.1,0),width=9.4)),run_time=.9)
            calls=VGroup(*[self.code(text,size=34) for text in ["16 → '(2 . 4)","13 → '(13 . 1)","6 → nil"]]).arrange(DOWN,buff=.35).move_to([0,-.7,0])
            self.play(FadeIn(calls[0]),run_time=.65)
            n.at_phrase(13,1);self.play(FadeIn(calls[1]),run_time=.65)
            n.at_phrase(13,2);self.play(FadeIn(calls[2]),run_time=.65)
        self.wipe()

    def log_area(self):
        with self.narrate("log_area") as n:
            title=self.heading("Natural log: area under 1/t")
            graph=LogArea();self.play(FadeIn(graph),run_time=.85)
            n.at(3);self.play(LaggedStart(*[Create(r) for r in graph.lower],lag_ratio=.15),run_time=1)
            n.at(4);self.play(FadeIn(self.caption("Right-endpoint heights give lower areas",y=1.25,color=PRED,size=28)),run_time=.65)
            n.at(5);self.play(LaggedStart(*[Create(r) for r in graph.upper],lag_ratio=.15),run_time=1)
            n.at(6)
            self.play(FadeIn(self.caption("lower sum ≤ ln 2 ≤ upper sum",y=-2.55,color=GOOD,size=29)),run_time=.7)
            n.at(8)
            self.wipe(title)
            interval=math_label("533/840  ≤  ln 2  ≤  319/420",size=43,color=TRUTH).move_to([0,.65,0]);self.play(FadeIn(interval),run_time=.8)
            n.at(11);self.play(FadeIn(math_label("gap = 1/8",size=38,color=GOOD).move_to([0,-.75,0])),run_time=.65)
            n.at(12);self.play(FadeIn(self.caption("Real area interpretation + finite rational endpoint calculations",size=24,color=PRED)),run_time=.7)
        self.wipe()

    def rectangles(self):
        with self.narrate("rectangles") as n:
            title=self.heading("One interval per rectangle, then add")
            popup=self.popup("lw-log-rectangles","start > 0 · step ≥ 0 · a natural count of pieces")
            n.at(2);focus=popup.focus(3);self.play(Create(focus),run_time=.65)
            n.at(3);self.play(Transform(focus,popup.focus(5)),Transform(popup.footer,T("lower = step/(start + step) · upper = step/start",size=23,color=TRUTH).move_to(popup.footer)),run_time=.7)
            n.at(6);self.play(Transform(focus,popup.focus(6)),run_time=.65)
            n.at(7);self.play(Transform(focus,popup.focus(4)),run_time=.65)
            n.at(9)
            self.wipe(title)
            self.play(FadeIn(self.code("(lw-log-rectangles 1 1/4 4)\n→ '(533/840 . 319/420)",size=34).move_to([0,.45,0])),run_time=.8)
            n.at(10);self.play(FadeIn(self.caption("A general width theorem controls the remaining gap",color=GOOD,size=27)),run_time=.65)
        self.wipe()

    def log_precision(self):
        with self.narrate("log_precision") as n:
            title=self.heading("A positive width target chooses finite work")
            self.play(FadeIn(math_label("epsilon > 0",size=43,color=TRUTH).move_to([0,.7,0])),run_time=.65)
            n.at(2)
            fuel=self.popup("lw-precision-fuel","Use the numerator of width and denominator of epsilon in reduced form")
            n.at(3);self.play(Indicate(fuel.body,color=TRUTH),run_time=.9)
            n.at(5);count=self.popup("lw-log-count","Add one so the rectangle count is positive")
            n.at(6)
            self.play(Transform(count.footer,T("value = 2, epsilon = 1/4: fuel = 4, count = 5, step = 1/5",size=21,color=GOOD).move_to(count.footer)),run_time=.7)
            n.at(7)
            bounds=self.popup("lw-log-bounds","let* computes bindings in sequence: count, then step")
            n.at(8);focus=bounds.focus(1);self.play(Create(focus),run_time=.65)
            n.at(9);self.play(Transform(focus,bounds.focus(2)),run_time=.65)
            n.at(10);self.play(Transform(focus,bounds.focus(3)),run_time=.65)
            n.at(12)
            self.wipe(title)
            coarse=self.code("(lw-log-bounds 2 1)\n→ '(7/12 . 5/6)",size=33).move_to([0,.9,0]);self.play(FadeIn(coarse),run_time=.75)
            n.at(13)
            fine=self.code("(lw-log-bounds 2 1/4)\n→ '(1627/2520 . 1879/2520)",size=31).move_to([0,-.85,0]);self.play(FadeIn(fine),run_time=.75)
            n.at(14);self.play(FadeIn(self.caption("Requested width 1/4 · actual width 1/10 in the refined example",size=24,color=GOOD)),run_time=.65)
        self.wipe()

    def mangoldt(self):
        with self.narrate("mangoldt") as n:
            title=self.heading("Prime-power data chooses the correct log interval")
            n.at(1);popup=self.popup("lw-mangoldt-bounds","Found a prime power: enclose ln(prime base) · otherwise return [0,0]")
            n.at(3);focus=popup.focus(2);self.play(Create(focus),run_time=.65)
            n.at(5)
            self.wipe(title)
            self.play(FadeIn(self.code("(lw-mangoldt-bounds 16 1) → '(7/12 . 5/6)",size=28).move_to([0,.75,0])),run_time=.75)
            n.at(6);self.play(FadeIn(self.code("(lw-mangoldt-bounds 6 1)  → '(0 . 0)",size=28).move_to([0,-.6,0])),run_time=.75)
            n.at(8)
            self.wipe(title)
            table=self.weight_table();self.play(FadeIn(table),run_time=.9)
            for i in [1,3,7,15]:self.play(Indicate(table[i],color=TRUTH),run_time=.5)
            n.at(9);self.play(FadeIn(self.caption("Arithmetic enclosures + a proved identification with Λ(n)",size=25,color=GOOD)),run_time=.7)
        self.wipe()

    def ramps(self):
        with self.narrate("ramps") as n:
            title=self.heading("A weight starts with a zero ramp")
            self.play(FadeIn(math_label("ramp(x,n) = max(0, x/n − 1)",size=41,color=TRUTH).move_to([0,.9,0])),run_time=.75)
            n.at(2);self.play(FadeIn(math_label("x < n:  0",size=35,color=DIM).move_to([-3,-.4,0])),run_time=.65)
            n.at(3);self.play(FadeIn(math_label("x = n:  0",size=35,color=PRED).move_to([3,-.4,0])),run_time=.65)
            n.at(5);self.popup("lw-ramp","Use a positive integer index · max selects the larger of its two arguments")
            n.at(6)
            self.wipe(title)
            axis=RationalRuler(3,5,[(3,"3"),(3.5,"7/2"),(4,"4"),(4.5,"9/2"),(5,"5")],y=-.7)
            def point(x):return axis.point(x)+UP*(max(0,x/4-1)*4)
            line=VMobject(color=PRED,stroke_width=4).set_points_as_corners([point(3),point(4),point(5)])
            dot=Dot(point(3.5),color=TRUTH,radius=.1);label=math_label("x = 7/2, n = 4: coefficient 0",size=35,color=TRUTH).move_to([0,1,0])
            self.play(FadeIn(axis),Create(line),FadeIn(dot),FadeIn(label),run_time=.85)
            n.at_phrase(6,1);self.play(dot.animate.move_to(point(4)),Transform(label,math_label("x = 4, n = 4: coefficient 0",size=35,color=TRUTH).move_to(label)),run_time=.8)
            n.at_phrase(6,2);self.play(dot.animate.move_to(point(4.5)),Transform(label,math_label("x = 9/2, n = 4: coefficient 1/8",size=35,color=GOOD).move_to(label)),run_time=.8)
            n.at(9);self.play(FadeIn(self.caption("contribution = Λ(n) × ramp(x,n)",color=GOOD,size=30)),run_time=.65)
        self.wipe()

    def smoothed(self):
        with self.narrate("smoothed") as n:
            title=self.heading("Add the weighted ramps to define S_z")
            sigma=math_label("∑",size=57,color=TRUTH)
            limits=VGroup(sigma,math_label("n = 1",size=20,color=TRUTH).next_to(sigma,DOWN,buff=.06),
                          math_label("⌊x⌋",size=20,color=TRUTH).next_to(sigma,UP,buff=.06))
            formula=VGroup(math_label("S_z(x) =",size=37,color=TRUTH),limits,
                           math_label("Λ(n) × (x/n − 1)",size=37,color=TRUTH)).arrange(RIGHT,buff=.35).move_to([0,1,0])
            self.play(FadeIn(formula),run_time=.8)
            n.at(2);self.play(FadeIn(self.caption("⌊x⌋ is the largest whole number not exceeding x",y=-.15,size=26)),run_time=.65)
            n.at(3);self.play(FadeIn(math_label("x = 9/2  ⇒  ⌊x⌋ = 4",size=39,color=GOOD).move_to([0,-1.3,0])),run_time=.7)
            n.at(4)
            self.wipe(title)
            terms=VGroup(*[math_label(s,size=33,color=c) for s,c in [("n = 1:  Λ(1) = 0",DIM),("n = 2:  (5/4) ln 2",PRED),("n = 3:  (1/2) ln 3",TRUTH),("n = 4:  (1/8) ln 2",PRED)]]).arrange(DOWN,buff=.35).move_to([0,.1,0])
            self.play(FadeIn(terms[0]),run_time=.65)
            for i in range(1,4):n.at(4+i);self.play(FadeIn(terms[i]),run_time=.65)
            n.at(8);self.play(Indicate(terms[1],color=PRED),Indicate(terms[3],color=PRED),run_time=.9)
            n.at(9)
            self.wipe(title)
            self.play(FadeIn(math_label("S_z(9/2) = (11/8) ln 2 + (1/2) ln 3",size=40,color=GOOD).move_to([0,.4,0])),run_time=.8)
        self.wipe()

    def padding(self):
        with self.narrate("padding") as n:
            title=self.heading("Choose a cutoff that covers every active term")
            n.at(1);self.play(FadeIn(math_label("x = numerator / denominator ≤ numerator",size=36,color=TRUTH).move_to([0,.7,0])),FadeIn(self.caption("x ≥ 1 · reduced denominator is a positive integer",y=-.5,size=26)),run_time=.85)
            n.at(2);self.popup("lw-signal-count","For x ≥ 1: the positive numerator is a natural cutoff at least x")
            n.at(3)
            self.wipe(title)
            cells=VGroup(*[self.chip(str(i),PRED if i<=4 else DIM,width=1.0) for i in range(1,10)]).arrange(RIGHT,buff=.18).move_to([0,.65,0]);self.play(FadeIn(cells),run_time=.9)
            self.play(FadeIn(self.code("(lw-signal-count 9/2) → 9",size=31).move_to([0,-.7,0])),run_time=.7)
            n.at(5);self.play(FadeIn(math_label("n ≥ x  ⇒  max(0, x/n − 1) = 0",size=36,color=TRUTH).move_to([0,-1.8,0])),run_time=.7)
            n.at(6);self.play(LaggedStart(*[Indicate(c,color=DIM) for c in cells[4:]],lag_ratio=.12),run_time=1)
            n.at(7);self.play(FadeIn(self.caption("Padding with zero terms preserves the sum",color=GOOD,size=28)),run_time=.65)
        self.wipe()

    def sum_code(self):
        with self.narrate("sum_code") as n:
            title=self.heading("A recursive sum of certified intervals")
            popup=self.popup("lw-smoothed-sum-bounds","x, a natural cutoff, and a positive primitive precision",page_size=5)
            n.at(2);focus=popup.focus(3);self.play(Create(focus),run_time=.65)
            n.at(3);self.play(FadeOut(focus),run_time=.3);popup.turn_page(self,1)
            n.at(4);self.play(Indicate(popup.body,color=TRUTH),run_time=.9)
            n.at(6)
            self.wipe(title)
            self.play(FadeIn(self.code("(lw-smoothed-sum-bounds 9/2 9 1)\n→ '(12661/10080 . 3061/1680)",size=31).move_to([0,.6,0])),run_time=.85)
            n.at(7);self.play(FadeIn(math_label("same interval as (11/8)·logBounds(2) + (1/2)·logBounds(3)",size=27,color=GOOD).move_to([0,-.9,0])),run_time=.75)
            n.at(9)
            self.wipe(title)
            steps=VGroup(math_label("0 ≤ ramp(x,n) ≤ x",size=38,color=PRED),math_label("each scaled width ≤ x × epsilon",size=36,color=TRUTH),math_label("sum width ≤ count × x × epsilon",size=37,color=GOOD)).arrange(DOWN,buff=.65).move_to([0,-.1,0])
            self.play(FadeIn(steps[0]),run_time=.65)
            n.at(10);self.play(FadeIn(steps[1]),run_time=.65)
            n.at(11);self.play(FadeIn(steps[2]),run_time=.65)
        self.wipe()

    def continuity(self):
        with self.narrate("continuity") as n:
            title=self.heading("Ramps join continuously, with possible corners")
            def value(x):return sum(math.log(p)*max(0,x/i-1) for i,p in PRIME_BASES.items() if i<=6)
            def point(x):return np.array([-5+(x-1)*2,-1.5+.8*value(x),0])
            axis=Line([-5,-1.5,0],[5,-1.5,0],color=DIM)
            ticks=VGroup(*[math_label(str(i),size=24,color=DIM).move_to([-5+(i-1)*2,-1.85,0]) for i in range(1,7)])
            curve=VMobject(color=PRED,stroke_width=4).set_points_as_corners([point(x) for x in np.linspace(1,6,151)])
            n.at(2);self.play(Create(axis),FadeIn(ticks),Create(curve),run_time=1.1)
            marker=Dot(point(3.5),color=TRUTH,radius=.1);self.play(FadeIn(marker),run_time=.6)
            n.at(3);self.play(marker.animate.move_to(point(4)),run_time=1)
            n.at(4);self.play(FadeIn(math_label("new term at x = 4:  Λ(4) × 0 = 0",size=33,color=TRUTH).move_to([0,1.1,0])),run_time=.7)
            n.at(5);self.play(marker.animate.move_to(point(4.5)),run_time=1)
            n.at(6);self.play(FadeIn(self.caption("On this bounded range, one fixed finite cutoff suffices",y=-2.65,size=26,color=GOOD)),run_time=.7)
            n.at(9);self.play(FadeIn(self.caption("Visualization of the real sum · certified samples use rational intervals",size=21)),run_time=.65)
        self.wipe()

    def gamma(self):
        with self.narrate("gamma") as n:
            title=self.heading("Euler’s constant supplies the next ingredient")
            self.play(FadeIn(math_label("γ = lim (H_m − ln m)",size=45,color=TRUTH).move_to([0,.8,0])),run_time=.7)
            n.at(2);self.play(FadeIn(math_label("H_m = 1 + 1/2 + 1/3 + … + 1/m",size=36,color=PRED).move_to([0,-.6,0])),run_time=.7)
            n.at(3);self.popup("lw-harmonic","An exact rational sum of reciprocals")
            n.at(4)
            self.wipe(title)
            counter=math_label("H₁ = 1",size=46,color=PRED).move_to([0,.55,0]);self.play(FadeIn(counter),run_time=.65)
            for j,text in [(1,"H₂ = 3/2"),(2,"H₃ = 11/6"),(3,"H₄ = 25/12")]:
                n.at_phrase(4,j);self.play(Transform(counter,math_label(text,size=46,color=PRED).move_to(counter)),run_time=.7)
            n.at(5)
            self.wipe(title)
            examples=VGroup(*[math_label(s,size=31,color=PRED) for s in ["H₂ − ln 2 ≈ 0.807","H₄ − ln 4 ≈ 0.697","H₈ − ln 8 ≈ 0.638"]]).arrange(DOWN,buff=.35).move_to([-2.1,.2,0]);self.play(FadeIn(examples),FadeIn(math_label("γ ≈ 0.577…",size=39,color=TRUTH).move_to([3.3,.2,0])),run_time=.9)
            n.at(7)
            self.wipe(title)
            self.play(FadeIn(math_label("H_m − ln m − 1/m ≤ γ ≤ H_m − ln m",size=38,color=TRUTH).move_to([0,.65,0])),run_time=.8)
            n.at_phrase(7,1);self.play(FadeIn(math_label("m is a positive integer",size=29,color=PRED).move_to([0,-.55,0])),run_time=.6)
            n.at(8);self.play(FadeIn(self.caption("Ideal interval width = 1/m",color=GOOD,size=29)),run_time=.65)
        self.wipe()

    def gamma_code(self):
        with self.narrate("gamma_code") as n:
            title=self.heading("Combine harmonic arithmetic with log bounds")
            popup=self.popup("lw-euler-from-log","lower = H_m − log.upper − 1/m · upper = H_m − log.lower")
            n.at(1);focus=popup.focus(1);self.play(Create(focus),run_time=.65)
            n.at(2);self.play(Transform(focus,popup.focus(2)),run_time=.65)
            n.at(4)
            self.wipe(title)
            self.play(FadeIn(math_label("gamma interval width = log interval width + 1/m",size=36,color=TRUTH).move_to([0,.7,0])),run_time=.75)
            n.at(5);self.play(FadeIn(math_label("epsilon/2 + epsilon/2 = epsilon",size=39,color=GOOD).move_to([0,-.55,0])),run_time=.7)
            n.at(6);count=self.popup("lw-euler-count","A positive count with reciprocal at most epsilon/2")
            n.at(8);bounds=self.popup("lw-euler-bounds","Choose the count; request the logarithm at half the target width")
            n.at(10);self.play(Transform(bounds.footer,T("Arithmetic validity and width are proved in the ACL2 book",size=23,color=GOOD).move_to(bounds.footer)),run_time=.65)
            n.at(11)
            self.wipe(title)
            self.play(FadeIn(self.code("(lw-euler-bounds 1)\n→ '(23099/90090 . 77153/90090)",size=31).move_to([0,.6,0])),run_time=.8)
            self.play(FadeIn(self.caption("Real-interpretation theorem: these endpoints contain γ",size=26,color=TRUTH)),run_time=.7)
        self.wipe()

    def centered(self):
        with self.narrate("centered") as n:
            title=self.heading("Center the sum to define the gap G_z")
            pieces=VGroup(math_label("S_z(x)",size=45,color=PRED),math_label("− x ln x",size=43,color=TRUTH),math_label("+ (1 + γ)x",size=43,color=GOOD)).arrange(DOWN,buff=.4).move_to([0,.2,0])
            n.at(1);self.play(FadeIn(pieces[0]),run_time=.65)
            n.at(2);self.play(FadeIn(pieces[1]),run_time=.65)
            n.at(3);self.play(FadeIn(pieces[2]),run_time=.65)
            n.at(4);self.play(FadeIn(self.caption("G_z(x) = S_z(x) − x ln x + (1 + γ)x",color=TRUTH,size=29)),run_time=.7)
            n.at(5)
            self.wipe(title)
            main=math_label("main term = x ln x − (1 + γ)x",size=40,color=TRUTH).move_to([0,.8,0]);self.play(FadeIn(main),run_time=.75)
            n.at(6);self.play(FadeIn(math_label("G_z = smoothed sum − main term",size=39,color=GOOD).move_to([0,-.6,0])),run_time=.75)
            n.at(9);self.play(FadeIn(self.caption("All three ingredients now have finite interval evaluators",size=27,color=PRED)),run_time=.7)
        self.wipe()

    def gz_code(self):
        with self.narrate("gz_code") as n:
            title=self.heading("The actual centered-signal evaluator")
            popup=self.popup("lw-gz-bounds-raw","Combine sum, log and gamma bounds using the proved interval operations",page_size=9)
            n.at(1);focus=popup.focus(2);self.play(Create(focus),run_time=.65)
            n.at(2);self.play(Transform(focus,popup.focus(4)),run_time=.65)
            n.at(3);self.play(Transform(popup.footer,T("Rational x ≥ 1 · cutoff covers x · positive primitive epsilon",size=22,color=GOOD).move_to(popup.footer)),run_time=.65)
            n.at(5)
            self.wipe(title)
            call=self.code("(lw-gz-bounds-raw 2 2 1)",size=34).move_to([0,1.25,0]);self.play(FadeIn(call),run_time=.75)
            n.at(6);self.play(FadeIn(math_label("S_z(2) = 0",size=36,color=PRED).move_to([0,.15,0])),run_time=.65)
            n.at(7)
            axis=RationalRuler(0,3,[(0,"0"),(1,"1"),(2,"2"),(3,"3")],y=-.85)
            self.play(FadeIn(axis),FadeIn(axis.band(38114/45045,229381/90090,color=GOOD)),run_time=.85)
            self.play(FadeIn(self.caption("[38114/45045, 229381/90090]",color=GOOD,size=28)),run_time=.65)
            n.at(8);self.popup("video-gz-two-positive","The lower endpoint is positive; real meaning uses the interpretation theorem",kind="defthm")
            n.at(9)
            self.wipe(title)
            self.play(FadeIn(math_label("One certified sample at x = 2",size=42,color=GOOD).move_to([0,.4,0])),run_time=.8)
        self.wipe()

    def budget(self):
        with self.narrate("budget") as n:
            title=self.heading("Turn a final width target into primitive precision")
            n.at(1);self.popup("lw-interval-width","Full width is upper endpoint minus lower endpoint")
            n.at(2)
            self.wipe(title)
            terms=VGroup(math_label("sum width ≤ count × x × epsilon",size=34,color=PRED),math_label("log correction width ≤ x × epsilon",size=34,color=TRUTH),math_label("gamma correction width ≤ x × epsilon",size=34,color=GOOD)).arrange(DOWN,buff=.55).move_to([0,.25,0]);self.play(FadeIn(terms[0]),run_time=.7)
            n.at(3);self.play(FadeIn(terms[1]),run_time=.65)
            n.at_phrase(3,1);self.play(FadeIn(terms[2]),run_time=.65)
            n.at(4);self.play(FadeIn(self.caption("total width ≤ (count + 2) × x × epsilon",size=29,color=GOOD)),run_time=.75)
            n.at(6)
            self.wipe(title)
            self.play(FadeIn(math_label("x = 9/2,  count = 9  ⇒  factor = 99/2",size=36,color=PRED).move_to([0,1,0])),run_time=.75)
            n.at(7);self.play(FadeIn(math_label("target width = 1/4",size=39,color=TRUTH).move_to([0,-.1,0])),run_time=.7)
            n.at(8);self.play(FadeIn(math_label("epsilon = target/(1 + factor) = (1/4)/(1 + 99/2) = 1/202",size=29,color=TRUTH).move_to([0,-1.2,0])),run_time=.75)
            n.at_phrase(8,1);self.play(FadeIn(math_label("width ≤ 99/404 < 1/4",size=37,color=GOOD).move_to([0,-2.3,0])),run_time=.7)
            n.at(9);self.popup("video-gz-width-budget","Proof uses the general width bound, without evaluating the endpoints",kind="defthm",page_size=12)
            n.at(11)
            self.wipe(title)
            self.play(FadeIn(math_label("A proved accuracy guarantee for a family of evaluations",size=37,color=GOOD).move_to([0,.35,0])),run_time=.8)
        self.wipe()

    def next(self):
        with self.narrate("next") as n:
            title=self.heading("The finite evaluator now has a defined job")
            steps=VGroup(*[self.chip(s,c,width=7.5) for s,c in [("recognize prime powers",PRED),("enclose the logarithmic weights",TRUTH),("add ramps and center the sum",GOOD)]]).arrange(DOWN,buff=.35).move_to([0,-.1,0])
            self.play(FadeIn(steps[0]),run_time=.65)
            n.at(2);self.play(FadeIn(steps[1]),run_time=.65)
            n.at(3);self.play(FadeIn(steps[2]),run_time=.65)
            n.at(4);self.play(FadeIn(self.caption("Arithmetic accuracy + explicit real interpretation",size=28,color=TRUTH)),run_time=.7)
            n.at(7)
            self.wipe(title)
            self.play(FadeIn(math_label("Part Five · Why a ceiling controls zeros",size=40,color=TRUTH).move_to([0,.6,0])),run_time=.8)
            n.at(9);self.play(FadeIn(self.caption("Keep the analytic hypotheses and interpretation attached",size=26,color=GOOD)),run_time=.7)
        self.wipe()
