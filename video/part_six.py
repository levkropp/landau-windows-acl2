"""Part Six: scalar kernels, finite sums, and separate error channels."""
import math
from lesson_scene import *
from lesson_source import PagedSourcePopup
from part_two import RationalRuler
from part_five import math_label


SOURCE_FILES={"exp-bounds":["lw-exp-term","lw-exp-sum","lw-exp-band","lw-exp-start-index",
    "lw-exp-initial-width","lw-exp-depth","lw-exp-index","lw-exp-bounds","lw-exp-neg-bounds"],
    "window-index":["lw-ceiling-loop","lw-ceiling-rational"],"rational-window":["lw-halving-depth"],
    "kernel-bounds":["lw-kernel-weight-scale","lw-kernel-weight-precision","lw-kernel-weight-bounds"]}
SOURCE_LOOKUP={name:".tools/acl2-part06/acl2/"+book+".lisp" for book,names in SOURCE_FILES.items() for name in names}


class LineGridPicture(VGroup):
    def __init__(self,count=4):
        super().__init__();self.count=count
        self.axes=VGroup(Line(self.point(0,0),self.point(1,0),color=DIM),Line(self.point(0,0),self.point(0,1),color=DIM))
        self.curve=Line(self.point(0,0),self.point(1,1),color=TRUTH,stroke_width=3)
        self.area=Polygon(self.point(0,0),self.point(1,0),self.point(1,1),stroke_width=0,fill_color=TRUTH,fill_opacity=.08)
        self.rectangles=VGroup(*[Polygon(self.point(j/count,0),self.point((j+1)/count,0),
            self.point((j+1)/count,j/count),self.point(j/count,j/count),stroke_color=PRED,
            stroke_width=1.5,fill_color=PRED,fill_opacity=.28) for j in range(count)])
        self.labels=VGroup(math_label("0",size=26,color=DIM).move_to(self.point(0,0)+DOWN*.32),
                          math_label("1",size=26,color=DIM).move_to(self.point(1,0)+DOWN*.32),
                          math_label("f(u) = u",size=30,color=TRUTH).move_to([-2.5,1.25,0]))
        self.add(self.area,self.axes,self.curve,self.rectangles,self.labels)

    def point(self,u,y):return np.array([-4.1+8.2*u,-1.65+2.6*y,0])


class PartSix(LessonScene):
    manifest_file="manifest-part06.json"
    timing_file="timing-part06.json"
    review_label="PART SIX · REVIEW 01"
    lesson_methods=("opening","factorial","terms","term_code","partial_sums","tail","band",
        "start","halving","precision","meaning","reciprocal","kernel","scale","kernel_precision",
        "weight_example","quadrature","grid_code","mesh","allocation","tail_cutoff","ledger","next")

    def popup(self,name,note="",kind="defun",page_size=9):
        book=".tools/acl2-part06/video/teaching-part06.lisp" if name.startswith("video-") else SOURCE_LOOKUP[name]
        popup=PagedSourcePopup(book,name,note,kind=kind,page_size=page_size)
        if popup.page_count!=1:raise ValueError(f"Unshown source pages for {name}: {popup.page_count}")
        self.play(FadeIn(popup,scale=.96),run_time=.8)
        return popup

    def opening(self):
        with self.narrate("opening") as n:
            title=self.heading("Turn the kernel into a finite rational construction")
            self.play(FadeIn(math_label("K_k(u) = uᵏ exp(−σu) / k!",size=43,color=PRED).move_to([0,.65,0])),run_time=.85)
            n.at(3)
            self.wipe(title)
            chain=VGroup(*[self.chip(text,color,width=3.5) for text,color in [("exponential band",PRED),("decaying band",TRUTH),("kernel weight",GOOD)]]).arrange(RIGHT,buff=.35).move_to([0,.5,0]);self.play(FadeIn(chain[0]),run_time=.65)
            n.at(4);self.play(LaggedStart(*[FadeIn(x) for x in chain[1:]],lag_ratio=.35),run_time=1)
            n.at(5);self.play(FadeIn(self.caption("Evaluation error + mesh error + tail error",y=-1,color=TRUTH,size=29)),run_time=.7)
            n.at(8);self.play(Transform(title,fitted(B("Part Six · Explicit kernels and error budgets",size=40)).move_to(title)),run_time=.8)
        self.wipe()

    def factorial(self):
        with self.narrate("factorial") as n:
            title=self.heading("Factorial is repeated whole-number multiplication")
            n.at(1);self.play(FadeIn(math_label("k! = 1 × 2 × … × k",size=44,color=PRED).move_to([0,1,0])),run_time=.75)
            n.at(2)
            rows=VGroup(*[math_label(text,size=34,color=TRUTH).move_to([0,.1-i*.65,0]) for i,text in enumerate(["1! = 1","2! = 1 × 2 = 2","3! = 1 × 2 × 3 = 6","4! = 1 × 2 × 3 × 4 = 24"])])
            for phrase,row in enumerate(rows):n.at_phrase(2,phrase);self.play(FadeIn(row,shift=LEFT*.2),run_time=.65)
            n.at(3)
            self.wipe(title)
            self.play(FadeIn(math_label("0! = 1",size=61,color=GOOD).move_to([0,.65,0])),run_time=.8)
            n.at(4);self.play(FadeIn(math_label("x⁰ / 0! = 1",size=41,color=TRUTH).move_to([0,-.85,0])),run_time=.75)
            n.at(6);self.play(FadeIn(self.caption("Factorials eventually dominate successive term ratios",size=27,color=PRED)),run_time=.7)
        self.wipe()

    def terms(self):
        with self.narrate("terms") as n:
            title=self.heading("Each term is a rational quotient")
            n.at(1);self.play(FadeIn(math_label("T_k(x) = xᵏ/k!",size=49,color=PRED).move_to([0,1,0])),run_time=.8)
            n.at(2);self.play(FadeIn(math_label("x ≥ 0 rational · k natural",size=29,color=DIM).move_to([0,-.1,0])),run_time=.7)
            n.at(3);self.play(FadeIn(math_label("T₀(x) = 1",size=37,color=TRUTH).move_to([0,-1.15,0])),run_time=.7)
            n.at(4);self.play(FadeIn(self.caption("next term = current term × x / new index",color=GOOD,size=28)),run_time=.75)
            n.at(5)
            self.wipe(title)
            values=VGroup(*[self.chip(text,PRED,width=1.7) for text in ["1","1","1/2","1/6","1/24"]]).arrange(RIGHT,buff=.3).move_to([0,.5,0])
            for phrase,value in enumerate(values):n.at_phrase(5,phrase);self.play(FadeIn(value,shift=LEFT*.12),run_time=.65)
            n.at(7);self.play(FadeIn(self.caption("Terms first · then a sum · then an omitted-tail bound",y=-1.1,color=TRUTH,size=29)),run_time=.7)
        self.wipe()

    def term_code(self):
        with self.narrate("term_code") as n:
            title=self.heading("The actual term evaluator uses the recurrence")
            popup=self.popup("lw-exp-term","Rational argument · natural index · nfix supplies the termination measure")
            n.at(2);focus=popup.focus(2);self.play(Create(focus),run_time=.65)
            n.at(3);self.play(Transform(focus,popup.focus(3)),run_time=.65)
            n.at(6)
            self.wipe(title)
            self.play(FadeIn(self.code("(lw-exp-term 1 3) → 1/6",size=40).move_to([0,.55,0])),run_time=.8)
            n.at(7);self.play(FadeIn(self.caption("Exact rational arithmetic",y=-.85,size=31,color=GOOD)),run_time=.7)
            n.at(8);self.play(FadeIn(self.caption("The omitted terms still need a bound",size=27,color=TRUTH)),run_time=.7)
        self.wipe()

    def partial_sums(self):
        with self.narrate("partial_sums") as n:
            title=self.heading("The stopping index counts from zero")
            n.at(1)
            value=math_label("S₀(1) = 1",size=48,color=PRED).move_to([0,.6,0]);self.play(FadeIn(value),run_time=.7)
            for phrase,text in [(1,"S₁(1) = 1 + 1 = 2"),(2,"S₂(1) = 2 + 1/2 = 5/2"),(3,"S₃(1) = 5/2 + 1/6 = 8/3")]:
                n.at_phrase(1,phrase);self.play(Transform(value,math_label(text,size=44,color=PRED).move_to(value)),run_time=.75)
            n.at(2);self.play(FadeIn(self.caption("Indices 0, 1, 2, 3: four terms",y=-.95,color=TRUTH,size=30)),run_time=.7)
            n.at(3)
            self.wipe(title)
            self.popup("lw-exp-sum","Add the current term to the preceding finite sum")
            n.at(6)
            self.wipe(title)
            self.play(FadeIn(math_label("finite sum  ≠  final real value",size=43,color=TRUTH).move_to([0,.55,0])),run_time=.8)
            n.at(8);self.play(FadeIn(self.caption("We need an upper endpoint too",y=-.85,color=GOOD,size=31)),run_time=.7)
        self.wipe()

    def tail(self):
        with self.narrate("tail") as n:
            title=self.heading("Pay for the entire omitted tail")
            self.play(FadeIn(math_label("S₃(1) = 8/3",size=42,color=PRED).move_to([0,1.05,0])),run_time=.75)
            n.at(1);self.play(FadeIn(math_label("first omitted term: T₄(1) = 1/24",size=36,color=TRUTH).move_to([0,-.1,0])),run_time=.75)
            n.at(4)
            self.wipe(title)
            bars=VGroup()
            for j in range(6):
                height=2/(2**j);x=-4.7+j*1.65
                bars.add(Rectangle(width=1.05,height=height,stroke_color=TRUTH,fill_color=TRUTH,fill_opacity=.25).move_to([x,-1.4+height/2,0]))
            self.play(LaggedStart(*[GrowFromEdge(b,DOWN) for b in bars],lag_ratio=.22),run_time=1.6)
            self.play(FadeIn(math_label("1/24 + 1/48 + 1/96 + …",size=36,color=TRUTH).move_to([0,1.5,0])),run_time=.7)
            n.at(5);self.play(FadeIn(math_label("halving tail = 2 × first term",size=34,color=GOOD).move_to([0,-2.25,0])),run_time=.7)
            n.at(6);self.play(FadeIn(self.caption("allowance = 1/12",size=31,color=GOOD)),run_time=.7)
            n.at(7)
            self.wipe(title)
            self.play(FadeIn(math_label("x ≥ 0,  n natural,  2x ≤ n + 2",size=39,color=PRED).move_to([0,.85,0])),run_time=.8)
            self.play(FadeIn(math_label("later successive ratios ≤ 1/2",size=39,color=TRUTH).move_to([0,-.65,0])),run_time=.8)
            n.at(8);self.play(FadeIn(self.caption("The ratio condition is part of the guarantee",size=28,color=GOOD)),run_time=.7)
        self.wipe()

    def band(self):
        with self.narrate("band") as n:
            title=self.heading("Finite lower sum + a paid-for tail")
            popup=self.popup("lw-exp-band","Nonnegative rational x · natural n · require 2x ≤ n+2")
            n.at(1);focus=popup.focus(1);self.play(Create(focus),run_time=.65)
            n.at(2);self.play(Transform(focus,popup.focus(2)),run_time=.65)
            n.at(3)
            self.wipe(title)
            self.play(FadeIn(math_label("lower = 8/3",size=41,color=PRED).move_to([0,1.05,0])),run_time=.7)
            n.at(4);self.play(FadeIn(math_label("upper = 8/3 + 1/12 = 11/4",size=40,color=GOOD).move_to([0,-.15,0])),run_time=.75)
            n.at(5);self.play(FadeIn(math_label("full width = 1/12",size=36,color=TRUTH).move_to([0,-1.35,0])),run_time=.7)
            n.at(6)
            self.wipe(title)
            self.popup("video-exp-band-finite-upper","Every natural later index ≥ 3 · a theorem about all later finite sums",kind="defthm",page_size=14)
        self.wipe()

    def start(self):
        with self.narrate("start") as n:
            title=self.heading("Compute a safe starting index")
            n.at(1);self.play(FadeIn(math_label("start = 1 + roundUp(2x)",size=43,color=PRED).move_to([0,.8,0])),run_time=.8)
            n.at(2);self.play(FadeIn(math_label("roundUp(12/5) = 3",size=38,color=TRUTH).move_to([0,-.55,0])),run_time=.75)
            n.at(4)
            self.wipe(title)
            self.popup("lw-ceiling-loop","nfix keeps a natural number unchanged and returns zero for anything else.")
            n.at(6)
            self.wipe(title)
            self.popup("lw-ceiling-rational","Compute sufficient fuel from the rational input")
            n.at_phrase(6,1)
            self.wipe(title)
            self.popup("lw-exp-start-index","A conservative index safely past the tail-ratio threshold")
            n.at(7)
            self.wipe(title)
            self.play(FadeIn(self.code("(lw-exp-start-index 1) → 3",size=38).move_to([0,.55,0])),run_time=.8)
            n.at(8);self.play(FadeIn(self.caption("Safe start first · more work for accuracy next",y=-.95,color=GOOD,size=29)),run_time=.7)
        self.wipe()

    def halving(self):
        with self.narrate("halving") as n:
            title=self.heading("A width request chooses the extra depth")
            self.play(FadeIn(math_label("target = 1/100",size=38,color=GOOD).move_to([0,1.15,0])),run_time=.7)
            n.at(1);allowance=math_label("initial allowance = 1/12",size=42,color=PRED).move_to([0,-.05,0]);self.play(FadeIn(allowance),run_time=.75)
            n.at(2)
            for phrase,text in enumerate(["after 1 halving: 1/24","after 2 halvings: 1/48","after 3 halvings: 1/96","after 4 halvings: 1/192"]):
                n.at_phrase(2,phrase);self.play(Transform(allowance,math_label(text,size=41,color=PRED).move_to(allowance)),run_time=.7)
            n.at(3);self.play(FadeIn(math_label("1/192 ≤ 1/100",size=37,color=GOOD).move_to([0,-1.3,0])),run_time=.7)
            n.at(4)
            self.wipe(title)
            self.popup("lw-halving-depth","Fixed width, doubled tolerance · equivalent to halving the width")
            n.at(7)
            self.wipe(title)
            self.popup("lw-exp-initial-width","Twice the first omitted term at the safe starting index")
            n.at_phrase(7,1)
            self.wipe(title)
            self.popup("lw-exp-depth","A positive rational tolerance · computed fuel, then halving depth")
        self.wipe()

    def precision(self):
        with self.narrate("precision") as n:
            title=self.heading("The requested enclosure is a finite construction")
            self.popup("lw-exp-index","Safe starting index + computed extra depth")
            n.at(1)
            self.wipe(title)
            self.popup("lw-exp-bounds","Evaluate the band at the computed stopping index")
            n.at(2)
            self.wipe(title)
            self.play(FadeIn(self.code("(lw-exp-bounds 1 1/10)\n→ '(8/3 . 11/4)",size=34).move_to([0,.95,0])),run_time=.8)
            n.at(3);self.play(FadeIn(self.code("(lw-exp-index 1 1/100) → 7",size=31).move_to([0,-.3,0])),run_time=.75)
            n.at(5);self.play(FadeIn(self.code("(lw-exp-bounds 1 1/100)\n→ '(685/252 . 54801/20160)",size=31).move_to([0,-1.6,0])),run_time=.8)
            n.at(7);self.play(FadeIn(self.caption("General guarantee: full width ≤ requested tolerance",size=26,color=GOOD)),run_time=.7)
        self.wipe()

    def meaning(self):
        with self.narrate("meaning") as n:
            title=self.heading("The arithmetic band has a proved real meaning")
            n.at(1);self.play(FadeIn(self.chip("all later finite partial sums lie in [L, R]",PRED,width=11).move_to([0,1.15,0])),run_time=.85)
            n.at(2);self.play(FadeIn(self.chip("the real exponential lies in [L, R]",GOOD,width=11).move_to([0,-.35,0])),run_time=.85)
            n.at(3)
            self.wipe(title)
            axis=RationalRuler(2.65,2.77,[(8/3,"8/3"),(11/4,"11/4")],y=-.35);self.play(FadeIn(axis),FadeIn(axis.band(8/3,11/4,color=PRED)),run_time=.85)
            dot=Dot(axis.point(8/3)+UP*.17,color=TRUTH,radius=.07);self.play(FadeIn(dot),run_time=.5)
            for value in [65/24,163/60,685/252]:self.play(dot.animate.move_to(axis.point(value)+UP*.17),run_time=.65)
            n.at(4);self.play(FadeIn(math_label("L ≤ each later sum ≤ R  ⇒  L ≤ limit ≤ R",size=34,color=GOOD).move_to([0,1.15,0])),run_time=.8)
            n.at(5);self.play(FadeIn(self.caption("ExpBounds.lean · computedExpBounds_sound",y=-1.55,size=25,color=PRED)),run_time=.7)
            n.at(8);self.play(FadeIn(self.caption("The certificate uses rational endpoints and proved inequalities",size=25,color=GOOD)),run_time=.7)
        self.wipe()

    def reciprocal(self):
        with self.narrate("reciprocal") as n:
            title=self.heading("Reciprocals reverse the endpoint order")
            n.at(1);self.play(FadeIn(math_label("exp(−x) = 1 / exp(x)",size=46,color=TRUTH).move_to([0,1.1,0])),run_time=.8)
            n.at(2);self.play(FadeIn(math_label("1 ≤ L ≤ exp(x) ≤ R",size=39,color=PRED).move_to([0,-.05,0])),run_time=.75)
            n.at(3);self.play(FadeIn(math_label("1/R ≤ exp(−x) ≤ 1/L",size=42,color=GOOD).move_to([0,-1.3,0])),run_time=.8)
            n.at(5)
            self.wipe(title)
            positive=VGroup(self.chip("L = 8/3",PRED,width=3),self.chip("R = 11/4",PRED,width=3)).arrange(RIGHT,buff=3).move_to([0,1.15,0])
            negative=VGroup(self.chip("1/R = 4/11",GOOD,width=3),self.chip("1/L = 3/8",GOOD,width=3)).arrange(RIGHT,buff=3).move_to([0,-1.05,0])
            self.play(FadeIn(positive),run_time=.65)
            self.play(Create(Arrow(positive[0].get_bottom(),negative[1].get_top(),buff=.12,color=TRUTH)),Create(Arrow(positive[1].get_bottom(),negative[0].get_top(),buff=.12,color=TRUTH)),FadeIn(negative),run_time=1)
            n.at(6)
            self.wipe(title)
            self.popup("lw-exp-neg-bounds","Positive input x ≥ 0 · swap the reciprocal endpoints")
            n.at(8)
            self.wipe(title)
            self.play(FadeIn(math_label("width([1/R, 1/L]) ≤ R − L",size=41,color=GOOD).move_to([0,.65,0])),run_time=.8)
            self.play(FadeIn(self.caption("For 1 ≤ L ≤ R · positive endpoints at most 1",y=-.9,color=TRUTH,size=29)),run_time=.7)
        self.wipe()

    def kernel(self):
        with self.narrate("kernel") as n:
            title=self.heading("The kernel retains its factorial normalization")
            n.at(1);self.play(FadeIn(math_label("K_k(u) = [uᵏ/k!] × exp(−σu)",size=43,color=PRED).move_to([0,.75,0])),run_time=.8)
            n.at(2);self.play(FadeIn(math_label("u ≥ 0, σ ≥ 0 rational · k natural",size=29,color=DIM).move_to([0,-.35,0])),run_time=.7)
            n.at(3);self.play(FadeIn(math_label("uᵏ/k! = T_k(u)",size=37,color=TRUTH).move_to([0,-1.45,0])),run_time=.75)
            n.at(5)
            self.wipe(title)
            def point(u):return np.array([-5+u*10/3,-1.55+80*(u*u/2)*math.exp(-3*u),0])
            curve=polyline([point(u) for u in np.linspace(0,3,170)],color=PRED,width=4)
            self.play(Create(Line([-5,-1.55,0],[5,-1.55,0],color=DIM)),Create(curve),FadeIn(math_label("K₂(u) = (u²/2) exp(−3u)",size=34,color=TRUTH).move_to([0,1.45,0])),run_time=1)
            self.play(FadeIn(self.caption("Illustrative curve · actual factorial normalization retained",y=-2.55,size=25)),run_time=.7)
            n.at(6)
            self.wipe(title)
            self.play(FadeIn(math_label("cell weight = h × K_k(u)",size=46,color=GOOD).move_to([0,.65,0])),run_time=.8)
            n.at(7);self.play(FadeIn(math_label("h ≥ 0  ⇒  weight ≥ 0",size=36,color=GOOD).move_to([0,-.65,0])),run_time=.7)
            n.at(8);self.play(FadeIn(self.caption("The signal multiplying this weight may have either sign",size=27,color=TRUTH)),run_time=.7)
        self.wipe()

    def scale(self):
        with self.narrate("scale") as n:
            title=self.heading("Separate the exact scale from the damping enclosure")
            n.at(1);self.play(FadeIn(math_label("scale = h × T_k(u)",size=44,color=PRED).move_to([0,.9,0])),run_time=.8)
            n.at(2);self.play(FadeIn(math_label("weight = scale × exp(−σu)",size=40,color=TRUTH).move_to([0,-.55,0])),run_time=.8)
            n.at(3)
            self.wipe(title)
            self.popup("lw-kernel-weight-scale","Exact nonnegative rational factor · cell width times the term")
            n.at(4)
            self.wipe(title)
            self.play(FadeIn(math_label("u = 1/3,  σ = 3,  k = 2,  h = 1/2",size=37,color=PRED).move_to([0,1.2,0])),run_time=.8)
            n.at(5);self.play(FadeIn(math_label("T₂(1/3) = (1/3)²/2 = 1/18",size=35,color=TRUTH).move_to([0,.15,0])),run_time=.75)
            self.play(FadeIn(math_label("scale = (1/2)(1/18) = 1/36",size=35,color=GOOD).move_to([0,-.9,0])),run_time=.75)
            n.at(7);self.play(FadeIn(self.caption("weight = exp(−1)/36",size=34,color=TRUTH)),run_time=.7)
        self.wipe()

    def kernel_precision(self):
        with self.narrate("kernel_precision") as n:
            title=self.heading("Choose the primitive tolerance after the scale")
            self.play(FadeIn(math_label("scaled width = scale × primitive width",size=37,color=PRED).move_to([0,.85,0])),run_time=.8)
            n.at(1);self.play(FadeIn(math_label("δ = requested error / (1 + scale)",size=39,color=TRUTH).move_to([0,-.55,0])),run_time=.8)
            n.at(2)
            self.wipe(title)
            self.popup("lw-kernel-weight-precision","Positive requested error · scale ≥ 0 makes the divisor positive")
            n.at(4)
            self.wipe(title)
            self.play(FadeIn(math_label("scale × δ = error × scale/(1 + scale) ≤ error",size=34,color=GOOD).move_to([0,.55,0])),run_time=.85)
            n.at(5)
            self.wipe(title)
            self.popup("lw-kernel-weight-bounds","Compute the decay band, then scale both endpoints",page_size=12)
            n.at(7);self.play(FadeIn(self.caption("kernel-bounds.lisp · full-width guarantee includes the scale",size=22,color=GOOD).move_to([0,-3.65,0])),run_time=.7)
        self.wipe()

    def weight_example(self):
        with self.narrate("weight_example") as n:
            title=self.heading("One fully computed weight, at two precisions")
            self.play(FadeIn(self.code("(lw-kernel-weight-bounds 1/3 3 2 1/2 1/10)",size=28).move_to([0,1.25,0])),run_time=.8)
            n.at(1);self.play(FadeIn(math_label("[1/99, 1/96]",size=49,color=GOOD).move_to([0,.15,0])),run_time=.75)
            n.at(2);self.play(FadeIn(math_label("1/99 ≤ exp(−1)/36 ≤ 1/96",size=36,color=TRUTH).move_to([0,-1,0])),run_time=.8)
            n.at(3);self.play(FadeIn(self.caption("full width = 1/3168 < 1/10",size=29,color=GOOD)),run_time=.7)
            n.at(4)
            self.wipe(title)
            self.play(FadeIn(self.code("(lw-kernel-weight-bounds 1/3 3 2 1/2 1/100)\n→ '(560/54801 . 7/685)",size=28).move_to([0,.75,0])),run_time=.9)
            n.at(6);self.play(FadeIn(self.caption("KernelBounds.lean · kernelWeightBounds_sound",y=-.85,size=26,color=PRED)),run_time=.7)
            n.at(7);self.play(FadeIn(self.caption("A scalar weight is now a checked construction",size=28,color=GOOD)),run_time=.7)
        self.wipe()

    def quadrature(self):
        with self.narrate("quadrature") as n:
            title=self.heading("An exact finite sum still has a grid error")
            n.at(1);picture=LineGridPicture(4);self.play(FadeIn(picture.area),Create(picture.axes),Create(picture.curve),FadeIn(picture.labels),run_time=1)
            n.at(2);self.play(FadeIn(math_label("area = 1/2",size=35,color=TRUTH).move_to([3,1.3,0])),run_time=.7)
            n.at(3);self.play(LaggedStart(*[FadeIn(r) for r in picture.rectangles],lag_ratio=.22),run_time=1.3)
            n.at(6);self.play(FadeIn(self.caption("(1/4) × (0 + 1/4 + 1/2 + 3/4) = 3/8",y=-2.6,size=27,color=PRED)),run_time=.8)
            n.at(7);self.play(FadeIn(self.caption("1/2 − 3/8 = 1/8",y=-3.35,size=28,color=GAPC)),run_time=.75)
            n.at(9);self.play(Transform(title,fitted(B("Exact arithmetic and exact integration are different jobs",size=38)).move_to(title)),run_time=.8)
        self.wipe()

    def grid_code(self):
        with self.narrate("grid_code") as n:
            title=self.heading("Check the finite line-grid example")
            popup=self.popup("video-line-grid","Teaching model f(u)=u · start, step and natural count")
            n.at(2);focus=popup.focus(3);self.play(Create(focus),run_time=.65)
            n.at(3)
            self.wipe(title)
            self.play(FadeIn(self.code("(video-line-grid 0 1/4 4) → 3/8",size=33).move_to([0,1,0])),run_time=.8)
            n.at(4);self.play(FadeIn(self.code("(video-line-grid 0 1/8 8) → 7/16",size=33).move_to([0,-.2,0])),run_time=.8)
            n.at(5);self.play(FadeIn(math_label("deficits from 1/2:   1/8   and   1/16",size=35,color=TRUTH).move_to([0,-1.45,0])),run_time=.75)
            n.at(6)
            self.wipe(title)
            self.popup("video-line-grid-formula","General rational start and step · natural count",kind="defthm",page_size=14)
        self.wipe()

    def mesh(self):
        with self.narrate("mesh") as n:
            title=self.heading("Bound variation between the sampled addresses")
            n.at(1);self.play(FadeIn(math_label("value change ≤ L × distance moved",size=40,color=PRED).move_to([0,1,0])),run_time=.8)
            n.at(2);self.play(FadeIn(math_label("one cell: variation ≤ Lh",size=40,color=TRUTH).move_to([0,-.2,0])),run_time=.8)
            n.at(3);self.play(FadeIn(math_label("cell area error ≤ Lh²",size=39,color=GOOD).move_to([0,-1.4,0])),run_time=.8)
            n.at(4)
            self.wipe(title)
            self.play(FadeIn(math_label("total mesh error ≤ L × interval length × h",size=36,color=GOOD).move_to([0,.9,0])),run_time=.85)
            n.at(5);diagram=LineGridPicture(4);diagram.scale(.55).move_to([0,-1.2,0]);self.play(FadeIn(diagram),run_time=.85)
            finer=LineGridPicture(8);finer.scale(.55).move_to(diagram);self.play(Transform(diagram,finer),run_time=1)
            n.at(6)
            self.wipe(title)
            self.play(FadeIn(math_label("f(u)=u on [0,1]:  L=1,  h=1/4",size=36,color=PRED).move_to([0,1,0])),run_time=.8)
            n.at(7);self.play(FadeIn(math_label("general bound = 1/4     actual deficit = 1/8",size=35,color=TRUTH).move_to([0,-.35,0])),run_time=.8)
            n.at(9);self.play(FadeIn(self.caption("Prove the variation bound for the full integrand",size=28,color=GOOD)),run_time=.7)
        self.wipe()

    def allocation(self):
        with self.narrate("allocation") as n:
            title=self.heading("Budget the error of each cell contribution")
            n.at(1);self.play(FadeIn(math_label("N cells · error per contribution ≤ δ",size=39,color=PRED).move_to([0,1,0])),run_time=.8)
            n.at(2);self.play(FadeIn(math_label("total finite evaluation error ≤ Nδ",size=39,color=GOOD).move_to([0,-.25,0])),run_time=.8)
            n.at(4);self.play(FadeIn(math_label("δ = evaluation budget / (N+1)",size=37,color=TRUTH).move_to([0,-1.5,0])),run_time=.8)
            n.at(5)
            self.wipe(title)
            cells=VGroup(*[self.chip("1/500",PRED if j<4 else DIM,width=1.9) for j in range(5)]).arrange(RIGHT,buff=.25).move_to([0,.6,0]);self.play(LaggedStart(*[FadeIn(c) for c in cells],lag_ratio=.15),run_time=1.2)
            self.play(FadeIn(T("four cell allowances + one reserve",size=28,color=TRUTH).move_to([0,-.5,0])),run_time=.65)
            n.at(6);self.play(FadeIn(math_label("4/500 < 1/100",size=38,color=GOOD).move_to([0,-1.65,0])),run_time=.7)
            n.at(7)
            self.wipe(title)
            self.popup("video-cell-tolerance","Teaching allocation · error already includes each cell's weight")
            n.at(8)
            self.wipe(title)
            self.popup("video-cell-budget","Natural count · positive rational budget",kind="defthm",page_size=16)
        self.wipe()

    def tail_cutoff(self):
        with self.narrate("tail_cutoff") as n:
            title=self.heading("A finite cutoff must pay for the discarded tail")
            def point(u):return np.array([-5+u,-1.5+2.5*math.exp(-u),0])
            axis=Line([-5,-1.5,0],[5.2,-1.5,0],color=DIM);curve=polyline([point(u) for u in np.linspace(0,10,170)],color=PRED,width=4)
            self.play(Create(axis),Create(curve),run_time=1)
            n.at(2);self.play(FadeIn(T("Model integrand: exp(−u)",size=30,color=PRED).move_to([1,1.15,0])),run_time=.75)
            cutoff=Line([-3,-1.5,0],[-3,.7,0],color=TRUTH);self.play(Create(cutoff),run_time=.65)
            n.at(3)
            integral=math_label("∫",size=53,color=TRUTH)
            lower=math_label("T",size=20,color=TRUTH).next_to(integral,DOWN,buff=-.04).shift(RIGHT*.08)
            upper=math_label("∞",size=20,color=TRUTH).next_to(integral,UP,buff=-.04).shift(RIGHT*.12)
            body=math_label("exp(−u) du = exp(−T)",size=33,color=TRUTH).next_to(integral,RIGHT,buff=.22)
            equation=VGroup(integral,lower,upper,body).move_to([0,-2.35,0])
            self.play(FadeIn(equation),run_time=.8)
            n.at(5);self.play(cutoff.animate.shift(RIGHT*6),run_time=1)
            self.play(FadeIn(math_label("T = 8:  computed upper endpoint ≤ 1/1000",size=31,color=GOOD).move_to([0,-3.3,0])),run_time=.75)
            n.at(6)
            self.wipe(title)
            self.popup("video-decay-tail-sample","Model exp(−u) tail · real area meaning uses the exponential interpretation",kind="defthm",page_size=10)
            n.at(7)
            self.wipe(title)
            self.play(FadeIn(math_label("Actual signal growth: |g(u)| ≤ A exp(2u)",size=35,color=PRED).move_to([0,1.05,0])),run_time=.8)
            n.at(8);self.play(FadeIn(math_label("|g(u)| K_k(u) ≤ A [uᵏ/k!] exp(−(σ−2)u)",size=33,color=TRUTH).move_to([0,-.3,0])),run_time=.85)
            self.play(FadeIn(self.caption("u ≥ 0, σ > 2 · include the signal, power and damping in tail estimates",size=23,color=GOOD)),run_time=.7)
        self.wipe()

    def ledger(self):
        with self.narrate("ledger") as n:
            title=self.heading("Different error channels need different controls")
            rows=VGroup(*[self.chip(text,color,width=10.7) for text,color in [("finite evaluation → tighter primitive enclosures",PRED),("mesh variation → smaller cells",TRUTH),("discarded tail → justified farther cutoff",HYPO)]]).arrange(DOWN,buff=.35).move_to([0,-.1,0])
            self.play(FadeIn(rows[0]),run_time=.7)
            n.at(2);self.play(FadeIn(rows[1]),run_time=.7)
            n.at(3);self.play(FadeIn(rows[2]),run_time=.7)
            n.at(5)
            self.wipe(title)
            self.play(FadeIn(math_label("|error₁|, |error₂|, |error₃| ≤ 1/1000",size=37,color=PRED).move_to([0,1,0])),run_time=.8)
            n.at(6);self.play(FadeIn(math_label("|total error| ≤ 3/1000 < 1/100",size=42,color=GOOD).move_to([0,-.4,0])),run_time=.85)
            n.at(7)
            self.wipe(title)
            self.popup("video-error-ledger","A checked conditional implication · establish every input error bound",kind="defthm",page_size=14)
        self.wipe()

    def next(self):
        with self.narrate("next") as n:
            title=self.heading("Scalar weights now have explicit error budgets")
            steps=VGroup(*[self.chip(text,color,width=8) for text,color in [("finite exponential enclosures",PRED),("a composed scalar kernel weight",GOOD),("separate sum, mesh and tail budgets",TRUTH)]]).arrange(DOWN,buff=.35).move_to([0,.05,0])
            self.play(FadeIn(steps[0]),run_time=.7)
            n.at(1);self.play(FadeIn(steps[1:]),run_time=.9)
            n.at(3);self.play(FadeIn(self.caption("Full reduction and Peano Arithmetic interpretation require composition",size=23,color=DIM)),run_time=.7)
            n.at(4)
            self.wipe(title)
            self.play(FadeIn(math_label("Part Seven · Complex phases and oscillating samples",size=36,color=TRUTH).move_to([0,.65,0])),run_time=.85)
            n.at(7);self.play(FadeIn(self.caption("Explicit constructions with justified error budgets",y=-.85,size=29,color=GOOD)),run_time=.7)
        self.wipe()
