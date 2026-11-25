"""Part Seven: rational phases and the actual finite Mellin constructors."""
import math
import textwrap
from fractions import Fraction
from lesson_scene import *
from lesson_source import PagedSourcePopup
from function_popup import read_form
from part_two import RationalRuler
from part_five import math_label


SOURCE_FILES={
 "complex-bounds":["lw-complexp","lw-complex-add","lw-complex-sub","lw-complex-scale","lw-complex-mul","lw-complex-diskp","lw-complex-power"],
 "mellin-sums":["lw-diskp"],
 "phase-bounds":["lw-phase-denominator","lw-phase-rotation","lw-phase-grid","lw-phase-steps","lw-phase-value"],
 "log-signal":["lw-log-signal-cap","lw-log-signal-lipschitz","lw-log-signal-budget","lw-log-signal-delta","lw-log-signal-point","lw-log-signal-margin","lw-log-signal-base","lw-log-signal-bounds"],
 "mellin-integrand":["lw-mellin-signal-cap","lw-mellin-kernel-cap","lw-mellin-component-error","lw-mellin-signal-error","lw-mellin-kernel-error","lw-mellin-phase-error","lw-mellin-signal","lw-mellin-weight","lw-mellin-phase","lw-mellin-sample","lw-mellin-sample-check"],
 "mellin-quadrature":["lw-mellin-cellsp","lw-mellin-sum-raw","lw-mellin-sum-error","lw-mellin-sum"]}
SOURCE_LOOKUP={name:".tools/acl2-part07/acl2/"+book+".lisp" for book,names in SOURCE_FILES.items() for name in names}


class SourceGroup(VGroup):
    def __init__(self,names,title,note):
        super().__init__()
        self.forms=[read_form(SOURCE_LOOKUP[name],"defun",name) for name in names]
        lines=[]
        for form in self.forms:
            if lines:lines.append("")
            for line in form.splitlines():
                indent=len(line)-len(line.lstrip())
                lines.extend(textwrap.wrap(line,width=72,subsequent_indent=" "*(indent+2),
                    break_long_words=False,break_on_hyphens=False,replace_whitespace=False) or [""])
        if len(lines)>17:raise ValueError(f"Split this source group for readability: {names}, {len(lines)} lines")
        background=card(12.5,6.65,stroke=PRED)
        heading=fitted(T("ACL2 definitions · "+title,size=26,color=TRUTH),11.6).move_to([0,2.2,0])
        self.body=fitted(T("\n".join(lines),size=29,font="Consolas"),11.3)
        if self.body.height>3.45:self.body.scale_to_fit_height(3.45)
        self.body.move_to([0,-.1,0])
        footer=fitted(T(note,size=22,color=DIM),11.4).move_to([0,-2.55,0])
        tag=T("Complete source · certified project snapshots",size=17,color=DIM).move_to([0,-3,0])
        self.add(background,heading,self.body,footer,tag)


class PhasePlane(VGroup):
    def __init__(self,center=(-2.8,-.35,0),unit=1.65,circle=False):
        super().__init__();self.center=np.array(center,dtype=float);self.unit=unit
        self.axes=VGroup(Line(self.point(-1.35,0),self.point(1.35,0),color=DIM),
                         Line(self.point(0,-1.35),self.point(0,1.35),color=DIM))
        self.labels=VGroup(math_label("1",size=22,color=DIM).move_to(self.point(1,0)+DOWN*.27),
                          math_label("i",size=25,color=DIM).move_to(self.point(0,1)+LEFT*.25))
        self.add(self.axes,self.labels)
        if circle:self.add(Circle(radius=unit,color=FAINT,stroke_width=2).move_to(self.center))

    def point(self,x,y):return self.center+RIGHT*float(x)*self.unit+UP*float(y)*self.unit
    def arrow(self,x,y,color=PRED):return Arrow(self.center,self.point(x,y),buff=0,color=color,stroke_width=4)


def rational_phase(angle,steps):
    value=Fraction(angle)/steps
    denominator=4+value*value
    real,imag=(4-value*value)/denominator,4*value/denominator
    x,y=Fraction(1),Fraction(0)
    for _ in range(steps):x,y=x*real-y*imag,x*imag+y*real
    return float(x),float(y)


class PartSeven(LessonScene):
    manifest_file="manifest-part07.json"
    timing_file="timing-part07.json"
    review_label="PART SEVEN · REVIEW 01"
    lesson_methods=("opening","pairs","linear","multiplication","disks","phase","rotation","powers",
        "grid","phase_precision","phase_meaning","height","signal","caps","product","budget",
        "components","sample","checks","cells","finite_sum","sum_budget","one_sided","interpretation","scope","next")

    def sources(self,names,title,note=""):
        panel=SourceGroup(names,title,note);self.play(FadeIn(panel,scale=.96),run_time=.8);return panel

    def popup(self,name,note="",kind="defun",page_size=10):
        book=".tools/acl2-part07/video/teaching-part07.lisp" if name.startswith("video-") else SOURCE_LOOKUP[name]
        panel=PagedSourcePopup(book,name,note,kind=kind,page_size=page_size)
        self.play(FadeIn(panel,scale=.96),run_time=.8)
        return panel

    def opening(self):
        with self.narrate("opening") as n:
            title=self.heading("Complete the oscillating weighted reading")
            self.play(FadeIn(self.chip("scalar kernel weight",PRED,width=6).move_to([0,.7,0])),run_time=.7)
            n.at(1);self.play(FadeIn(math_label("× complex phase",size=40,color=TRUTH).move_to([0,-.55,0])),run_time=.75)
            n.at(2)
            self.wipe(title)
            pipeline=VGroup(*[self.chip(text,color,width=3.5) for text,color in [("signal",PRED),("weight",GOOD),("phase",TRUTH)]]).arrange(RIGHT,buff=.35).move_to([0,.65,0]);self.play(FadeIn(pipeline),run_time=.9)
            n.at(5);self.play(FadeIn(self.caption("Explicit product precision → explicit finite-sum precision",y=-1,color=GOOD,size=28)),run_time=.75)
            n.at(7);self.play(Transform(title,fitted(B("Part Seven · Complex phases and oscillating samples",size=38)).move_to(title)),run_time=.8)
        self.wipe()

    def pairs(self):
        with self.narrate("pairs") as n:
            title=self.heading("A rational complex point stores two coordinates")
            plane=PhasePlane();self.play(FadeIn(plane),run_time=.8)
            n.at(2);point=Dot(plane.point(3/5,4/5),color=PRED,radius=.085);self.play(FadeIn(point),Create(plane.arrow(3/5,4/5)),run_time=.85)
            self.play(FadeIn(math_label("3/5 + (4/5)i",size=36,color=PRED).move_to([3,.7,0])),run_time=.7)
            n.at(3);self.play(FadeIn(self.code("'(3/5 . 4/5)",size=35).move_to([3,-.5,0])),run_time=.7)
            n.at(4);self.play(FadeIn(self.caption("first: real coordinate · second: imaginary coordinate",size=26,color=TRUTH)),run_time=.7)
            n.at(5)
            self.wipe(title)
            self.sources(["lw-complexp"],"rational complex points","A dotted pair of rational coordinates")
            n.at(7)
            self.wipe(title)
            pair=VGroup(self.chip("interval endpoints [L,R]",GOOD,width=5.4),self.chip("complex coordinates (x,y)",PRED,width=5.4)).arrange(RIGHT,buff=.5).move_to([0,.4,0]);self.play(FadeIn(pair),run_time=.9)
            n.at(8);self.play(FadeIn(self.caption("Same storage shape · different mathematical meanings",y=-1,color=TRUTH,size=29)),run_time=.7)
        self.wipe()

    def linear(self):
        with self.narrate("linear") as n:
            title=self.heading("Add, subtract and scale coordinates")
            self.play(FadeIn(math_label("(x,y) + (u,v) = (x+u, y+v)",size=38,color=PRED).move_to([0,1,0])),run_time=.8)
            n.at(1);self.play(FadeIn(math_label("scale c:  (x,y) → (cx,cy)",size=39,color=TRUTH).move_to([0,-.15,0])),run_time=.8)
            n.at(2);self.play(FadeIn(math_label("(x,y) − (u,v) = (x−u,y−v)",size=37,color=GOOD).move_to([0,-1.3,0])),run_time=.8)
            n.at(3)
            self.wipe(title)
            self.sources(["lw-complex-add","lw-complex-scale","lw-complex-sub"],"coordinate operations","Every output coordinate is rational")
            n.at(5)
            self.wipe(title)
            plane=PhasePlane(circle=True);arrow=plane.arrow(.3,.4);self.play(FadeIn(plane),GrowArrow(arrow),run_time=.85)
            label=math_label("(3/10, 2/5)",size=35,color=PRED).move_to([3,.65,0]);self.play(FadeIn(label),run_time=.65)
            n.at(6);self.play(Transform(arrow,plane.arrow(.6,.8,color=TRUTH)),Transform(label,math_label("×2 → (3/5, 4/5)",size=34,color=TRUTH).move_to(label)),run_time=.9)
            self.play(Transform(arrow,plane.arrow(-.6,-.8,color=HYPO)),FadeIn(math_label("×(−1): reverse direction",size=31,color=HYPO).move_to([3,-.65,0])),run_time=1)
        self.wipe()

    def multiplication(self):
        with self.narrate("multiplication") as n:
            title=self.heading("Complex multiplication can turn a vector")
            self.play(FadeIn(math_label("i² = −1",size=40,color=TRUTH).move_to([0,1.15,0])),run_time=.7)
            n.at(1);self.play(FadeIn(math_label("real part = xu − yv",size=36,color=PRED).move_to([0,-.05,0])),run_time=.75)
            n.at(2);self.play(FadeIn(math_label("imaginary part = xv + yu",size=36,color=GOOD).move_to([0,-1.2,0])),run_time=.75)
            n.at(3)
            self.wipe(title)
            self.sources(["lw-complex-mul"],"multiply two rational complex points","Inputs: left=(x,y), right=(u,v)")
            n.at(4)
            self.wipe(title)
            plane=PhasePlane(circle=True);arrow=plane.arrow(.6,.8);self.play(FadeIn(plane),GrowArrow(arrow),run_time=.85)
            n.at(5);self.play(Rotate(arrow,angle=PI/2,about_point=plane.center),FadeIn(math_label("(3/5,4/5) × i = (−4/5,3/5)",size=27,color=TRUTH).move_to([3,.6,0])),run_time=1.2)
            n.at(7)
            self.wipe(title)
            plane=PhasePlane(circle=True);arrow=plane.arrow(1,0,color=TRUTH);self.play(FadeIn(plane),GrowArrow(arrow),run_time=.65)
            for _ in range(4):self.play(Rotate(arrow,angle=PI/2,about_point=plane.center),run_time=.55)
            self.play(FadeIn(math_label("i⁴ = 1",size=43,color=GOOD).move_to([3,.3,0])),run_time=.6)
            n.at(8)
            self.wipe(title)
            self.sources(["lw-complex-power"],"finite repeated multiplication","Natural index · base case is the complex point (1,0)")
        self.wipe()

    def disks(self):
        with self.narrate("disks") as n:
            title=self.heading("Check a disk with squared rational inequalities")
            n.at(1);self.play(FadeIn(math_label("x² + y² ≤ r²,  r ≥ 0",size=47,color=GOOD).move_to([0,.65,0])),run_time=.8)
            n.at(2)
            self.wipe(title)
            self.sources(["lw-diskp","lw-complex-diskp"],"disk membership","No square-root evaluator is used")
            n.at(3)
            self.wipe(title)
            plane=PhasePlane(circle=True);self.play(FadeIn(plane),FadeIn(Dot(plane.point(.6,.8),color=GOOD,radius=.09)),run_time=.85)
            self.play(FadeIn(math_label("(3/5)² + (4/5)² = 1",size=30,color=GOOD).move_to([3,.9,0])),run_time=.75)
            n.at(4);self.play(FadeIn(Dot(plane.point(1,1),color=GAPC,radius=.09)),FadeIn(math_label("1² + 1² = 2 > 1",size=31,color=GAPC).move_to([3,-.3,0])),run_time=.8)
            n.at(6);self.play(FadeIn(self.caption("Error disk around z₀: test the difference z − z₀",size=27,color=TRUTH)),run_time=.7)
        self.wipe()

    def phase(self):
        with self.narrate("phase") as n:
            title=self.heading("A phase is a unit-length direction")
            plane=PhasePlane(circle=True);arrow=plane.arrow(1,0);self.play(FadeIn(plane),GrowArrow(arrow),run_time=.9)
            n.at(1);self.play(FadeIn(math_label("exp(i t) = cos t + i sin t",size=32,color=TRUTH).move_to([3,.85,0])),run_time=.8)
            n.at(2);arc=Arc(radius=plane.unit,start_angle=0,angle=1,color=TRUTH,arc_center=plane.center)
            self.play(Rotate(arrow,angle=1,about_point=plane.center),Create(arc),run_time=1.3)
            label=math_label("t = 1 radian",size=30,color=TRUTH).move_to([3,-.25,0]);self.play(FadeIn(label),run_time=.65)
            n.at(3);self.play(Rotate(arrow,angle=-2,about_point=plane.center),FadeOut(arc),Transform(label,math_label("t = −1 radian",size=30,color=HYPO).move_to(label)),run_time=1.2)
            n.at(4);self.play(FadeIn(math_label("length = 1",size=34,color=GOOD).move_to([3,-1.45,0])),run_time=.7)
            n.at(7);self.play(FadeIn(self.caption("Exact unit length and correct direction are separate requirements",size=24,color=PRED)),run_time=.7)
        self.wipe()

    def rotation(self):
        with self.narrate("rotation") as n:
            title=self.heading("A rational rotation preserves the unit circle")
            n.at(1);self.play(FadeIn(math_label("denominator D = 4 + t² > 0",size=39,color=PRED).move_to([0,1.1,0])),run_time=.8)
            n.at(2);self.play(FadeIn(math_label("R(t) = ((4−t²)/D, 4t/D)",size=41,color=TRUTH).move_to([0,-.1,0])),run_time=.8)
            n.at(4);self.play(FadeIn(math_label("(4−t²)² + (4t)² = (4+t²)²",size=35,color=GOOD).move_to([0,-1.4,0])),run_time=.8)
            n.at(6)
            self.wipe(title)
            self.play(FadeIn(math_label("R(1) = (3/5,4/5)",size=47,color=GOOD).move_to([0,.65,0])),run_time=.8)
            n.at(7);self.play(FadeIn(self.caption("R(1) is not exactly exp(i) · refinement corrects the angle",y=-.85,size=27,color=TRUTH)),run_time=.75)
            n.at(9)
            self.wipe(title)
            self.sources(["lw-phase-denominator","lw-phase-rotation"],"the rational rotation","Rational input · a strictly positive denominator")
        self.wipe()

    def powers(self):
        with self.narrate("powers") as n:
            title=self.heading("Repeat small rational rotations")
            n.at(1);self.play(FadeIn(M("P<sub>N</sub>(t) = R(t/N)<sup>N</sup>",size=47,color=PRED).move_to([0,.8,0])),run_time=.8)
            n.at(2);self.play(FadeIn(math_label("each step and its finite power have length 1",size=32,color=GOOD).move_to([0,-.55,0])),run_time=.75)
            n.at(4)
            self.wipe(title)
            self.play(FadeIn(math_label("t=1, N=2:  R(1/2) = (15/17, 8/17)",size=36,color=PRED).move_to([0,1.1,0])),run_time=.8)
            n.at(5);self.play(FadeIn(math_label("R(1/2)² = (161/289, 240/289)",size=39,color=TRUTH).move_to([0,-.15,0])),run_time=.85)
            n.at(6);self.play(FadeIn(self.caption("Exact rational coordinates · direction still approximate",y=-1.65,color=GOOD,size=28)),run_time=.75)
        self.wipe()

    def grid(self):
        with self.narrate("grid") as n:
            title=self.heading("Refine the direction, and prove its error bound")
            self.sources(["lw-phase-grid"],"the finite phase grid","Rational angle · positive natural step count")
            n.at(2)
            self.wipe(title)
            axis=RationalRuler(.9,1.005,[(.9,"0.9"),(.95,"0.95"),(1,"1")],y=-.1)
            target=Dot(axis.point(1),color=TRUTH,radius=.09);self.play(FadeIn(axis),FadeIn(target),run_time=.85)
            self.play(FadeIn(T("Magnified angle view · target = 1 radian",size=27,color=TRUTH).move_to([0,1.1,0])),run_time=.7)
            n.at(3);dot=Dot(axis.point(2*math.atan(.5)),color=PRED,radius=.075);label=math_label("N = 1",size=31,color=PRED).move_to([0,-1.3,0]);self.play(FadeIn(dot),FadeIn(label),run_time=.7)
            n.at(4);self.play(dot.animate.move_to(axis.point(4*math.atan(.25))),Transform(label,math_label("N = 2",size=31,color=PRED).move_to(label)),run_time=.9)
            n.at_phrase(4,1);self.play(dot.animate.move_to(axis.point(8*math.atan(.125))),Transform(label,math_label("N = 4",size=31,color=PRED).move_to(label)),run_time=.9)
            n.at(6)
            self.wipe(title)
            self.play(FadeIn(math_label("N > 0,  |t| ≤ N",size=36,color=PRED).move_to([0,1,0])),run_time=.75)
            self.play(FadeIn(math_label("distance(P_N(t), exp(i t)) ≤ 2t²/N",size=39,color=GOOD).move_to([0,-.2,0])),run_time=.85)
            n.at(7);self.play(FadeIn(self.caption("Conservative distance bound · the angle drawing is illustrative",y=-1.6,size=26,color=TRUTH)),run_time=.75)
        self.wipe()

    def phase_precision(self):
        with self.narrate("phase_precision") as n:
            title=self.heading("Compute the step count from the requested distance")
            n.at(1);self.play(FadeIn(math_label("N > 0,  |t| ≤ N,  2t²/N ≤ error",size=39,color=TRUTH).move_to([0,.75,0])),run_time=.8)
            n.at(2)
            self.wipe(title)
            self.sources(["lw-phase-steps","lw-phase-value"],"computed phase precision","Precision fuel enforces both requirements, then add one")
            n.at(4)
            self.wipe(title)
            self.play(FadeIn(self.code("(lw-phase-steps 1 1/4) → 9",size=38).move_to([0,.9,0])),run_time=.8)
            n.at(5);self.play(FadeIn(math_label("2/9 < 1/4",size=45,color=GOOD).move_to([0,-.4,0])),run_time=.75)
            n.at(7);self.play(FadeIn(self.caption("The evaluator uses rational arithmetic, not inverse trigonometry",size=25,color=PRED)),run_time=.7)
        self.wipe()

    def phase_meaning(self):
        with self.narrate("phase_meaning") as n:
            title=self.heading("The rational point has a proved phase interpretation")
            self.play(FadeIn(self.chip("arithmetic: rational point + unit bound + compatibility",PRED,width=11).move_to([0,1,0])),run_time=.85)
            n.at(2);self.play(FadeIn(self.chip("interpretation: distance to exp(i t) ≤ requested error",GOOD,width=11).move_to([0,-.3,0])),run_time=.85)
            n.at(4);self.play(FadeIn(math_label("exact unit length",size=36,color=TRUTH).move_to([0,-1.6,0])),run_time=.7)
            n.at(7)
            self.wipe(title)
            self.play(FadeIn(lines("Unit bound: controls amplification", "Distance bound: identifies the direction",size=34,buff=.6,color=TRUTH).move_to([0,.4,0])),run_time=.9)
            n.at(9);self.play(FadeIn(self.caption("PhaseBounds.lean · phaseValue_norm and phaseValue_exp_bound",size=23,color=PRED)),run_time=.75)
        self.wipe()

    def height(self):
        with self.narrate("height") as n:
            title=self.heading("The Mellin angle is −H times the address")
            n.at(1);self.play(FadeIn(math_label("transform height H",size=36,color=PRED).move_to([0,1.15,0])),run_time=.7)
            n.at(2);self.play(FadeIn(math_label("angle t = −Hu     phase = exp(−iHu)",size=39,color=TRUTH).move_to([0,-.1,0])),run_time=.85)
            n.at(3)
            self.wipe(title)
            plane=PhasePlane(circle=True);arrow=plane.arrow(1,0);self.play(FadeIn(plane),GrowArrow(arrow),run_time=.85)
            self.play(Rotate(arrow,angle=-1.2,about_point=plane.center),FadeIn(math_label("H > 0: clockwise as u increases",size=28,color=TRUTH).move_to([3,.7,0])),run_time=1.3)
            n.at(5);self.play(Transform(arrow,plane.arrow(1,0,color=GOOD)),FadeIn(math_label("H = 0: phase = 1",size=33,color=GOOD).move_to([3,-.7,0])),run_time=.9)
            n.at(8);self.play(FadeIn(self.caption("The sign belongs to the mathematical interpretation",size=27,color=PRED)),run_time=.7)
        self.wipe()

    def signal(self):
        with self.narrate("signal") as n:
            title=self.heading("The signal's exponential address also has an error budget")
            self.play(FadeIn(math_label("g(u) = G_z(exp(u))",size=44,color=PRED).move_to([0,.9,0])),run_time=.8)
            n.at(2);self.play(FadeIn(math_label("rational nearby address + proved transport margin",size=31,color=TRUTH).move_to([0,-.55,0])),run_time=.8)
            n.at(4)
            self.wipe(title)
            self.sources(["lw-log-signal-cap","lw-log-signal-lipschitz","lw-log-signal-budget","lw-log-signal-delta"],"choose an address allowance","Coarse cap and transport factor from the earlier signal machinery")
            n.at(5)
            self.wipe(title)
            self.sources(["lw-log-signal-point","lw-log-signal-margin"],"a nearby address and its transport margin","The computed address is near exp(u); the margin pays for displacement")
            n.at(6)
            self.wipe(title)
            self.sources(["lw-log-signal-base","lw-log-signal-bounds"],"enclose the intended log-variable signal","The zero ceiling coefficient selects G_z itself")
            n.at(9);self.play(FadeIn(self.caption("Real interpretation: the interval contains G_z(exp(u))",size=23,color=GOOD).move_to([0,-3.65,0])),run_time=.7)
        self.wipe()

    def caps(self):
        with self.narrate("caps") as n:
            title=self.heading("Compute coarse caps before requesting fine precision")
            n.at(1);self.play(FadeIn(math_label("signal magnitude cap M     weight cap K",size=38,color=TRUTH).move_to([0,.8,0])),run_time=.8)
            n.at(3);self.play(FadeIn(self.caption("The kernel order is called index in the source",y=-.7,size=28,color=DIM)),run_time=.7)
            n.at(4)
            self.wipe(title)
            panel=self.sources(["lw-mellin-signal-cap","lw-mellin-kernel-cap"],"coarse magnitude caps","These definitions do not take the final error request")
            n.at(5);self.play(Indicate(panel.body,color=TRUTH),run_time=.85)
            n.at(6)
            self.wipe(title)
            chain=VGroup(self.chip("coarse caps first",PRED,width=4.5),math_label("→",size=38),self.chip("fine tolerances next",GOOD,width=4.5)).arrange(RIGHT,buff=.4).move_to([0,.5,0]);self.play(FadeIn(chain),run_time=.9)
            n.at(7);self.play(FadeIn(self.caption("This order prevents a circular precision choice",y=-1,size=29,color=TRUTH)),run_time=.7)
        self.wipe()

    def product(self):
        with self.narrate("product") as n:
            title=self.heading("Change one factor at a time")
            self.play(FadeIn(math_label("g w z − g₀ w₀ z₀",size=47,color=PRED).move_to([0,.8,0])),run_time=.8)
            self.play(FadeIn(self.caption("g,w,z intended · g₀,w₀,z₀ computed",y=-.45,size=28,color=DIM)),run_time=.65)
            n.at(2)
            self.wipe(title)
            terms=VGroup(*[math_label(text,size=34,color=color) for text,color in [
                ("|(g−g₀) w z|",PRED),("|g₀ (w−w₀) z|",GOOD),("|g₀ w₀ (z−z₀)|",HYPO)]]).arrange(DOWN,buff=.5).move_to([-2.5,.15,0])
            self.play(FadeIn(terms),run_time=.9)
            n.at(4);self.play(FadeIn(math_label("≤ K δg",size=36,color=PRED).move_to([3,.95,0])),run_time=.7)
            n.at(5);self.play(FadeIn(math_label("≤ M δw",size=36,color=GOOD).move_to([3,.1,0])),run_time=.7)
            n.at(6);self.play(FadeIn(math_label("≤ MK δp",size=36,color=HYPO).move_to([3,-.75,0])),run_time=.7)
            n.at(7);self.play(FadeIn(self.caption("Unit phase · 0 ≤ both weights ≤ K · computed signal magnitude ≤ M",size=23,color=TRUTH)),run_time=.7)
            n.at(8)
            self.wipe(title)
            self.play(FadeIn(math_label("sample distance error ≤ K δg + M δw + MK δp",size=35,color=TRUTH).move_to([0,.65,0])),run_time=.85)
            n.at(9);self.play(FadeIn(self.caption("Every primitive error pays its amplification cost",y=-.95,size=29,color=GOOD)),run_time=.7)
        self.wipe()

    def budget(self):
        with self.narrate("budget") as n:
            title=self.heading("Give each amplified contribution at most a third")
            self.sources(["lw-mellin-component-error"],"one component's tolerance","requested error / [3 × (1 + amplification factor)]")
            n.at(2)
            self.wipe(title)
            panel=self.sources(["lw-mellin-signal-error","lw-mellin-kernel-error","lw-mellin-phase-error"],"three component tolerances","Weight cap for signal · signal cap for weight · product cap for phase")
            n.at_phrase(2,1);self.play(Indicate(panel.body,color=GOOD),run_time=.65)
            n.at_phrase(2,2);self.play(Indicate(panel.body,color=HYPO),run_time=.65)
            n.at(4)
            self.wipe(title)
            self.play(FadeIn(math_label("Illustrative caps: M=2, K=3, error=1/10",size=33,color=TRUTH).move_to([0,1.25,0])),run_time=.75)
            values=VGroup(*[math_label(text,size=35,color=color) for text,color in [("δg = 1/120",PRED),("δw = 1/90",GOOD),("δp = 1/210",HYPO)]]).arrange(RIGHT,buff=.6).move_to([0,.05,0])
            self.play(FadeIn(values[0]),run_time=.65)
            n.at_phrase(4,1);self.play(FadeIn(values[1]),run_time=.65)
            n.at_phrase(4,2);self.play(FadeIn(values[2]),run_time=.65)
            n.at(5);self.play(FadeIn(math_label("3/120 + 2/90 + 6/210 < 1/10",size=36,color=TRUTH).move_to([0,-1.3,0])),run_time=.8)
            n.at(6);self.play(FadeIn(self.caption("Illustrative caps · not values asserted for a particular address",size=23,color=DIM)),run_time=.7)
        self.wipe()

    def components(self):
        with self.narrate("components") as n:
            title=self.heading("Make each approximation choice explicit")
            self.sources(["lw-mellin-signal","lw-mellin-weight","lw-mellin-phase"],"the computed signal, weight and phase","Scalar lower endpoints · phase argument is −height × address")
            n.at(5)
            self.wipe(title)
            self.play(FadeIn(math_label("L ≤ real value ≤ R",size=42,color=PRED).move_to([0,1.05,0])),run_time=.8)
            self.play(FadeIn(math_label("chosen approximation = L",size=38,color=TRUTH).move_to([0,-.1,0])),run_time=.75)
            self.play(FadeIn(math_label("distance from real value ≤ R−L",size=36,color=GOOD).move_to([0,-1.3,0])),run_time=.8)
            n.at(7);self.play(FadeIn(self.caption("Full widths pay the scalar errors; compatibility preserves the caps",size=24,color=DIM)),run_time=.7)
        self.wipe()

    def sample(self):
        with self.narrate("sample") as n:
            title=self.heading("The actual oscillating sample is now a defined function")
            self.sources(["lw-mellin-sample"],"the actual weighted sample","u, σ, cell weight ≥ 0 rational · rational height · natural index · positive rational error")
            n.at(3)
            self.wipe(title)
            plane=PhasePlane(circle=True);arrow=plane.arrow(.6,-.8,color=HYPO);self.play(FadeIn(plane),GrowArrow(arrow),run_time=.9)
            self.play(FadeIn(lines("Illustrative components","signal = −2","weight = 1/2","phase = (3/5,−4/5)",size=29,buff=.23,color=PRED).move_to([3,.4,0])),run_time=.8)
            n.at(4);self.play(Transform(arrow,plane.arrow(-.6,.8,color=GOOD)),FadeIn(self.caption("sample = (−3/5,4/5)",size=31,color=GOOD)),run_time=1.1)
            n.at(5);self.play(Transform(title,fitted(B("The illustration shows the product, not an asserted G_z value",size=35)).move_to(title)),run_time=.8)
        self.wipe()

    def checks(self):
        with self.narrate("checks") as n:
            title=self.heading("Check the rational premises of sample soundness")
            panel=self.popup("lw-mellin-sample-check","Caps, component widths and the amplified sample budget",page_size=8)
            if panel.page_count!=2:raise ValueError("Update narration for the sample check's source pages")
            n.at(2);panel.turn_page(self,1)
            n.at(3);self.play(Indicate(panel.body,color=TRUTH),run_time=.9)
            n.at(4)
            self.wipe(title)
            self.play(FadeIn(math_label("generic phase theorem + exact rational checks",size=37,color=PRED).move_to([0,.95,0])),run_time=.85)
            n.at(6);self.play(FadeIn(math_label("⇒ distance to the intended weighted sample ≤ error",size=32,color=GOOD).move_to([0,-.4,0])),run_time=.85)
            n.at(7);self.play(FadeIn(self.caption("MellinIntegrand.lean · mellinSample_sound",size=26,color=TRUTH)),run_time=.7)
        self.wipe()

    def cells(self):
        with self.narrate("cells") as n:
            title=self.heading("A finite weighted grid is explicit list data")
            n.at(1);self.play(FadeIn(self.code("'(address . weight)",size=39).move_to([0,.85,0])),run_time=.8)
            n.at(2);self.play(FadeIn(self.code("'((0 . 1/2) (1/2 . 1/2))",size=37).move_to([0,-.4,0])),run_time=.8)
            n.at(3)
            self.wipe(title)
            self.sources(["lw-mellin-cellsp"],"valid finite cell data","caar reads the first address · cdar reads its weight")
            n.at(4)
            self.wipe(title)
            pair=VGroup(self.chip("u=0, weight=1/2",PRED,width=5),self.chip("u=1/2, weight=1/2",GOOD,width=5)).arrange(RIGHT,buff=.7).move_to([0,.6,0]);self.play(FadeIn(pair),run_time=.9)
            n.at(5);self.play(FadeIn(self.caption("Cell pair = address and weight · complex pair = two coordinates",y=-.9,size=25,color=TRUTH)),run_time=.75)
            n.at(6);self.play(FadeIn(self.caption("Each sample allowance already covers its weighted contribution",size=25,color=DIM)),run_time=.7)
        self.wipe()

    def finite_sum(self):
        with self.narrate("finite_sum") as n:
            title=self.heading("Traverse the list and add the actual computed samples")
            self.sources(["lw-mellin-sum-raw"],"the finite computed sum","One sample from the first cell + recursion on the remaining cells")
            n.at(3)
            self.wipe(title)
            plane=PhasePlane(circle=False);self.play(FadeIn(plane),run_time=.75)
            first=plane.arrow(-.6,.8,color=PRED);second=Arrow(plane.point(-.6,.8),plane.point(-.4,.6),buff=0,color=HYPO,stroke_width=4)
            self.play(GrowArrow(first),GrowArrow(second),run_time=1)
            self.play(FadeIn(math_label("(−3/5,4/5) + (1/5,−1/5)",size=28,color=PRED).move_to([3,.8,0])),run_time=.7)
            n.at(4);self.play(GrowArrow(plane.arrow(-.4,.6,color=GOOD)),FadeIn(math_label("= (−2/5,3/5)",size=36,color=GOOD).move_to([3,-.45,0])),run_time=.95)
            n.at(5);self.play(FadeIn(self.caption("Illustrative contributions · not asserted outputs at the earlier cells",size=23,color=DIM)),run_time=.7)
        self.wipe()

    def sum_budget(self):
        with self.narrate("sum_budget") as n:
            title=self.heading("Allocate the finite sum's evaluation budget")
            n.at(1);self.play(FadeIn(math_label("point error = sum budget / (N+1)",size=41,color=TRUTH).move_to([0,.65,0])),run_time=.8)
            n.at(2)
            self.wipe(title)
            self.sources(["lw-mellin-sum-error","lw-mellin-sum"],"the total-budget wrapper","The per-point error already refers to a weighted sample")
            n.at(3)
            self.wipe(title)
            self.play(FadeIn(math_label("N=2, sum budget=1/10:  point error=1/30",size=34,color=PRED).move_to([0,1.05,0])),run_time=.8)
            n.at(4);self.play(FadeIn(math_label("2 × 1/30 = 1/15 < 1/10",size=42,color=GOOD).move_to([0,-.15,0])),run_time=.85)
            n.at(5);self.play(FadeIn(self.caption("Complex triangle inequality · no cancellation needed",y=-1.5,size=27,color=TRUTH)),run_time=.7)
            n.at(8);self.play(FadeIn(self.caption("Evaluation budget only · mesh and tail costs remain separate",size=25,color=DIM)),run_time=.7)
        self.wipe()

    def one_sided(self):
        with self.narrate("one_sided") as n:
            title=self.heading("The one-sided estimate keeps its extra real reading")
            n.at(1);conditions=VGroup(*[self.chip(text,color,width=9.7) for text,color in [("nonnegative weights",GOOD),("signal values with either sign",PRED),("phases in the unit disk",TRUTH)]]).arrange(DOWN,buff=.3).move_to([0,.05,0]);self.play(FadeIn(conditions),run_time=.95)
            n.at(2)
            self.wipe(title)
            self.play(FadeIn(math_label("|oscillating sum| + plain reading ≤ positive-contribution budget",size=29,color=GOOD).move_to([0,.8,0])),run_time=.85)
            n.at(3);self.play(FadeIn(self.caption("mellin-sums.lisp · lw-mellin-one-sided-bound",y=-.5,size=25,color=PRED)),run_time=.7)
            n.at(4);self.play(FadeIn(math_label("The plain real reading remains",size=39,color=TRUTH).move_to([0,-1.65,0])),run_time=.75)
        self.wipe()

    def interpretation(self):
        with self.narrate("interpretation") as n:
            title=self.heading("Attach each computation to the quantity it represents")
            self.play(FadeIn(self.chip("sample → intended weighted integrand + distance allowance",PRED,width=11.5).move_to([0,1.15,0])),run_time=.85)
            n.at(1);self.play(FadeIn(self.chip("finite sum → intended finite sum + total evaluation error",GOOD,width=11.5).move_to([0,-.15,0])),run_time=.85)
            n.at(2);self.play(FadeIn(self.caption("MellinIntegrand.lean · MellinQuadrature.lean",y=-1.6,size=26,color=TRUTH)),run_time=.7)
            n.at(5)
            self.wipe(title)
            bridge=VGroup(*[self.chip(text,color,width=10.5) for text,color in [("finite sum + mesh and tail arguments → improper moment",PRED),("analytic identification + valid pole geometry → competing estimate",TRUTH)]]).arrange(DOWN,buff=.65).move_to([0,.25,0]);self.play(FadeIn(bridge[0]),run_time=.8)
            n.at(6);self.play(FadeIn(bridge[1]),run_time=.85)
            n.at(7);self.play(FadeIn(self.caption("The bridges are part of the proof, with their hypotheses attached",size=25,color=GOOD)),run_time=.7)
        self.wipe()

    def scope(self):
        with self.narrate("scope") as n:
            title=self.heading("Three explicit constructors with proved budgets")
            items=VGroup(*[self.chip(text,color,width=8) for text,color in [("rational phase",TRUTH),("oscillating weighted sample",PRED),("evaluated finite sum",GOOD)]]).arrange(DOWN,buff=.35).move_to([0,.1,0]);self.play(FadeIn(items),run_time=.95)
            n.at(4);self.play(FadeIn(self.caption("Concrete components on the route toward Peano Arithmetic",size=26,color=TRUTH)),run_time=.7)
            n.at(5)
            self.wipe(title)
            self.play(FadeIn(lines("Final composition", "General-zero applicability", "Arithmetic interpretation",size=35,buff=.5,color=TRUTH).move_to([0,.3,0])),run_time=.95)
            n.at(6);self.play(FadeIn(self.caption("An evaluated sum is not automatically a coefficient contradiction",size=25,color=DIM)),run_time=.7)
        self.wipe()

    def next(self):
        with self.narrate("next") as n:
            title=self.heading("The finite complex reading is now visible")
            self.play(FadeIn(math_label("signal × weight × phase → sample → finite sum",size=36,color=PRED).move_to([0,.75,0])),run_time=.85)
            n.at(2);self.play(FadeIn(self.caption("Product amplification budget + separate sum allocation",y=-.65,size=28,color=TRUTH)),run_time=.7)
            n.at(4)
            self.wipe(title)
            self.play(FadeIn(math_label("Part Eight · Poles, zero covers and competing coefficients",size=34,color=TRUTH).move_to([0,.65,0])),run_time=.85)
            n.at(5);self.play(FadeIn(self.caption("Illustrative geometry · checked certificates · actual zeros",y=-.85,size=28,color=GOOD)),run_time=.7)
        self.wipe()
