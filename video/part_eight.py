"""Part Eight: checked pole geometry and the conditional coefficient contradiction."""
import math
import textwrap
from lesson_scene import *
from lesson_source import PagedSourcePopup
from function_popup import read_form
from part_two import RationalRuler
from part_five import math_label


SOURCE_FILES={
 "complex-geometric":["lw-complex-conjugate","lw-complex-norm-square","lw-complex-reciprocal"],
 "pole-lower":["lw-pole-coefficient"],
 "pole-geometry":["lw-plane-pointp","lw-distance-squared","lw-tie-numerator","lw-tie-denominator","lw-tie-height","lw-avoid-height-interval","lw-chosen-height","lw-nearest-point","lw-other-points","lw-isolating-radius-squared"],
 "box-circles":["lw-boxp","lw-box-contains","lw-square-interval","lw-distance-box","lw-boxes-outside-circle","lw-circle-check"],
 "zeta-pole-lower":["lw-zeta-residue-denominator","lw-zeta-pole-residue"],
 "pole-radius-dominance":["lw-pole-regular-coefficient"],
 "cauchy-extraction":["lw-cauchy-boundary-check"],
 "mellin-pole-bridge":["lw-zeta-model-coefficient","lw-zeta-model-polynomial","lw-mellin-model-boundary-check"],
 "mellin-real-anchor":["lw-mellin-real-anchor-bound"],
 "mellin-window-budget":["lw-mellin-window-decay-index","lw-mellin-model-error-precision"]}
SOURCE_LOOKUP={name:".tools/acl2-part08/acl2/"+book+".lisp" for book,names in SOURCE_FILES.items() for name in names}
SOURCE_LOOKUP.update({name:".tools/acl2-part08/video/teaching-part08.lisp" for name in ["video-eight-geometric-prefix","video-eight-toy-coefficient","video-eight-separated-bounds"]})


class SourceGroup(VGroup):
    def __init__(self,names,title,note):
        super().__init__();lines=[]
        for name in names:
            if lines:lines.append("")
            for line in read_form(SOURCE_LOOKUP[name],"defun",name).splitlines():
                indent=len(line)-len(line.lstrip())
                lines.extend(textwrap.wrap(line,width=72,subsequent_indent=" "*(indent+2),
                    break_long_words=False,break_on_hyphens=False,replace_whitespace=False) or [""])
        if len(lines)>17:raise ValueError(f"Split source group: {names}, {len(lines)} lines")
        background=card(12.5,6.65,stroke=PRED)
        heading=fitted(T("ACL2 definitions · "+title,size=26,color=TRUTH),11.6).move_to([0,2.2,0])
        self.body=fitted(T("\n".join(lines),size=29,font="Consolas"),11.3)
        if self.body.height>3.45:self.body.scale_to_fit_height(3.45)
        self.body.move_to([0,-.1,0])
        footer=fitted(T(note,size=22,color=DIM),11.4).move_to([0,-2.55,0])
        self.add(background,heading,self.body,footer,T("Complete source · isolated certified snapshots",size=17,color=DIM).move_to([0,-3,0]))


class PolePlane(VGroup):
    def __init__(self):
        super().__init__();self.origin=np.array([-4.65,-1.05,0]);self.unit=1.15
        self.add(Line(self.point(-.3,0),self.point(3.35,0),color=DIM),
                 Line(self.point(0,-1.6),self.point(0,2.05),color=DIM),
                 DashedLine(self.point(2,-1.65),self.point(2,2),color=FAINT))
        self.add(T("real",size=19,color=DIM).move_to(self.point(3.2,-.3)),
                 T("imaginary",size=19,color=DIM).move_to(self.point(.25,2.25)))

    def point(self,x,y):return self.origin+RIGHT*float(x)*self.unit+UP*float(y)*self.unit
    def marker(self,x,y,color=PRED):return Dot(self.point(x,y),radius=.075,color=color)
    def box(self,x0,x1,y0,y1,color=PRED):
        return Rectangle(width=(x1-x0)*self.unit,height=(y1-y0)*self.unit,
                         color=color,fill_color=color,fill_opacity=.2).move_to(self.point((x0+x1)/2,(y0+y1)/2))


class PartEight(LessonScene):
    manifest_file="manifest-part08.json"
    timing_file="timing-part08.json"
    review_label="PART EIGHT · REVIEW 01"
    lesson_methods=("opening","poles","geometric","coefficients","reciprocal","center","ties","avoid","nearest","isolation",
        "boxes","square","box_distance","circle","cover","multiplicity","dominance","regular","model","comparison",
        "anchor","budget","contradiction","witness","scope","next")

    def sources(self,names,title,note=""):
        panel=SourceGroup(names,title,note);self.play(FadeIn(panel,scale=.96),run_time=.8);return panel

    def popup(self,name,note="",kind="defun",page_size=9):
        panel=PagedSourcePopup(SOURCE_LOOKUP[name],name,note,kind=kind,page_size=page_size)
        self.play(FadeIn(panel,scale=.96),run_time=.8);return panel

    def opening(self):
        with self.narrate("opening") as n:
            title=self.heading("Compare two descriptions of the same reading")
            left=self.chip("signal ceiling → upper estimate",PRED,width=6.6).move_to([0,.8,0]);self.play(FadeIn(left),run_time=.8)
            n.at(3);self.play(FadeIn(self.chip("isolated pole → lower estimate",TRUTH,width=6.6).move_to([0,-.55,0])),run_time=.8)
            n.at(4);self.play(FadeIn(self.caption("geometry → model → comparison → contradiction",y=-1.9,size=30,color=GOOD)),run_time=.8)
            n.at(6);self.play(FadeIn(self.caption("Illustrative points and boxes · actual-zero hypotheses stay explicit",size=24,color=DIM)),run_time=.7)
            n.at(7);self.play(Transform(title,fitted(B("Part Eight · Poles, zero covers and the contradiction",size=37)).move_to(title)),run_time=.8)
        self.wipe()

    def poles(self):
        with self.narrate("poles") as n:
            title=self.heading("A reciprocal singularity leaves a visible trace")
            axes=Axes(x_range=[0,1,.25],y_range=[0,8,2],x_length=7.5,y_length=3.4,
                      axis_config={"include_numbers":False,"include_tip":False,"color":DIM}).move_to([-1.1,-.2,0])
            graph=VMobject(color=PRED).set_points_as_corners([axes.c2p(x,1/(1-x)) for x in np.linspace(0,.875,110)])
            self.play(FadeIn(axes),Create(graph),FadeIn(math_label("1/(1−x)",size=33,color=PRED).move_to([4,.7,0])),run_time=1)
            n.at(1);dot=Dot(axes.c2p(.5,2),color=TRUTH);self.play(FadeIn(dot),run_time=.4)
            for x in [.75,.875]:self.play(dot.animate.move_to(axes.c2p(x,1/(1-x))),run_time=1)
            n.at(2);self.play(FadeIn(T("x = 1",size=24,color=TRUTH).move_to(axes.c2p(1,0)+DOWN*.35)),run_time=.7)
            n.at(3)
            self.wipe(title)
            self.play(FadeIn(math_label("F(z) = reciprocal pole part + regular part",size=37,color=PRED).move_to([0,.7,0])),run_time=.85)
            n.at(5);self.play(FadeIn(self.caption("regular here = analytic nearby = local power series",y=-.75,size=29,color=GOOD)),run_time=.8)
            n.at(7);self.play(FadeIn(self.caption("Read the singularity through its coefficients",y=-2,size=31,color=TRUTH)),run_time=.75)
        self.wipe()

    def geometric(self):
        with self.narrate("geometric") as n:
            title=self.heading("Start with a finite geometric identity")
            terms=VGroup(*[math_label(t,size=45,color=PRED) for t in ["1","+ 1/2","+ 1/4"]]).arrange(RIGHT,buff=.55).move_to([0,1,0])
            n.at(1);self.play(FadeIn(terms[0]),run_time=.6)
            n.at_phrase(1,1);self.play(FadeIn(terms[1]),run_time=.6)
            n.at_phrase(1,2);self.play(FadeIn(terms[2]),run_time=.6)
            n.at(2);self.play(FadeIn(math_label("prefix = 7/4",size=39,color=GOOD).move_to([0,-.1,0])),run_time=.7)
            n.at(3);self.play(FadeIn(math_label("7/4 + 1/4 = 2",size=42,color=TRUTH).move_to([0,-1.3,0])),run_time=.75)
            n.at(4)
            self.wipe(title)
            self.play(FadeIn(M("(1−x)(1+x+⋯+x<sup>N−1</sup>) = 1−x<sup>N</sup>",size=40,color=PRED).move_to([0,.85,0])),run_time=.85)
            n.at(5);self.play(FadeIn(M("1/(1−x) = prefix + x<sup>N</sup>/(1−x)",size=37,color=TRUTH).move_to([0,-.5,0])),run_time=.8)
            n.at(6)
            self.wipe(title)
            self.sources(["video-eight-geometric-prefix"],"the finite geometric prefix","Natural count · exact arithmetic; no infinite sum in this function")
            n.at(7)
            self.wipe(title)
            self.play(FadeIn(self.caption("Limit interpretation: |x| < 1 makes the remainder tend to zero",y=.2,size=30,color=GOOD)),run_time=.7)
        self.wipe()

    def coefficients(self):
        with self.narrate("coefficients") as n:
            title=self.heading("The offset determines the coefficient scale")
            self.play(FadeIn(math_label("c/(a−z) = (c/a) × 1/(1−z/a)",size=43,color=PRED).move_to([0,1,0])),run_time=.9)
            n.at(3);self.play(FadeIn(M("coefficient of z<sup>j</sup>:  c/a<sup>j+1</sup>",size=42,color=TRUTH).move_to([0,-.2,0])),run_time=.85)
            n.at(4);self.play(FadeIn(math_label("c=1, a=2:",size=33,color=GOOD).move_to([-3.4,-1.5,0])),FadeIn(math_label("1/2",size=36,color=GOOD).move_to([-.7,-1.5,0])),run_time=.7)
            n.at_phrase(4,1);self.play(FadeIn(math_label("1/4",size=36,color=GOOD).move_to([1.3,-1.5,0])),run_time=.65)
            n.at_phrase(4,2);self.play(FadeIn(math_label("1/8, …",size=36,color=GOOD).move_to([3.6,-1.5,0])),run_time=.65)
            n.at(5);self.play(FadeIn(self.caption("index 5: 1/64 · a ≠ 0; expansion valid for |z| < |a|",size=25,color=DIM)),run_time=.7)
        self.wipe()

    def reciprocal(self):
        with self.narrate("reciprocal") as n:
            title=self.heading("Complex reciprocals stay rational")
            self.sources(["lw-complex-conjugate","lw-complex-norm-square","lw-complex-reciprocal"],"conjugate, squared magnitude and reciprocal","Nonzero complex input for the reciprocal identity")
            n.at(3)
            self.wipe(title)
            self.play(FadeIn(math_label("1/(2+i) = (2−i)/5 = 2/5 − (1/5)i",size=41,color=TRUTH).move_to([0,.65,0])),run_time=.9)
            n.at(4)
            self.wipe(title)
            self.sources(["lw-pole-coefficient"],"the physical pole coefficient","Natural index j · residue × reciprocal(offset)^(j+1)")
            n.at(7)
            self.wipe(title)
            self.play(FadeIn(self.caption("nfix preserves a natural number and returns zero otherwise",y=.2,size=28,color=DIM)),run_time=.7)
        self.wipe()

    def center(self):
        with self.narrate("center") as n:
            title=self.heading("A nearest point may not be strictly nearest")
            plane=PolePlane();points=VGroup(plane.marker(1,1),plane.marker(1,-1),plane.marker(0,0));center=plane.marker(2,0,TRUTH)
            self.play(FadeIn(plane),FadeIn(points),FadeIn(center),run_time=.9)
            n.at(2);ties=VGroup(Line(plane.point(2,0),plane.point(1,1),color=TRUTH),Line(plane.point(2,0),plane.point(1,-1),color=TRUTH));self.play(Create(ties),run_time=.8)
            n.at(3);self.play(FadeIn(math_label("H=0:  d₁²=d₂²=2",size=34,color=TRUTH).move_to([3,.7,0])),run_time=.75)
            n.at(5);self.play(FadeOut(ties),center.animate.move_to(plane.point(2,5/8)),run_time=1.1)
            n.at(6)
            self.wipe(title)
            self.sources(["lw-plane-pointp","lw-distance-squared"],"rational points and squared distances","All candidates strictly left of the fixed center line")
        self.wipe()

    def ties(self):
        with self.narrate("ties") as n:
            title=self.heading("Equal squared distances give a linear equation")
            self.play(FadeIn(math_label("(σ−x₁)²+(H−y₁)² = (σ−x₂)²+(H−y₂)²",size=32,color=PRED).move_to([0,1,0])),run_time=.9)
            n.at(1);self.play(FadeIn(math_label("H² cancels → at most one H when y₁ ≠ y₂",size=33,color=TRUTH).move_to([0,-.3,0])),run_time=.8)
            n.at(3)
            self.wipe(title)
            self.sources(["lw-tie-numerator","lw-tie-denominator","lw-tie-height"],"candidate tie heights","Equal imaginary coordinates: harmless extra candidate 0")
            n.at(4)
            self.wipe(title)
            self.play(FadeIn(math_label("example forbidden heights: −1, 0, 1",size=42,color=TRUTH).move_to([0,.8,0])),run_time=.8)
            n.at(5);self.play(FadeIn(self.caption("Same height + distinct points left of σ → unequal horizontal distances",y=-.65,size=27,color=GOOD)),run_time=.75)
            n.at(7);self.play(FadeIn(self.caption("A finite overestimate of the forbidden list is safe",y=-1.95,size=28,color=DIM)),run_time=.7)
        self.wipe()

    def avoid(self):
        with self.narrate("avoid") as n:
            title=self.heading("Halve an interval once per forbidden height")
            ruler=RationalRuler(-1,1,[(-1,"−1"),(0,"0"),(.5,"1/2"),(.75,"3/4"),(1,"1")],y=.3)
            band=Line(ruler.point(-1),ruler.point(1),color=PRED,stroke_width=13)
            self.play(FadeIn(ruler),Create(band),run_time=.85)
            n.at(1);self.play(Transform(band,Line(ruler.point(0),ruler.point(1),color=PRED,stroke_width=13)),run_time=1)
            n.at(2);self.play(Transform(band,Line(ruler.point(.5),ruler.point(1),color=PRED,stroke_width=13)),run_time=1)
            n.at(3);self.play(Transform(band,Line(ruler.point(.5),ruler.point(.75),color=PRED,stroke_width=13)),run_time=1)
            n.at(6);self.play(FadeIn(Dot(ruler.point(5/8),color=TRUTH)),FadeIn(math_label("chosen H = 5/8",size=40,color=TRUTH).move_to([0,-1.1,0])),run_time=.8)
            n.at(8)
            self.wipe(title)
            self.sources(["lw-avoid-height-interval","lw-chosen-height"],"avoid each forbidden value, then take the midpoint","Rational lower < upper · finite forbidden list")
        self.wipe()

    def nearest(self):
        with self.narrate("nearest") as n:
            title=self.heading("The nearest-point scan now has a strict gap")
            plane=PolePlane();self.play(FadeIn(plane),FadeIn(plane.marker(2,5/8,TRUTH)),run_time=.7)
            values=[(1,1,"73/64",GOOD),(1,-1,"233/64",PRED),(0,0,"281/64",PRED)]
            n.at(1)
            for i,(x,y,label,color) in enumerate(values):
                if i:n.at_phrase(1,i)
                self.play(FadeIn(plane.marker(x,y,color)),FadeIn(math_label("d² = "+label,size=32,color=color).move_to([3,1.1-i*.85,0])),run_time=.65)
            n.at(3)
            self.wipe(title)
            self.sources(["lw-nearest-point"],"the recursive distance comparison","Nonempty point list · compare squared distances")
            n.at(7)
            self.wipe(title)
            self.play(FadeIn(self.caption("Equal copies share a location; strictness concerns different points",y=.2,size=27,color=GOOD)),run_time=.7)
        self.wipe()

    def isolation(self):
        with self.narrate("isolation") as n:
            title=self.heading("Average across the strict squared-distance gap")
            self.play(FadeIn(math_label("r² = (selected d² + min(cap, next d²))/2",size=38,color=PRED).move_to([0,1,0])),run_time=.85)
            n.at(3);self.play(FadeIn(math_label("73/64 < 153/64 < 233/64",size=41,color=TRUTH).move_to([0,-.2,0])),run_time=.8)
            n.at(5)
            self.wipe(title)
            plane=PolePlane();circle=Circle(radius=math.sqrt(153/64)*plane.unit,color=GOOD).move_to(plane.point(2,5/8))
            self.play(FadeIn(plane),FadeIn(VGroup(plane.marker(1,1,GOOD),plane.marker(1,-1),plane.marker(0,0),plane.marker(2,5/8,TRUTH))),Create(circle),run_time=1)
            self.play(FadeIn(lines("center = (2, 5/8)","squared radius = 153/64","cap = 4",size=28,color=TRUTH).move_to([3,.4,0])),run_time=.7)
            n.at(6)
            self.wipe(title)
            self.sources(["lw-other-points","lw-isolating-radius-squared"],"remove equal copies and compute the isolating radius","Certificate stores r² · nonempty list left of σ · selected d² < cap")
        self.wipe()

    def boxes(self):
        with self.narrate("boxes") as n:
            title=self.heading("Replace an approximate marker by a containing box")
            plane=PolePlane();dot=plane.marker(.6,1,TRUTH);box=plane.box(.35,.85,.7,1.3)
            self.play(FadeIn(plane),FadeIn(dot),run_time=.75)
            n.at(2);self.play(Create(box),run_time=1)
            n.at(3);self.play(FadeIn(self.code("(real-lo real-hi imag-lo imag-hi)",size=27).move_to([2.6,.65,0])),run_time=.8)
            n.at(4)
            self.wipe(title)
            self.sources(["lw-boxp","lw-box-contains"],"box validity and rational containment","Four entries · ordered real interval · ordered imaginary interval")
            n.at(7)
            self.wipe(title)
            self.play(FadeIn(self.caption("The whole selected box inside · every competing box outside",y=.2,size=29,color=GOOD)),run_time=.7)
        self.wipe()

    def square(self):
        with self.narrate("square") as n:
            title=self.heading("Squaring an interval must retain the interior")
            ruler=RationalRuler(-2,3,[(-2,"−2"),(0,"0"),(3,"3")],y=.7)
            band=Line(ruler.point(-2),ruler.point(3),color=PRED,stroke_width=12);self.play(FadeIn(ruler),Create(band),run_time=.8)
            n.at(2);self.play(FadeIn(math_label("endpoint squares: 4 and 9",size=36,color=TRUTH).move_to([0,-.55,0])),run_time=.8)
            n.at(3);self.play(FadeIn(Dot(ruler.point(0),color=GOOD)),FadeIn(math_label("but 0² = 0",size=37,color=GOOD).move_to([0,-1.7,0])),run_time=.8)
            n.at(4);self.play(FadeIn(self.caption("[−2,3]² is enclosed by [0,9]",size=30,color=GOOD)),run_time=.7)
            n.at(7)
            self.wipe(title)
            self.sources(["lw-square-interval"],"square an interval, including a crossing of zero","Crosses zero → lower endpoint 0; upper endpoint = max(endpoint squares)")
        self.wipe()

    def box_distance(self):
        with self.narrate("box_distance") as n:
            title=self.heading("Every point in the box gets a distance bound")
            self.sources(["lw-distance-box"],"interval squared distance to a box","Subtract coordinates → square intervals → add intervals")
            n.at(3)
            self.wipe(title)
            plane=PolePlane();self.play(FadeIn(plane),FadeIn(plane.marker(2,1,TRUTH)),run_time=.8)
            self.play(Create(plane.box(.59,.61,.99,1.01,GOOD)),Create(plane.box(.59,.61,-1.01,-.99,PRED)),run_time=.9)
            self.play(FadeIn(lines("New example: center (2,1)","boxes around (3/5,±1)",size=28,color=PRED).move_to([3,1.1,0])),run_time=.7)
            n.at(5);self.play(FadeIn(math_label("selected: all d² < 2",size=34,color=GOOD).move_to([3,-.35,0])),FadeIn(math_label("other: all d² > 5",size=34,color=PRED).move_to([3,-1.25,0])),run_time=.85)
            n.at(7);self.play(Create(Circle(radius=math.sqrt(3)*plane.unit,color=TRUTH).move_to(plane.point(2,1))),FadeIn(self.caption("Squared radius 3 · exact checks, conservative displayed summaries",size=23,color=DIM)),run_time=1)
        self.wipe()

    def circle(self):
        with self.narrate("circle") as n:
            title=self.heading("Compare box bounds with a squared radius")
            self.sources(["lw-boxes-outside-circle"],"exclude all competing boxes","Each lower squared-distance bound > stored squared radius")
            n.at(1)
            self.wipe(title)
            self.sources(["lw-circle-check"],"the actual circle checker","Selected upper bound < r² < every other lower bound")
            n.at(3)
            self.wipe(title)
            self.play(FadeIn(math_label("selected box inside · all competing boxes outside",size=35,color=GOOD).move_to([0,1,0])),run_time=.8)
            n.at(4);self.play(FadeIn(math_label("2 < 3 < 5",size=55,color=TRUTH).move_to([0,-.3,0])),run_time=.85)
            n.at(5);self.play(FadeIn(self.caption("ACL2 parameter radius = squared radius in this checker",y=-1.85,size=28,color=DIM)),run_time=.75)
        self.wipe()

    def cover(self):
        with self.narrate("cover") as n:
            title=self.heading("Geometry needs a complete and meaningful cover")
            boxes=VGroup(*[self.chip(t,c,width=10.7) for t,c in [("1 · every relevant zero is covered",PRED),("2 · selected box contains one zero location",TRUTH),("3 · selected inside; every other box outside",GOOD)]]).arrange(DOWN,buff=.32).move_to([0,.1,0])
            n.at(2);self.play(FadeIn(boxes[0]),FadeIn(boxes[1]),run_time=.9)
            n.at(3);self.play(FadeIn(self.caption("One location can have multiplicity greater than one",size=27,color=TRUTH)),run_time=.7)
            n.at(6);self.play(FadeIn(boxes[2]),run_time=.8)
            n.at(7);self.play(Transform(title,fitted(B("Checking a supplied cover does not generate one",size=39)).move_to(title)),run_time=.8)
        self.wipe()

    def multiplicity(self):
        with self.narrate("multiplicity") as n:
            title=self.heading("Multiplicity scales one pole contribution")
            self.play(FadeIn(math_label("ζ′(s)/ζ(s) = m/(s−ρ) + regular",size=40,color=PRED).move_to([0,1.05,0])),run_time=.85)
            n.at(2);self.play(FadeIn(math_label("normalization: −1/[s(s−1)]",size=36,color=TRUTH).move_to([0,-.1,0])),run_time=.8)
            n.at(3);self.play(FadeIn(math_label("c = −m/[ρ(ρ−1)]",size=43,color=GOOD).move_to([0,-1.35,0])),run_time=.8)
            n.at(4)
            self.wipe(title)
            self.sources(["lw-zeta-residue-denominator","lw-zeta-pole-residue"],"the zeta pole coefficient convention","Rational model point ρ ≠ 0,1 · positive natural multiplicity")
            n.at(5)
            self.wipe(title)
            self.play(FadeIn(math_label("illustrative ρ = 1/2+i:  m=1 → 4/5;  m=2 → 8/5",size=33,color=TRUTH).move_to([0,.65,0])),run_time=.9)
            n.at(6);self.play(FadeIn(self.caption("Illustrative input only · not a certified zeta zero",y=-1,size=28,color=DIM)),run_time=.75)
        self.wipe()

    def dominance(self):
        with self.narrate("dominance") as n:
            title=self.heading("Nearer does not mean dominant at every index")
            self.play(FadeIn(math_label("F(z) = 1/(2−z) − 3/(3−z)",size=43,color=PRED).move_to([0,1,0])),run_time=.85)
            n.at(2);self.play(FadeIn(math_label("index 0:  1/2 − 1 = −1/2",size=37,color=TRUTH).move_to([0,-.3,0])),run_time=.8)
            n.at(4)
            self.wipe(title)
            self.play(FadeIn(M("2<sup>j+1</sup> × coefficient = 1 − 3(2/3)<sup>j+1</sup>",size=37,color=PRED).move_to([0,1.3,0])),run_time=.85)
            self.play(FadeIn(self.caption("Blue bars: magnitude of the competing contribution",y=.72,size=24,color=DIM)),run_time=.65)
            bars=VGroup();base=np.array([-4.8,-1.7,0])
            for j in range(6):
                height=2.1*3*(2/3)**(j+1)/2
                bar=Rectangle(width=.7,height=height,stroke_color=PRED,fill_color=PRED,fill_opacity=.5).move_to(base+RIGHT*j*1.7+UP*height/2)
                bars.add(bar,T(str(j),size=22,color=DIM).next_to(bar,DOWN,buff=.15))
            n.at(5);self.play(LaggedStart(*[FadeIn(m) for m in bars],lag_ratio=.08),run_time=1.3)
            n.at(6);self.play(FadeIn(math_label("j=5: 179/243 > 1/2",size=34,color=TRUTH).move_to([0,-2.75,0])),run_time=.8)
            n.at(8)
            self.wipe(title)
            self.sources(["video-eight-toy-coefficient"],"the two-pole teaching model","Illustrative poles at 2 and 3; exact project coefficient constructor")
        self.wipe()

    def regular(self):
        with self.narrate("regular") as n:
            title=self.heading("The regular coefficients need a larger contour")
            self.play(FadeIn(math_label("regular part: |h(z)| ≤ B on |z| = R",size=36,color=PRED).move_to([0,1,0])),run_time=.8)
            n.at(1);self.play(FadeIn(M("Cauchy estimate: |h<sub>j</sub>| ≤ B/R<sup>j</sup>",size=43,color=TRUTH).move_to([0,-.2,0])),run_time=.85)
            n.at(2);self.play(FadeIn(math_label("selected distance d < R → d/R < 1",size=35,color=GOOD).move_to([0,-1.4,0])),run_time=.75)
            n.at(4)
            self.wipe(title)
            self.sources(["lw-pole-regular-coefficient"],"physical-radius rescaling","Coefficient of unit variable w becomes coefficient/R^j for z=R w")
            n.at(5)
            self.wipe(title)
            self.sources(["lw-cauchy-boundary-check"],"finite polynomial boundary checks","Prescribed rational orbit + computed count + proved extraction allowance")
            n.at(6)
            self.wipe(title)
            self.play(FadeIn(self.caption("Finite samples alone do not bound an arbitrary analytic function",y=.2,size=29,color=TRUTH)),run_time=.7)
        self.wipe()

    def model(self):
        with self.narrate("model") as n:
            title=self.heading("Construct coefficients instead of assuming agreement")
            self.sources(["lw-zeta-model-coefficient"],"selected pole + other poles + regular coefficient","Fixed rational model inputs · explicit physical radius")
            n.at(2)
            self.wipe(title)
            self.sources(["lw-zeta-model-polynomial"],"build the finite coefficient list","Advance offset · decrease natural count · stop at the empty list")
            n.at(3)
            self.wipe(title)
            self.play(FadeIn(self.chip("constructed model polynomial",PRED,width=8).move_to([0,.7,0])),run_time=.8)
            n.at(5);self.play(FadeIn(self.chip("analytic justification of its input data",TRUTH,width=9).move_to([0,-.8,0])),run_time=.8)
        self.wipe()

    def comparison(self):
        with self.narrate("comparison") as n:
            title=self.heading("Compare two constructed polynomials")
            panel=self.popup("lw-mellin-model-boundary-check","Actual improper polynomial − pole-model polynomial; bound the difference",page_size=8)
            if panel.page_count!=2:raise ValueError(f"Revisit comparison narration: {panel.page_count} source pages")
            n.at(2);panel.turn_page(self,1)
            n.at(3)
            self.wipe(title)
            self.play(FadeIn(self.chip("accepted boundary comparison → coefficient-distance bound",GOOD,width=11.7).move_to([0,.75,0])),run_time=.85)
            n.at(5);self.play(FadeIn(math_label("current improper-polynomial region: σ − inner radius > 2",size=31,color=TRUTH).move_to([0,-.6,0])),run_time=.8)
            n.at(6);self.play(FadeIn(self.caption("A longer cutoff does not prove meromorphic continuation",y=-1.9,size=28,color=DIM)),run_time=.75)
        self.wipe()

    def anchor(self):
        with self.narrate("anchor") as n:
            title=self.heading("The extra plain real reading stays in the estimate")
            self.play(FadeIn(M("|I<sub>H</sub>| + Re(I<sub>0</sub>) ≤ window budget",size=43,color=PRED).move_to([0,.9,0])),run_time=.9)
            n.at(2);self.play(FadeIn(math_label("separate model: |Re(I₀)| ≤ anchor bound",size=36,color=TRUTH).move_to([0,-.4,0])),run_time=.8)
            n.at(4)
            self.wipe(title)
            self.sources(["lw-mellin-real-anchor-bound"],"the height-zero model bound","Pole-family mass + regular cap + comparison errors")
            n.at(5)
            self.wipe(title)
            self.play(FadeIn(math_label("Re(I₀) ≥ −anchor bound",size=42,color=TRUTH).move_to([0,.85,0])),run_time=.8)
            n.at(6);self.play(FadeIn(M("⇒ |I<sub>H</sub>| ≤ window budget + anchor bound",size=37,color=GOOD).move_to([0,-.55,0])),run_time=.85)
            n.at(7);self.play(FadeIn(self.caption("Two compatible models · selected height and height zero",size=27,color=DIM)),run_time=.75)
        self.wipe()

    def budget(self):
        with self.narrate("budget") as n:
            title=self.heading("Choose the index, then the numerical precision")
            self.play(FadeIn(self.chip("strict distance / radius < 1",PRED,width=8).move_to([0,.8,0])),run_time=.8)
            n.at(2);self.play(FadeIn(self.chip("computed geometric thresholds → enough index",GOOD,width=10).move_to([0,-.6,0])),run_time=.8)
            n.at(3)
            self.wipe(title)
            self.sources(["lw-mellin-window-decay-index"],"combine three geometric index requirements","Window, real anchor and regular part; distance < every relevant radius")
            n.at(4)
            self.wipe(title)
            self.sources(["lw-mellin-model-error-precision"],"precision after the scale is fixed","scale ≥ 0 · error = 1/[128(1+scale)]")
            n.at(6)
            self.wipe(title)
            self.play(FadeIn(self.chip("uniform caps and clearances → index → precision",TRUTH,width=11.6).move_to([0,.65,0])),run_time=.85)
            n.at(7);self.play(FadeIn(self.caption("A cap that secretly depends on the requested precision can create a loop",y=-1,size=26,color=DIM)),run_time=.75)
        self.wipe()

    def contradiction(self):
        with self.narrate("contradiction") as n:
            title=self.heading("One normalized reading cannot satisfy separated bounds")
            ruler=RationalRuler(0,1,[(0,"0"),(.5,"1/2"),(.75,"3/4"),(1,"1")],y=.2)
            self.play(FadeIn(ruler),run_time=.8)
            n.at(1);lower=Line(ruler.point(.75),ruler.point(1),color=TRUTH,stroke_width=11);self.play(Create(lower),FadeIn(self.caption("illustrative lower bound: value ≥ 3/4",y=1.45,size=31,color=TRUTH)),run_time=.85)
            n.at(2);upper=Line(ruler.point(0),ruler.point(.5),color=PRED,stroke_width=11);self.play(Create(upper),FadeIn(self.caption("illustrative upper bound: value ≤ 1/2",y=-1.15,size=31,color=PRED)),run_time=.85)
            n.at(3);self.play(FadeIn(self.caption("3/4 > 1/2 → no compatible value",size=33,color=GOOD)),run_time=.8)
            n.at(4)
            self.wipe(title)
            self.popup("video-eight-separated-bounds","Teaching theorem: lower = pole − remainder > upper",kind="defthm",page_size=9)
            n.at(6)
            self.wipe(title)
            self.play(FadeIn(self.chip("accepted models + computed budgets + failed search",PRED,width=11.3).move_to([0,.8,0])),run_time=.8)
            n.at(7);self.play(FadeIn(math_label("contradiction → search succeeds",size=43,color=GOOD).move_to([0,-.6,0])),run_time=.85)
        self.wipe()

    def witness(self):
        with self.narrate("witness") as n:
            title=self.heading("The conditional conclusion returns a rational address")
            self.play(FadeIn(self.chip("actual finite search result → computed address x",PRED,width=10.7).move_to([0,1.1,0])),run_time=.8)
            n.at(3);self.play(FadeIn(math_label("Y ≤ x    and    x² ≤ Y³",size=46,color=TRUTH).move_to([0,-.05,0])),run_time=.85)
            n.at(5);self.play(FadeIn(math_label("returned signal interval: lower endpoint > 0",size=34,color=GOOD).move_to([0,-1.3,0])),run_time=.8)
            n.at(6);self.play(FadeIn(self.caption("lw-mellin-computed-budget-window-witness · conditional theorem",size=23,color=DIM)),run_time=.7)
        self.wipe()

    def scope(self):
        with self.narrate("scope") as n:
            title=self.heading("A certified conditional chain, with explicit remaining work")
            proven=VGroup(*[self.chip(t,GOOD,width=10.5) for t in ["finite geometry and box checks","constructed models and coefficient comparisons","conditional contradiction and returned witness"]]).arrange(DOWN,buff=.3).move_to([0,.1,0]);self.play(FadeIn(proven),run_time=1)
            n.at(3)
            self.wipe(title)
            remaining=VGroup(*[self.chip(t,TRUTH,width=11.5) for t in ["general analytic models and complete zero covers","uniform compatible caps as precision varies","full statement and Peano Arithmetic interpretation"]]).arrange(DOWN,buff=.32).move_to([0,.2,0]);self.play(FadeIn(remaining),run_time=1)
            n.at(7);self.play(FadeIn(self.caption("No claim of a completed Riemann Hypothesis proof in Peano Arithmetic",size=23,color=DIM)),run_time=.75)
        self.wipe()

    def next(self):
        with self.narrate("next") as n:
            title=self.heading("The final episode follows the completed proof milestone")
            self.play(FadeIn(self.caption("Part Nine · The completed ACL2 reduction",y=1,size=35,color=TRUTH)),run_time=.9)
            n.at(2);chain=VGroup(*[self.chip(t,c,width=2.8) for t,c in [("geometry",PRED),("models",TRUTH),("comparison",PRED),("witness",GOOD)]]).arrange(RIGHT,buff=.25).move_to([0,-.45,0]);self.play(FadeIn(chain[0]),run_time=.6)
            for i in range(1,4):n.at_phrase(2,i);self.play(FadeIn(chain[i]),run_time=.6)
            n.at(4);self.play(FadeIn(self.caption("landau-windows-acl2 · smaller, reviewable mathematical tasks",size=28,color=GOOD)),run_time=.8)
        self.wipe()
