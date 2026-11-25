"""The completed encoded-zero Landau reduction and its documented interpretation."""
import math,textwrap
from lesson_scene import *
from lesson_source import PagedSourcePopup
from function_popup import read_form
from part_two import RationalRuler
from part_five import math_label

SOURCE_FILES={
 "euler-window-encoded-zero":["lw-euler-window-approximate-zerop","lw-euler-window-encoded-zero-reduction"],
 "euler-continuation":["lw-complex-euler-continuation-value"],
 "euler-window-circle-pair":["lw-euler-window-prepare-circles","lw-euler-window-zero-sample-request"],
 "euler-window-ceiling-reduction":["lw-euler-window-ceiling-threshold"],
 "signal-continuity":["lw-landau-window-search","lw-landau-window-address"]}
SOURCE_LOOKUP={n:".tools/acl2-part09/acl2/"+b+".lisp" for b,names in SOURCE_FILES.items() for n in names}


class FinalSourceCard(VGroup):
    def __init__(self,names,title,note):
        super().__init__();lines=[]
        for name in names:
            if lines:lines.append("")
            for line in read_form(SOURCE_LOOKUP[name],"defun",name).splitlines():
                indent=len(line)-len(line.lstrip());lines.extend(textwrap.wrap(line,width=72,subsequent_indent=" "*(indent+2),break_long_words=False,break_on_hyphens=False,replace_whitespace=False) or [""])
        if len(lines)>17:raise ValueError(f"Split source card {names}: {len(lines)} lines")
        background=card(12.5,6.65,stroke=PRED);heading=fitted(T("ACL2 source · "+title,size=26,color=TRUTH),11.6).move_to([0,2.2,0])
        body=fitted(T("\n".join(lines),size=29,font="Consolas"),11.3)
        if body.height>3.45:body.scale_to_fit_height(3.45)
        body.move_to([0,-.1,0]);self.add(background,heading,body,fitted(T(note,size=22,color=DIM),11.4).move_to([0,-2.55,0]),T("Complete definitions · proof checkpoint 52aec9e",size=17,color=DIM).move_to([0,-3,0]))


class PartNine(LessonScene):
    manifest_file="manifest-part09.json";timing_file="timing-part09.json";review_label="PART NINE · COMPLETED REDUCTION"
    lesson_methods=("opening","contract","region","encoded","requests","euler","fixed","clearances","circles","scan","clusters","generated","coefficients","anchor","budgets","threshold","theorem","address","positive","quantifiers","coding","induction","audit","classical","scope","ending")

    def sources(self,names,title,note=""):
        panel=FinalSourceCard(names,title,note);self.play(FadeIn(panel,scale=.96),run_time=.8);return panel

    def steps(self,items,width=10.7,colors=None):
        colors=colors or [PRED]*len(items)
        return VGroup(*[self.chip(t,c,width=width) for t,c in zip(items,colors)]).arrange(DOWN,buff=.3).move_to([0,.15,0])

    def opening(self):
        with self.narrate("opening") as n:
            title=self.heading("The windowed Landau ceiling reduction is proved")
            self.play(FadeIn(B("Proved in Peano Arithmetic",size=40,color=GOOD).move_to([0,.9,0])),run_time=.8)
            n.at(1);self.play(FadeIn(self.caption("computed threshold · guaranteed search · rational violation",y=-.4,size=30,color=PRED)),run_time=.8)
            n.at(4);self.play(FadeIn(self.caption("Encoded zero data now generate the contour and budget inputs",y=-1.7,size=27,color=TRUTH)),run_time=.75)
            n.at(6);self.play(FadeIn(self.caption("Direct Peano Arithmetic manuscript · vanilla ACL2 certification",size=24,color=DIM)),run_time=.7)
            n.at(7);self.play(Transform(title,fitted(B("Part Nine · The completed ACL2 reduction",size=40)).move_to(title)),run_time=.8)
        self.wipe()

    def contract(self):
        with self.narrate("contract") as n:
            title=self.heading("A theorem with explicit inputs and a computed output")
            items=self.steps(["ceiling: C ≥ 0, rational θ = p/q, 0 ≤ θ < 1","rational region + sufficiently accurate small-value probe","computed Y₀ → every rational Y ≥ Y₀"],colors=[PRED,TRUTH,GOOD])
            self.play(FadeIn(items[0]),run_time=.8)
            n.at(2);self.play(FadeIn(items[1]),run_time=.8)
            n.at(3);self.play(FadeIn(items[2]),run_time=.8)
            n.at(6);self.play(FadeIn(self.caption("The proof establishes that its own finite search succeeds",size=28,color=GOOD)),run_time=.75)
        self.wipe()

    def region(self):
        with self.narrate("region") as n:
            title=self.heading("Choose a rational disk and reserve a strict margin")
            circle=Circle(radius=1.7,color=PRED).move_to([-3,-.1,0]);inner=Circle(radius=1.4,color=TRUTH).move_to(circle);center=Dot(circle.get_center(),color=GOOD)
            self.play(Create(circle),FadeIn(center),run_time=.9)
            self.play(FadeIn(T("center = 252 + i h",size=27,color=PRED).move_to([-3,-2.2,0])),run_time=.7)
            n.at(1);self.play(FadeIn(math_label("251 < cap < 252−θ",size=35,color=PRED).move_to([2.9,1.1,0])),run_time=.8)
            n.at(2);self.play(Create(inner),FadeIn(math_label("radius = cap−slack",size=35,color=TRUTH).move_to([2.9,-.15,0])),run_time=.9)
            n.at(4);self.play(FadeIn(self.caption("Positive real part throughout the disk · rational h and positive slack",size=24,color=GOOD)),run_time=.75)
            n.at(7);self.play(FadeIn(fitted(T("Schematic disk · quantitative constants",size=25,color=DIM),6).move_to([2.9,-1.55,0])),run_time=.7)
        self.wipe()

    def encoded(self):
        with self.narrate("encoded") as n:
            title=self.heading("Encode a zero through arbitrarily fine rational probes")
            self.play(FadeIn(math_label("∀ rational ε > 0:  ∃ rational offset u",size=37,color=TRUTH).move_to([0,1,0])),run_time=.85)
            n.at(2);self.play(FadeIn(math_label("u in the fixed disk · |native value(u,ε)| ≤ ε",size=32,color=PRED).move_to([0,-.35,0])),run_time=.85)
            n.at(3);self.play(FadeIn(self.caption("The rational offset may change with ε",y=-1.6,size=30,color=GOOD)),run_time=.75)
            n.at(5)
            self.wipe(title)
            self.sources(["lw-euler-window-approximate-zerop"],"the finite approximate-zero test","One requested precision; the encoded-zero condition quantifies over all positive rational requests")
        self.wipe()

    def requests(self):
        with self.narrate("requests") as n:
            title=self.heading("Fix the request and threshold before choosing the probe")
            boxes=self.steps(["1 · region + ceiling parameters","2 · prepared geometry, request r > 0, threshold Y₀","3 · obtain a probe at ε ≤ r/4"],colors=[PRED,TRUTH,GOOD])
            n.at(1);self.play(FadeIn(boxes[0]),run_time=.75)
            n.at(2);self.play(FadeIn(boxes[1]),run_time=.8)
            n.at(3);self.play(FadeIn(boxes[2]),run_time=.8)
            n.at(4);self.play(FadeIn(self.caption("Y₀ is independent of the later probe coordinates",size=29,color=TRUTH)),run_time=.75)
        self.wipe()

    def euler(self):
        with self.narrate("euler") as n:
            title=self.heading("The native target is the normalized zeta function")
            self.play(FadeIn(math_label("Z(s) = (s−1) ζ(s)  away from 1",size=43,color=PRED).move_to([0,1,0])),run_time=.85)
            n.at(2);self.play(FadeIn(math_label("Z(1)=1 · Z is entire",size=39,color=TRUTH).move_to([0,-.3,0])),run_time=.8)
            n.at(4);self.play(FadeIn(self.caption("Zeros of Z correspond to zeta zeros; no artificial zero at 1",y=-1.7,size=28,color=GOOD)),run_time=.75)
            n.at(5)
            self.wipe(title)
            self.sources(["lw-complex-euler-continuation-value"],"computed cutoff, point error and dyadic Euler prefix","Positive rational real part · rational height · positive rational request")
        self.wipe()

    def fixed(self):
        with self.narrate("fixed") as n:
            title=self.heading("Identify the limit through a fixed finite model")
            self.play(FadeIn(math_label("U_N(s) = (s−1) Σ n^(−s) + (N+1)^(1−s)",size=32,color=PRED).move_to([0,1,0])),run_time=.9)
            self.play(FadeIn(self.caption("sum n=1 through N · finite Dirichlet prefix + Euler correction",y=-.3,size=27,color=DIM)),run_time=.7)
            n.at(4)
            self.wipe(title)
            boxes=self.steps(["fixed cutoff → primitive rounding error tends to 0","fractional-part identity → corrected finite models tend to Z","native value V(s,ε):  |V(s,ε)−Z(s)| ≤ ε/4"],colors=[PRED,TRUTH,GOOD]);self.play(FadeIn(boxes[0]),run_time=.8)
            n.at(5);self.play(FadeIn(boxes[1]),run_time=.8)
            n.at(7);self.play(FadeIn(boxes[2]),run_time=.8)
            n.at(8);self.play(FadeIn(self.caption("Mathematical interpretation argument · distinct from the ACL2 certificate",size=24,color=DIM)),run_time=.7)
        self.wipe()

    def clearances(self):
        with self.narrate("clearances") as n:
            title=self.heading("Clearance bounds are now proved arithmetic inputs")
            real=self.chip("real axis: alternating terms + Euler correction",PRED,width=10.8).move_to([0,1,0]);right=self.chip("right of 1: finite Möbius weights + approximate inverse",TRUTH,width=11.6).move_to([0,-.4,0])
            n.at(1);self.play(FadeIn(real),run_time=.8)
            n.at(3);self.play(FadeIn(right),run_time=.8)
            n.at(5);self.play(FadeIn(self.caption("Computed positive floors and safe neighborhoods",y=-1.9,size=31,color=GOOD)),run_time=.75)
            n.at(7);self.play(FadeIn(self.caption("The diagram summarizes proved interfaces; it is not a zero certificate",size=24,color=DIM)),run_time=.7)
        self.wipe()

    def circles(self):
        with self.narrate("circles") as n:
            title=self.heading("Generate a checked contour from compatible local charts")
            center=np.array([-3,-.1,0]);circle=Circle(radius=1.55,color=PRED).move_to(center);self.play(Create(circle),run_time=.85)
            patches=VGroup(*[Circle(radius=.43,color=GOOD,stroke_opacity=.75).move_to(center+1.55*np.array([math.cos(a),math.sin(a),0])) for a in np.linspace(0,2*math.pi,12,endpoint=False)])
            n.at(1);self.play(LaggedStart(*[Create(c) for c in patches],lag_ratio=.06),run_time=1.4)
            n.at(3);self.play(FadeIn(lines("fixed coarse data","uniform positive floor","refinement-compatible caps",size=29,color=TRUTH).move_to([3,.5,0])),run_time=.9)
            n.at(5);self.play(FadeIn(self.caption("Finite integer counts · no exact irrational zero stored",size=28,color=GOOD)),run_time=.75)
            n.at(7);self.play(FadeIn(self.caption("Schematic local charts",y=-1.8,size=23,color=DIM).move_to([3,-1.8,0])),run_time=.7)
        self.wipe()

    def scan(self):
        with self.narrate("scan") as n:
            title=self.heading("A finite real-circle scan has two controlled outcomes")
            row=VGroup(*[self.chip(t,c,width=3.5) for t,c in [("count 0",GOOD),("count 0",GOOD),("positive count",TRUTH)]]).arrange(RIGHT,buff=.4).move_to([0,.75,0]);self.play(FadeIn(row[0]),run_time=.75)
            n.at(1);self.play(FadeIn(row[1]),run_time=.7)
            n.at(3);self.play(FadeIn(self.caption("outer empty circle → original probe supplies the modulated count",y=-.65,size=26,color=PRED)),run_time=.8)
            n.at(4);self.play(FadeIn(row[2]),run_time=.75)
            n.at(5);self.play(FadeIn(self.caption("first positive successor → compute an interior probe and modulation",y=-1.65,size=26,color=TRUTH)),run_time=.8)
            n.at(7);self.play(FadeIn(self.caption("Both cases return a compatible empty-real / positive-modulated pair",size=24,color=GOOD)),run_time=.75)
        self.wipe()

    def clusters(self):
        with self.narrate("clusters") as n:
            title=self.heading("Small values and finite counts also handle clusters")
            circle=Circle(radius=1.55,color=PRED).move_to([-3,-.1,0]);self.play(Create(circle),run_time=.8)
            dots=VGroup(*[Dot([-3+dx,-.1+dy,0],color=TRUTH,radius=.07) for dx,dy in [(-.25,.15),(-.03,.2),(.12,-.05),(.28,.05)]]);n.at(2);self.play(FadeIn(dots),run_time=.8)
            self.play(FadeIn(lines("positive count","small-value probe","checked clearance",size=32,color=GOOD).move_to([3,.45,0])),run_time=.8)
            n.at(4);self.play(FadeIn(self.caption("One multiple location and several nearby locations use the same interface",size=24,color=TRUTH)),run_time=.75)
            n.at(6);self.play(FadeIn(self.caption("No supplied exact isolated zero · illustrative dots only",y=-1.8,size=25,color=DIM).move_to([2.9,-1.8,0])),run_time=.7)
        self.wipe()

    def generated(self):
        with self.narrate("generated") as n:
            title=self.heading("The constructor now returns the needed paired data")
            self.sources(["lw-euler-window-prepare-circles"],"prepare both circle interfaces","Real scan result → case-dependent modulation → paired covers and request")
            n.at(4)
            self.wipe(title)
            fields=VGroup(*[self.chip(t,c,width=2.1) for t,c in [("height",PRED),("modulated",GOOD),("empty",GOOD),("real radius",TRUTH),("request",TRUTH)]]).arrange(RIGHT,buff=.3).move_to([0,.65,0]);self.play(LaggedStart(*[FadeIn(m) for m in fields],lag_ratio=.12),run_time=1.2)
            n.at(5)
            self.wipe(title)
            self.sources(["lw-euler-window-zero-sample-request"],"read the computed positive request","nth 4 reads the fifth field of the prepared list")
        self.wipe()

    def coefficients(self):
        with self.narrate("coefficients") as n:
            title=self.heading("The actual Mellin output and native coefficients now agree")
            boxes=self.steps(["actual improper Mellin evaluator I_j(εI)","native Euler coefficient A_j(s,εA)","distance allowance: 5 εI + εA/2"],colors=[PRED,TRUTH,GOOD]);self.play(FadeIn(boxes[0]),run_time=.8)
            n.at(1);self.play(FadeIn(boxes[1]),run_time=.8)
            n.at(2);self.play(FadeIn(self.caption("Coefficient orientation: evaluate at s−z",size=28,color=DIM)),run_time=.75)
            n.at(4);self.play(FadeIn(boxes[2]),run_time=.8)
            n.at(6);self.play(Transform(title,fitted(B("One compatible arithmetic chain",size=41)).move_to(title)),run_time=.75)
        self.wipe()

    def anchor(self):
        with self.narrate("anchor") as n:
            title=self.heading("Keep the real coefficient in the one-sided estimate")
            self.play(FadeIn(M("|A<sub>j</sub>(252+iH)| + Re(A<sub>j</sub>(252)) ≤ window allowance",size=33,color=PRED).move_to([0,.85,0])),run_time=.9)
            n.at(3);self.play(FadeIn(self.chip("empty real circle → separate real-anchor bound",TRUTH,width=10.8).move_to([0,-.5,0])),run_time=.8)
            n.at(5);self.play(FadeIn(self.caption("failed search → oscillating upper cap including the anchor allowance",y=-1.9,size=26,color=GOOD)),run_time=.8)
            n.at(7);self.play(FadeIn(self.caption("Schematic bound · all request allowances remain in the proved statement",size=23,color=DIM)),run_time=.7)
        self.wipe()

    def budgets(self):
        with self.narrate("budgets") as n:
            title=self.heading("Uniform caps make the precision choices noncircular")
            row=self.steps(["fixed coarse bounds and clearances","large enough coefficient index","fine factor and evaluator requests"],colors=[TRUTH,PRED,GOOD])
            self.play(FadeIn(row[0]),run_time=.8)
            n.at(4);self.play(FadeIn(row[1]),FadeIn(row[2]),run_time=.9)
            n.at(5);self.play(FadeIn(self.caption("The same bounds support every later refinement",size=30,color=GOOD)),run_time=.75)
            n.at(7);self.play(FadeIn(self.caption("Computed and certified · conservative bounds, no practical runtime promise",y=-1.95,size=25,color=DIM)),run_time=.75)
        self.wipe()

    def threshold(self):
        with self.narrate("threshold") as n:
            title=self.heading("Read the prepared pair and compute the window threshold")
            self.sources(["lw-euler-window-ceiling-threshold"],"the final threshold wrapper","Region + ceiling inputs; no later probe coordinate is an argument")
            n.at(4)
            self.wipe(title)
            self.play(FadeIn(math_label("region, C, p, q → r > 0 and positive integer Y₀",size=35,color=TRUTH).move_to([0,.8,0])),run_time=.85)
            n.at(5);self.play(FadeIn(self.caption("Validity theorems establish positivity and the required checks",y=-.65,size=28,color=GOOD)),run_time=.75)
        self.wipe()

    def theorem(self):
        with self.narrate("theorem") as n:
            panel=PagedSourcePopup(SOURCE_LOOKUP["lw-euler-window-encoded-zero-reduction"],"lw-euler-window-encoded-zero-reduction","The completed theorem · all hypotheses, conclusion and proof hints",kind="defthm",page_size=10)
            if panel.page_count!=3:raise ValueError(f"Revisit final theorem narration for {panel.page_count} pages")
            self.play(FadeIn(panel,scale=.96),run_time=.8)
            n.at(2);panel.turn_page(self,1)
            n.at(5);panel.turn_page(self,2)
        self.wipe()

    def address(self):
        with self.narrate("address") as n:
            title=self.heading("Run the existing search and decode its rational address")
            self.sources(["lw-landau-window-search","lw-landau-window-address"],"the actual search and address wrappers","The returned index selects an address on the constructed rational grid")
            n.at(3)
            self.wipe(title)
            self.play(FadeIn(math_label("Y ≤ x   and   x² ≤ Y³",size=48,color=TRUTH).move_to([0,1,0])),run_time=.85)
            n.at(5);self.play(FadeIn(self.caption("Exact squared comparison · no rounded square root",y=-.4,size=29,color=GOOD)),run_time=.75)
            n.at(6);ruler=RationalRuler(4,8,[(4,"4"),(6,"6"),(8,"8")],y=-1.65);self.play(FadeIn(ruler),FadeIn(Dot(ruler.point(6),color=GOOD)),run_time=.8)
            n.at(7);self.play(FadeIn(self.caption("Illustrative window geometry; not an execution of the final threshold",size=24,color=DIM)),run_time=.7)
        self.wipe()

    def positive(self):
        with self.narrate("positive") as n:
            title=self.heading("The returned positive lower endpoint proves the violation")
            self.play(FadeIn(M("[L,U] encloses Gz(x) − Cx<sup>p/q</sup>",size=41,color=PRED).move_to([0,1,0])),run_time=.85)
            n.at(3);self.play(FadeIn(math_label("L > 0 ⇒ true signal difference > 0",size=40,color=GOOD).move_to([0,-.25,0])),run_time=.85)
            n.at(5);self.play(FadeIn(math_label("illustrative [1/8,3/8] → difference ≥ 1/8",size=33,color=TRUTH).move_to([0,-1.55,0])),run_time=.8)
            n.at(6);self.play(FadeIn(self.caption("The theorem computes the actual endpoint; 1/8 is only an illustration",size=24,color=DIM)),run_time=.7)
        self.wipe()

    def quantifiers(self):
        with self.narrate("quantifiers") as n:
            title=self.heading("Instantiate the encoded zero at one computed precision")
            items=self.steps(["encoded zero: ∀ ε > 0, a suitable rational probe exists","choose the probe at ε = r/4","∀ rational Y ≥ Y₀: search returns a violation"],colors=[TRUTH,PRED,GOOD]);self.play(FadeIn(items[0]),run_time=.8)
            n.at(2);self.play(FadeIn(items[1]),run_time=.8)
            n.at(3);self.play(FadeIn(items[2]),run_time=.8)
            n.at(6);self.play(FadeIn(self.caption("Contrapositive: failed search above Y₀ excludes the encoded zero",size=26,color=TRUTH)),run_time=.75)
        self.wipe()

    def coding(self):
        with self.narrate("coding") as n:
            title=self.heading("Finite data can be represented by natural-number codes")
            entries=self.steps(["integer → sign and magnitude","rational → normalized numerator and denominator","complex pair / finite list / polynomial → finite codes"],colors=[PRED,TRUTH,GOOD]);n.at(1);self.play(FadeIn(entries[0]),run_time=.75)
            n.at(2);self.play(FadeIn(entries[1]),run_time=.75)
            n.at(4);self.play(FadeIn(entries[2]),run_time=.8)
            n.at(5);self.play(FadeIn(self.caption("Function graphs and hypotheses become arithmetic relations on codes",size=25,color=TRUTH)),run_time=.75)
        self.wipe()

    def induction(self):
        with self.narrate("induction") as n:
            title=self.heading("A direct proof in first-order Peano Arithmetic")
            self.play(FadeIn(B("The encoded Landau reduction: PROVED",size=38,color=GOOD).move_to([0,1.15,0])),run_time=.8)
            n.at(1);self.play(FadeIn(self.chip("coded finite computations and their arithmetic inequalities",PRED,width=11.5).move_to([0,-.15,0])),run_time=.85)
            n.at(3);self.play(FadeIn(self.caption("Ordinary induction on natural-valued measures",y=-1.5,size=29,color=TRUTH)),run_time=.75)
            n.at(4)
            self.wipe(title)
            self.play(FadeIn(self.chip("Section 14 · finite Mellin quadrature estimates",PRED,width=11).move_to([0,.9,0])),run_time=.85)
            n.at(5);self.play(FadeIn(self.chip("Theorem 15.2 · threshold and returned rational witness",TRUTH,width=11.6).move_to([0,-.45,0])),run_time=.85)
            n.at(6);self.play(FadeIn(self.caption("The classical zeta correspondence is also proved in the manuscript",y=-1.8,size=26,color=GOOD)),run_time=.75)
            n.at(7);self.play(FadeIn(self.caption("classical/pa-paper.tex · classical/pa-paper.pdf",size=25,color=DIM)),run_time=.7)
        self.wipe()

    def audit(self):
        with self.narrate("audit") as n:
            title=self.heading("The completion audit records the exact proof path")
            self.play(FadeIn(B("647 books · 3,649 exported theorems",size=40,color=GOOD).move_to([0,1,0])),run_time=.85)
            n.at(1);self.play(FadeIn(self.caption("Certificates present and fresh against their sources",y=-.2,size=28,color=PRED)),run_time=.75)
            n.at(2);self.play(FadeIn(self.caption("Final 558-book dependency closure imported successfully",y=-1.3,size=28,color=TRUTH)),run_time=.75)
            n.at(4);self.play(FadeIn(self.caption("Proof checkpoint 52aec9e · source hashes in docs/certification-audit.json",size=23,color=DIM)),run_time=.7)
        self.wipe()

    def classical(self):
        with self.narrate("classical") as n:
            title=self.heading("The classical comparison connects both ends")
            boxes=self.steps(["native sample V(s,ε) ↔ normalized zeta Z(s)","actual zero ↔ arbitrarily fine probes in a compact disk","positive returned endpoint → classical ceiling violation"],colors=[PRED,TRUTH,GOOD]);self.play(FadeIn(boxes[0]),run_time=.8)
            n.at(1);self.play(FadeIn(boxes[1]),run_time=.8)
            n.at(4);self.play(FadeIn(boxes[2]),run_time=.8)
            n.at(6);self.play(FadeIn(self.caption("Complete PA proof and zeta correspondence: classical/pa-paper.pdf",size=25,color=TRUTH)),run_time=.75)
        self.wipe()

    def scope(self):
        with self.narrate("scope") as n:
            title=self.heading("One essential Landau conversion, proved with less")
            self.play(FadeIn(B("Proved in Peano Arithmetic",size=40,color=GOOD).move_to([0,1,0])),run_time=.85)
            n.at(1);self.play(FadeIn(self.caption("computed threshold · success proof · certified rational witness",y=-.2,size=29,color=PRED)),run_time=.8)
            n.at(3);self.play(FadeIn(self.caption("Multiple and clustered zeros use the same constructed interface",y=-1.35,size=26,color=TRUTH)),run_time=.75)
            n.at(5);self.play(FadeIn(self.caption("Separate ceiling and a full RH proof in arithmetic remain separate questions",size=24,color=DIM)),run_time=.75)
        self.wipe()

    def ending(self):
        with self.narrate("ending") as n:
            title=self.heading("Read the theorem. Reproduce the certificate.")
            self.play(FadeIn(self.chip("theorem · audit · interpretation · worked lesson book",PRED,width=11).move_to([0,.9,0])),run_time=.85)
            n.at(3);self.play(FadeIn(self.caption("Vanilla ACL2 · reproducible certification instructions",y=-.4,size=29,color=GOOD)),run_time=.75)
            n.at(5)
            self.wipe(title)
            self.play(FadeIn(lines("From successor and induction","to a certified window violation",size=39,color=PRED).move_to([0,.65,0])),run_time=.9)
            n.at(7);self.play(FadeIn(B("Same conversion. Fewer assumptions.",size=39,color=TRUTH).move_to([0,-1.2,0])),run_time=.85)
            self.play(FadeIn(self.caption("landau-windows-acl2 · proved in Peano Arithmetic",size=27,color=GOOD)),run_time=.7)
        self.wipe()
