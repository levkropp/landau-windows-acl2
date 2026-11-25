"""Part Five: recurring ceilings, one-sided readings, and competing scales."""
import math
import re
from html import escape
from lesson_scene import *
from lesson_source import PagedSourcePopup
from part_two import RationalRuler
from part_three import math_label as plain_math_label
from parts import WavePanel


SNAPSHOT=ROOT/".tools/acl2-part05"


def math_label(text,size=36,color=INK):
    # Use real superscript markup rather than an unrelated Canadian-script
    # slash glyph. Some Windows fonts draw missing-glyph boxes for that glyph.
    replacements={"³ᐟ²":"<sup>3/2</sup>","¹ᐟ²":"<sup>1/2</sup>",
                  "³ᐟ⁴":"<sup>3/4</sup>","xᶿ":"x<sup>θ</sup>"}
    if not any(token in text for token in replacements):return plain_math_label(text,size=size,color=color)
    markup=escape(text)
    for token,replacement in replacements.items():markup=markup.replace(token,replacement)
    return fitted(M(markup,size=size,color=color),12.3)


class KernelPicture(VGroup):
    """Relative shapes only; each kernel is divided by its own peak value."""
    def __init__(self,k=12,sigma=4):
        super().__init__()
        self.k=k;self.sigma=sigma
        self.axis=Line(self.point(0,0),self.point(7,0),color=DIM)
        self.ticks=VGroup(*[math_label(str(i),size=24,color=DIM).move_to(self.point(i,0)+DOWN*.32) for i in range(8)])
        a,b=self.point(3,0),self.point(4.5,0)
        self.window=Rectangle(width=b[0]-a[0],height=2.45,stroke_width=0,fill_color=GOOD,fill_opacity=.11).move_to((a+b)/2+UP*1.225)
        self.label=math_label("U = 3     3U/2 = 9/2",size=27,color=GOOD).move_to([0,1.45,0])
        self.curve=self.shape(k)
        self.add(self.window,self.axis,self.ticks,self.label,self.curve)

    def point(self,u,y):return np.array([-5.2+u*10.4/7,-1.6+2.3*y,0])

    def shape(self,k):
        peak=k/self.sigma
        def value(u):return 0 if u<=0 else math.exp(k*math.log(u/peak)-self.sigma*(u-peak))
        return polyline([self.point(u,value(u)) for u in np.linspace(0,7,190)],color=PRED,width=4)


class PartFive(LessonScene):
    manifest_file="manifest-part05.json"
    timing_file="timing-part05.json"
    review_label="PART FIVE · REVIEW 01"
    lesson_methods=("opening","complex","zeros","symmetry","ceiling","windows",
                    "recurring","theorem","contrary","logarithm","waves","transform",
                    "kernel","positive_part","readings","checked_readings","geometry",
                    "growth","threshold","rh","scope","next")

    def popup(self,name,note="",kind="defun",page_size=9):
        book=(".tools/acl2-part05/video/teaching-part05.lisp" if name.startswith("video-")
              else ".tools/acl2-part05/acl2/landau-bounds.lisp")
        popup=PagedSourcePopup(book,name,note,kind=kind,page_size=page_size)
        if popup.page_count!=1:raise ValueError(f"Unshown source pages for {name}: {popup.page_count}")
        self.play(FadeIn(popup,scale=.96),run_time=.8)
        return popup

    def chip(self,text,color=PRED,width=3.2):
        return super().chip(text.replace("Y³ᐟ²","Y^(3/2)"),color=color,width=width)

    def zero_map(self):
        picture=ZeroMap(corner=[-5.1,-2.15,0],x_len=4.5,y_len=3.9,x_range=(-.2,1.2),n_zeros=10)
        picture.x_title.become(T("real part",size=20,color=DIM).move_to(picture.x_title))
        return picture

    def opening(self):
        with self.narrate("opening") as n:
            title=self.heading("Why this signal matters")
            self.play(FadeIn(math_label("G_z(x) = S_z(x) − x ln x + (1 + γ)x",size=37,color=PRED).move_to([0,.65,0])),run_time=.8)
            n.at(1);self.play(FadeIn(self.caption("A finite evaluator with justified intervals",y=-.65,color=GOOD,size=28)),run_time=.7)
            n.at(3)
            self.wipe(title)
            chain=VGroup(self.chip("ceiling on G_z",GOOD,width=4),math_label("⇒",size=40),self.chip("zero-free region",TRUTH,width=4)).arrange(RIGHT,buff=.45).move_to([0,.3,0])
            self.play(FadeIn(chain[0]),run_time=.7);self.play(FadeIn(chain[1:]),run_time=.8)
            n.at(6);self.play(FadeIn(self.caption("Worked arithmetic examples · checked in ACL2",color=PRED,size=27)),run_time=.7)
            n.at(8);self.play(Transform(title,fitted(B("Part Five · Why a ceiling controls zeros",size=40)).move_to(title)),run_time=.8)
        self.wipe()

    def complex(self):
        with self.narrate("complex") as n:
            title=self.heading("A complex address has two coordinates")
            origin=np.array([-5,-1.4,0]);flat=origin+RIGHT*2.25;point=flat+UP*1.8
            axes=VGroup(Line(origin+LEFT*.3,origin+RIGHT*4.9,color=DIM),Line(origin+DOWN*.25,origin+UP*3,color=DIM))
            self.play(Create(axes),run_time=.8)
            n.at(1);horizontal=Arrow(origin,flat,buff=0,color=PRED);self.play(GrowArrow(horizontal),FadeIn(math_label("real part β",size=29,color=PRED).move_to([-2.6,-1.9,0])),run_time=.8)
            n.at(2);vertical=Arrow(flat,point,buff=0,color=TRUTH);self.play(GrowArrow(vertical),FadeIn(Dot(point,color=TRUTH)),FadeIn(math_label("height t",size=29,color=TRUTH).move_to([-4,1,0])),run_time=.8)
            n.at(3);self.play(FadeIn(math_label("ρ = β + i t",size=43,color=TRUTH).move_to([3,.7,0])),run_time=.75)
            n.at(4);self.play(FadeIn(math_label("i² = −1",size=37,color=PRED).move_to([3,-.55,0])),run_time=.7)
            n.at(6)
            self.wipe(title)
            flow=VGroup(self.chip("input address ρ",PRED,width=4),math_label("→",size=40),self.chip("output f(ρ)",TRUTH,width=4)).arrange(RIGHT,buff=.5).move_to([0,.7,0]);self.play(FadeIn(flow),run_time=.85)
            n.at(7);self.play(Transform(flow[2],self.chip("f(ρ) = 0 + 0i",GOOD,width=4).move_to(flow[2])),run_time=.85)
            n.at(8);self.play(FadeIn(self.caption("Both output coordinates must vanish",y=-.8,color=GOOD,size=29)),run_time=.7)
            n.at(9);self.play(FadeIn(self.caption("Dots mark input addresses where that happens",size=26)),run_time=.7)
        self.wipe()

    def zeros(self):
        with self.narrate("zeros") as n:
            title=self.heading("Zeta's zeros live at complex addresses")
            self.play(FadeIn(math_label("ζ(s) = 1 + 1/2ˢ + 1/3ˢ + 1/4ˢ + …",size=40,color=PRED).move_to([0,.65,0])),run_time=.85)
            n.at(1);self.play(FadeIn(math_label("This series: Re(s) > 1",size=31,color=TRUTH).move_to([0,-.65,0])),run_time=.7)
            n.at(3);self.play(FadeIn(self.caption("Analytic continuation extends the function; s = 1 is a pole",size=25,color=GOOD)),run_time=.75)
            n.at(5)
            self.wipe(title)
            picture=self.zero_map();self.play(FadeIn(picture),run_time=.9)
            right=lines("critical strip", "0 < Re(s) < 1",size=32,color=PRED).move_to([3,1,0]);self.play(FadeIn(right),run_time=.7)
            n.at(6);central=Line(picture.c2p(.5,0),picture.c2p(.5,55),color=TRUTH,stroke_width=3);self.play(Create(central),FadeIn(math_label("RH: Re(ρ) = 1/2",size=34,color=TRUTH).move_to([3,-.6,0])),run_time=.85)
            n.at(7);self.play(Indicate(picture.dots,color=TRUTH),run_time=.9)
            n.at(8);self.play(FadeIn(self.caption("Sample known zeros · a finite picture is not a proof for all zeros",size=23)),run_time=.7)
        self.wipe()

    def symmetry(self):
        with self.narrate("symmetry") as n:
            title=self.heading("The mirror reduces the question to one side")
            picture=self.zero_map();self.play(FadeIn(picture),run_time=.85)
            left=Dot(picture.c2p(.22,33),radius=.1,color=HYPO);right=Dot(picture.c2p(.78,33),radius=.1,color=HYPO)
            n.at(1);self.play(FadeIn(left),run_time=.65);self.play(Create(DashedLine(left.get_center(),right.get_center(),color=HYPO)),FadeIn(right),run_time=.8)
            n.at(2);self.play(FadeIn(lines("hypothetical", "reflected pair",size=29,color=HYPO).move_to([3.1,.9,0])),run_time=.7)
            n.at(4);self.play(FadeIn(math_label("β + i t  ↔  (1 − β) + i t",size=29,color=TRUTH).move_to([2.7,-.55,0])),run_time=.8)
            n.at(5);shade=Rectangle(width=picture.c2p(1,0)[0]-picture.c2p(.5,0)[0],height=picture.y_len,stroke_width=0,fill_color=GAPC,fill_opacity=.2).move_to((picture.c2p(.5,0)+picture.c2p(1,55))/2);self.play(FadeIn(shade),run_time=.75)
            n.at(6);self.play(FadeOut(left),FadeOut(right),run_time=.65)
            n.at(8);self.play(FadeIn(self.caption("Exclude every zero with real part greater than 1/2",size=28,color=GOOD)),run_time=.75)
        self.wipe()

    def ceiling(self):
        with self.narrate("ceiling") as n:
            title=self.heading("An upper ceiling leaves the lower side free")
            self.play(FadeIn(math_label("G_z(x) ≤ C xᶿ",size=51,color=GOOD).move_to([0,.55,0])),run_time=.8)
            n.at(4);self.play(FadeIn(math_label("C > 0       0 < θ < 1",size=35,color=TRUTH).move_to([0,-.75,0])),run_time=.7)
            n.at(6)
            self.wipe(title)
            rows=VGroup(math_label("16¹ᐟ² = 4",size=44,color=PRED),math_label("16³ᐟ⁴ = 8",size=44,color=TRUTH)).arrange(RIGHT,buff=1.8).move_to([0,.2,0]);self.play(FadeIn(rows[0]),run_time=.7);self.play(FadeIn(rows[1]),run_time=.7)
            n.at(8)
            self.wipe(title)
            plot=CeilingPlot(center=[0,-.55,0],width=11.2,height=3.6,top=2)
            gap=plot.curve(plot.gap,GAPC,3.5);ceiling=plot.curve(plot.ceiling,GOOD,4)
            self.play(Create(plot.axis),Create(gap),Create(ceiling),run_time=1.2)
            self.play(FadeIn(T("schematic · logarithmic horizontal scale",size=23,color=DIM).move_to([0,1.35,0])),run_time=.6)
            n.at(9);floor=plot.curve(-plot.ceiling,DIM,2);self.play(Create(DashedVMobject(floor,num_dashes=35)),run_time=.8)
            self.play(FadeIn(cross_mark(size=.25).move_to(plot.p(3.6,-1.25))),run_time=.55)
            n.at(10);self.play(FadeIn(self.caption("Upper bound only · no absolute-value bound assumed",color=GOOD,size=27)),run_time=.7)
        self.wipe()

    def windows(self):
        with self.narrate("windows") as n:
            title=self.heading("A window contains every point of an interval")
            self.play(FadeIn(math_label("[Y, Y³ᐟ²]",size=49,color=GOOD).move_to([0,.7,0])),run_time=.75)
            n.at(3)
            self.wipe(title)
            axis=RationalRuler(0,10,[(0,"0"),(4,"4"),(8,"8"),(10,"10")],y=-.3)
            band=axis.band(4,8,color=GOOD);label=math_label("Y = 4  ⇒  [4, 8]",size=37,color=GOOD).move_to([0,1.1,0]);self.play(FadeIn(axis),FadeIn(band),FadeIn(label),run_time=.9)
            for cue,left,right,extent in [(4,16,64,80),(5,64,512,600)]:
                n.at(cue)
                new=RationalRuler(0,extent,[(0,"0"),(left,str(left)),(right,str(right))],y=-.3)
                self.play(Transform(axis,new),Transform(band,new.band(left,right,color=GOOD)),Transform(label,math_label(f"Y = {left}  ⇒  [{left}, {right}]",size=37,color=GOOD).move_to(label)),run_time=1.1)
            n.at(6);self.play(FadeIn(self.caption("Example addresses · not asserted good windows for G_z",y=-1.45,size=25,color=DIM)),run_time=.7)
            n.at(8);points=VGroup(*[Dot(new.point(t),radius=.055,color=TRUTH) for t in np.linspace(64,512,17)]);self.play(LaggedStart(*[FadeIn(p) for p in points],lag_ratio=.06),run_time=.9)
            n.at(9);self.play(FadeIn(self.caption("The hypothesis covers the full real interval",color=TRUTH,size=28)),run_time=.7)
        self.wipe()

    def recurring(self):
        with self.narrate("recurring") as n:
            title=self.heading("One fixed ceiling · arbitrarily large good windows")
            fixed=self.chip("Fix C > 0 and 0 < θ < 1",GOOD,width=7.5).move_to([0,1.15,0])
            n.at(1);self.play(FadeIn(fixed),run_time=.7)
            n.at(3);demand=self.chip("Any demanded threshold Y₀",PRED,width=8).move_to([0,-.1,0]);self.play(FadeIn(demand),run_time=.7)
            n.at(4);answer=self.chip("Some Y ≥ max(Y₀, 1): ceiling on [Y, Y³ᐟ²]",TRUTH,width=11.5).move_to([0,-1.4,0]);self.play(FadeIn(answer),run_time=.85)
            n.at(6)
            self.wipe(title)
            axis=Line([-5.6,-.1,0],[5.6,-.1,0],color=DIM)
            windows=VGroup(*[Rectangle(width=w,height=.65,stroke_color=GOOD,fill_color=GOOD,fill_opacity=.16).move_to([x,-.1,0]) for x,w in [(-4.5,.65),(-1.8,1.0),(2.2,1.55)]])
            self.play(Create(axis),FadeIn(windows),run_time=.85)
            threshold=Arrow([-3.6,-1.2,0],[-3.6,-.5,0],buff=0,color=PRED);self.play(GrowArrow(threshold),run_time=.6)
            n.at(7);self.play(threshold.animate.shift(RIGHT*4),run_time=1);self.play(Indicate(windows[2],color=GOOD),run_time=.7)
            n.at(9);self.play(FadeIn(self.caption("C stays fixed across the windows",y=1.05,color=GOOD,size=30)),run_time=.7)
            n.at(10);self.play(FadeIn(self.caption("Schematic locations · no upper limit on demanded thresholds",size=24)),run_time=.7)
        self.wipe()

    def theorem(self):
        with self.narrate("theorem") as n:
            title=self.heading("The classical windowed Landau bridge")
            self.play(FadeIn(math_label("C > 0,  0 < θ < 1",size=35,color=TRUTH).move_to([0,1.15,0])),run_time=.7)
            n.at(2);self.play(FadeIn(math_label("Arbitrarily large Y:  G_z(x) ≤ C xᶿ on [Y, Y³ᐟ²]",size=31,color=GOOD).move_to([0,0,0])),run_time=.85)
            n.at(3);self.play(FadeIn(math_label("⇒  ζ(s) ≠ 0 whenever Re(s) > θ",size=38,color=TRUTH).move_to([0,-1.25,0])),run_time=.85)
            n.at(4);self.play(FadeIn(self.caption("Zeros may lie on the boundary θ; the excluded side is strict",size=24)),run_time=.7)
            n.at(5)
            self.wipe(title)
            source=(SNAPSHOT/"lean/ZetaPoleData.lean").read_text(encoding="utf8")
            statement=re.search(r'theorem zeta_landau_windowed_unconditional[\s\S]*?:=\n',source).group(0).rsplit(":=",1)[0].rstrip()
            background=card(12.6,6.45,stroke=PRED)
            header=fitted(T("Lean theorem statement · proved in the soft layer",size=27,color=TRUTH),11.8).move_to([0,2.25,0])
            body=fitted(T(statement,size=27,font="Cambria Math"),11.5).move_to([0,-.05,0])
            footer=T("ZetaPoleData.lean · zeta_landau_windowed_unconditional",size=20,color=DIM).move_to([0,-2.7,0])
            self.play(FadeIn(VGroup(background,header,body,footer)),run_time=.9)
            n.at(8);self.play(Indicate(body,color=GOOD),run_time=1)
        self.wipe()

    def contrary(self):
        with self.narrate("contrary") as n:
            title=self.heading("A rogue zero forces violations in every late window")
            n.at(1);self.play(FadeIn(math_label("ζ(ρ) = 0,  β = Re(ρ) > θ",size=39,color=HYPO).move_to([0,.9,0])),run_time=.8)
            n.at(3);self.play(FadeIn(math_label("No arbitrarily large good windows for fixed C > 0",size=31,color=GAPC).move_to([0,-.15,0])),run_time=.8)
            n.at(4);self.play(FadeIn(math_label("∃ Y₀  ∀ Y ≥ Y₀  ∃ x ∈ [Y, Y³ᐟ²]:  G_z(x) > C xᶿ",size=29,color=TRUTH).move_to([0,-1.35,0])),run_time=.9)
            n.at(6)
            self.wipe(title)
            axis=RationalRuler(0,10,[(0,"0"),(3,"Y"),(8,"Y<sup>3/2</sup>")],y=-.4)
            band=axis.band(3,8,color=GOOD);self.play(FadeIn(axis),FadeIn(band),run_time=.8)
            self.play(FadeIn(Dot(axis.point(6.3)+UP*.32,color=GAPC,radius=.1)),FadeIn(T("at least one violation",size=29,color=GAPC).move_to([0,.95,0])),run_time=.8)
            n.at(8);self.play(FadeIn(self.caption("Existence so far · threshold and address not yet computed",size=25,color=TRUTH)),run_time=.75)
        self.wipe()

    def logarithm(self):
        with self.narrate("logarithm") as n:
            title=self.heading("Change the addresses, keep the same signal")
            n.at(1);self.play(FadeIn(math_label("x = eᵘ     u = ln x",size=46,color=PRED).move_to([0,1,0])),run_time=.8)
            n.at(2);self.play(FadeIn(math_label("ln(xy) = ln x + ln y",size=34,color=TRUTH).move_to([0,-.2,0])),run_time=.7)
            n.at(3)
            self.wipe(title)
            upper=self.chip("x:  [Y, Y³ᐟ²]",GOOD,width=7).move_to([0,1.15,0]);lower=self.chip("u:  [U, 3U/2]",PRED,width=7).move_to([0,-.65,0])
            self.play(FadeIn(upper),GrowArrow(Arrow([0,.55,0],[0,.05,0],buff=0,color=TRUTH)),FadeIn(lower),run_time=1)
            self.play(FadeIn(T("U = ln Y",size=27,color=TRUTH).move_to([4.7,.15,0])),run_time=.6)
            n.at(4);self.play(FadeIn(math_label("C xᶿ = C exp(θu)",size=32,color=GOOD).move_to([0,-2.1,0])),run_time=.7)
            n.at(5)
            self.wipe(title)
            self.play(FadeIn(math_label("g(u) = G_z(eᵘ)",size=49,color=TRUTH).move_to([0,.7,0])),run_time=.8)
            n.at(7);self.play(FadeIn(math_label("log-window width = 3U/2 − U = U/2",size=35,color=GOOD).move_to([0,-.8,0])),run_time=.75)
        self.wipe()

    def waves(self):
        with self.narrate("waves") as n:
            title=self.heading("A useful wave picture · then the cancellation problem")
            picture=WavePanel(center=[0,-.45,0],width=11.1,height=3.5,span=3,top=1.6,a0=.12,samples=210)
            wave=picture.curve(4,beta=.5,color=PRED)
            self.play(FadeIn(picture.box),Create(picture.axis),Create(wave),run_time=1.1)
            self.play(FadeIn(math_label("schematic mode: exp(βu) cos(tu + phase)",size=30,color=PRED).move_to([0,1.55,0])),run_time=.7)
            n.at(3);self.play(Transform(wave,picture.curve(4,beta=.75,color=HYPO)),Create(picture.envelope(.75,color=HYPO)),run_time=1.3)
            n.at(4);self.play(FadeIn(self.caption("β > θ: a faster envelope than the ceiling's growth scale",color=TRUTH,size=26)),run_time=.7)
            n.at(7)
            self.wipe(title)
            u,values=picture.values(4,beta=.5)
            second=polyline([picture.p(a,-.85*b) for a,b in zip(u,values)],color=HYPO,width=3)
            total=polyline([picture.p(a,.15*b) for a,b in zip(u,values)],color=TRUTH,width=4)
            self.play(FadeIn(picture.box),Create(picture.axis),Create(picture.curve(4,beta=.5,color=PRED)),Create(second),run_time=1.1)
            self.play(Create(total),FadeIn(T("Two schematic modes can nearly cancel",size=30,color=TRUTH).move_to([0,1.55,0])),run_time=.9)
            n.at(9);self.play(FadeIn(self.caption("The rigorous argument estimates the combined signal",size=27,color=GOOD)),run_time=.7)
        self.wipe()

    def transform(self):
        with self.narrate("transform") as n:
            title=self.heading("A transform takes weighted readings")
            flow=VGroup(self.chip("signal g(u)",PRED,width=3),self.chip("damping + phase",TRUTH,width=4),self.chip("integrate",GOOD,width=2.7)).arrange(RIGHT,buff=.45).move_to([0,.9,0])
            self.play(FadeIn(flow[0]),run_time=.6)
            n.at(1);self.play(FadeIn(flow[1:]),run_time=.85)
            self.play(FadeIn(math_label("Φ(s) = ∫₀∞ g(u) exp(−s u) du",size=39,color=TRUTH).move_to([0,-.5,0])),run_time=.8)
            n.at(3);self.play(FadeIn(math_label("s = σ + i t",size=33,color=PRED).move_to([0,-1.6,0])),run_time=.7)
            n.at(4);self.play(FadeIn(self.caption("Integral identity used here: Re(s) > 2",size=26,color=GOOD)),run_time=.7)
            n.at(6)
            self.wipe(title)
            self.play(FadeIn(math_label("Transform identity contains  −ζ′(s)/ζ(s)",size=35,color=PRED).move_to([0,1,0])),run_time=.8)
            n.at(7);self.play(FadeIn(math_label("ζ(ρ) = 0  ⇒  a pole of Φ at ρ",size=38,color=HYPO).move_to([0,-.15,0])),run_time=.8)
            n.at(8);self.play(FadeIn(math_label("Near ρ:   Φ(s) = c/(s − ρ) + h(s)",size=36,color=TRUTH).move_to([0,-1.35,0])),run_time=.8)
            self.play(FadeIn(self.caption("c ≠ 0 · h is analytic near ρ · ρ is a nontrivial zero",size=24,color=GOOD)),run_time=.65)
        self.wipe()

    def kernel(self):
        with self.narrate("kernel") as n:
            title=self.heading("Higher derivatives choose a concentrated reading")
            n.at(1);self.play(FadeIn(math_label("K_k(u) = uᵏ exp(−σu) / k!",size=43,color=PRED).move_to([0,.65,0])),run_time=.85)
            n.at(2);self.play(FadeIn(math_label("k! = 1 × 2 × … × k",size=32,color=TRUTH).move_to([0,-.65,0])),run_time=.7)
            n.at(3)
            self.wipe(title)
            picture=KernelPicture(k=12,sigma=4);self.play(FadeIn(picture),run_time=.9)
            counter=T("σ = 4,  k = 12: peak at 3",size=26,color=TRUTH).move_to([0,-2.55,0]);self.play(FadeIn(counter),run_time=.6)
            n.at(4)
            for k,text in [(15,"σ = 4,  k = 15: peak at 15/4"),(18,"σ = 4,  k = 18: peak at 9/2")]:
                self.play(Transform(picture.curve,picture.shape(k)),Transform(counter,T(text,size=26,color=TRUTH).move_to(counter)),run_time=1.2)
            n.at(5);self.play(Transform(picture.curve,picture.shape(15)),Transform(counter,T("Choose the order; bound inside mass and both tails",size=26,color=GOOD).move_to(counter)),run_time=1.1)
            n.at(6);self.play(FadeIn(self.caption("Each curve divided by its own peak · shapes, not absolute masses",size=22)),run_time=.7)
            n.at(9);left=Arrow(picture.point(1.4,.42),picture.point(2.1,.42),buff=0,color=GAPC);right=Arrow(picture.point(6,.42),picture.point(5.3,.42),buff=0,color=GAPC);self.play(GrowArrow(left),GrowArrow(right),run_time=.85)
        self.wipe()

    def positive_part(self):
        with self.narrate("positive_part") as n:
            title=self.heading("The one-sided cancellation starts with an identity")
            n.at(1);formula=math_label("|x| + x",size=56,color=TRUTH).move_to([0,.5,0]);self.play(FadeIn(formula),run_time=.75)
            n.at(2);self.play(Transform(formula,math_label("x ≥ 0:   |x| + x = 2x",size=44,color=PRED).move_to(formula)),run_time=.9)
            n.at(3);self.play(Transform(formula,math_label("x < 0:   |x| + x = −x + x = 0",size=42,color=GOOD).move_to(formula)),run_time=.9)
            n.at(4);self.play(Transform(formula,math_label("|x| + x = 2 max(x, 0)",size=48,color=TRUTH).move_to(formula)),run_time=.9)
            n.at(5)
            self.wipe(title)
            example=math_label("|−3| + (−3) = 0",size=49,color=GOOD).move_to([0,.5,0]);self.play(FadeIn(example),run_time=.7)
            n.at_phrase(5,1);self.play(Transform(example,math_label("|2| + 2 = 4",size=49,color=PRED).move_to(example)),run_time=.7)
            n.at_phrase(5,2);self.play(Transform(example,math_label("|−1| + (−1) = 0",size=49,color=GOOD).move_to(example)),run_time=.7)
            n.at(7)
            self.wipe(title)
            self.popup("video-positive-part","Rational input x · positive part is the larger of x and zero")
            n.at(8)
            self.wipe(title)
            self.popup("video-positive-part-identity","The rational identity · all signs of x allowed",kind="defthm",page_size=12)
            n.at(9)
            self.wipe(title)
            self.play(FadeIn(math_label("x ≤ R,  R ≥ 0  ⇒  max(x, 0) ≤ R",size=38,color=GOOD).move_to([0,.55,0])),run_time=.85)
            n.at(10);self.play(FadeIn(self.caption("No floor for x is required",y=-.9,color=TRUTH,size=31)),run_time=.7)
        self.wipe()

    def readings(self):
        with self.narrate("readings") as n:
            title=self.heading("Add a plain reading to a signed reading")
            def row(label,values,y,color):
                return VGroup(T(label,size=27,color=DIM).move_to([-4.7,y,0]),
                              *[math_label(str(value),size=36,color=color).move_to([x,y,0]) for x,value in zip([-1.7,1.2,4.1],values)])
            values=row("signal",[-3,2,-1],1.15,PRED);self.play(FadeIn(values),run_time=.8)
            n.at(1);weights=row("weight",[1,1,1],.3,DIM);self.play(FadeIn(weights),run_time=.7)
            n.at(2);self.play(FadeIn(math_label("plain = −3 + 2 − 1 = −2",size=31,color=TRUTH).move_to([0,-2.4,0])),run_time=.75)
            n.at(3);phases=row("phase",[1,-1,1],-.55,HYPO);self.play(FadeIn(phases),run_time=.7)
            n.at(4);products=row("product",[-3,-2,-1],-1.4,HYPO);self.play(FadeIn(products),run_time=.8)
            n.at(5)
            self.wipe(title)
            reading=math_label("|signed| = |−6| = 6",size=44,color=HYPO).move_to([0,.9,0]);self.play(FadeIn(reading),run_time=.75)
            n.at(6);combined=math_label("|signed| + plain = 6 + (−2) = 4",size=40,color=GOOD).move_to([0,-.55,0]);self.play(FadeIn(combined),run_time=.8)
            n.at(7)
            self.wipe(title)
            triangle=math_label("|x − y + z| ≤ |x| + |y| + |z|",size=40,color=PRED).move_to([0,.95,0]);self.play(FadeIn(triangle),run_time=.85)
            n.at(8);self.play(FadeIn(math_label("|signed| + plain ≤ 2 max(x,0) + 2 max(y,0) + 2 max(z,0)",size=28,color=GOOD).move_to([0,-.35,0])),run_time=.9)
            n.at(9);self.play(FadeIn(math_label("2 × (0 + 2 + 0) = 4",size=39,color=TRUTH).move_to([0,-1.65,0])),run_time=.7)
            n.at(10)
            self.wipe(title)
            self.play(FadeIn(math_label("signal:  −3, 2, −1    →    −10, 2, −1",size=36,color=PRED).move_to([0,1,0])),run_time=.8)
            self.play(FadeIn(math_label("6 + (−2) = 4    →    13 + (−9) = 4",size=39,color=GOOD).move_to([0,-.45,0])),run_time=.9)
            n.at(11);self.play(FadeIn(self.caption("Large negative values disappear from this upper bound",color=TRUTH,size=27)),run_time=.7)
        self.wipe()

    def checked_readings(self):
        with self.narrate("checked_readings") as n:
            title=self.heading("A checked finite model of the cancellation")
            plain=self.popup("video-plain-three","Add three rational signal values · all weights are one")
            n.at(1);self.play(Indicate(plain.body,color=TRUTH),run_time=.8)
            n.at(2)
            self.wipe(title)
            self.popup("video-signed-three","Fixed phases +1, −1, +1 · a real special case")
            n.at(4)
            self.wipe(title)
            theorem=self.popup("video-three-one-sided","Rational x, y, z · no lower bound on the signal values",kind="defthm",page_size=16)
            n.at(6);self.play(Indicate(theorem.body,color=TRUTH),run_time=.9)
            n.at(8)
            self.wipe(title)
            self.play(FadeIn(math_label("|oscillating reading| + plain reading ≤ one-sided budget",size=31,color=GOOD).move_to([0,.8,0])),run_time=.85)
            n.at(9);self.play(FadeIn(math_label("The extra real reading remains",size=38,color=TRUTH).move_to([0,-.55,0])),run_time=.8)
            n.at(10);self.play(FadeIn(self.caption("Further analytic control is required to bound the magnitude alone",size=24,color=PRED)),run_time=.75)
        self.wipe()

    def geometry(self):
        with self.narrate("geometry") as n:
            title=self.heading("The pole supplies a competing coefficient scale")
            center=np.array([1.6,-.5,0]);pole=center+LEFT*1.7;edge=center+LEFT*2.2
            n.at(1);point=Dot(center,color=PRED,radius=.08);boundary=Line(edge+UP*2.2,edge+DOWN*2.2,color=GOOD,stroke_width=2)
            self.play(FadeIn(point),Create(boundary),FadeIn(math_label("z = σ + i t",size=29,color=PRED).next_to(point,UP,buff=.6)),FadeIn(math_label("Re = θ",size=26,color=GOOD).move_to(edge+UP*2.45)),run_time=.9)
            n.at(2);self.play(FadeIn(math_label("Φ(z+h) = c₀ + c₁h + c₂h² + …",size=30,color=TRUTH).move_to([0,-3.05,0])),run_time=.8)
            n.at(3);self.play(FadeIn(Dot(pole,color=HYPO,radius=.1)),Create(Line(pole,center,color=HYPO)),FadeIn(math_label("ρ",size=29,color=HYPO).next_to(pole,DOWN,buff=.2)),FadeIn(math_label("d",size=28,color=HYPO).move_to((pole+center)/2+UP*.3)),run_time=.85)
            n.at(4);circle=Circle(radius=1.95,color=DIM,stroke_width=2).move_to(center);self.play(Create(circle),run_time=.9)
            n.at(5);self.play(FadeIn(math_label("d < E = σ − θ",size=34,color=GOOD).move_to([-3.7,-1,0])),run_time=.85)
            n.at(6)
            self.wipe(title)
            scales=VGroup(math_label("pole contribution scale:  1/dᵏ",size=38,color=HYPO),math_label("ceiling scale:  1/Eᵏ",size=38,color=GOOD),math_label("d < E  ⇒  (E/d)ᵏ grows",size=41,color=TRUTH)).arrange(DOWN,buff=.6).move_to([0,.15,0]);self.play(FadeIn(scales),run_time=1)
            n.at(7);self.play(FadeIn(self.caption("Schematic local geometry · not an actual zero certificate",size=24)),run_time=.7)
            n.at(8)
            self.wipe(title)
            obligations=VGroup(*[self.chip(text,color,width=9) for text,color in [("justify the enclosing circles",PRED),("bound every competing pole and remainder",TRUTH),("handle multiplicities and clusters",HYPO)]]).arrange(DOWN,buff=.35).move_to([0,-.1,0]);self.play(FadeIn(obligations[0]),run_time=.7)
            self.play(FadeIn(obligations[1]),run_time=.7)
            n.at(9);self.play(FadeIn(obligations[2]),run_time=.7)
        self.wipe()

    def growth(self):
        with self.narrate("growth") as n:
            title=self.heading("The estimates must eventually become incompatible")
            self.play(FadeIn(math_label("lower ≤ same coefficient ≤ upper",size=43,color=PRED).move_to([0,.75,0])),run_time=.8)
            n.at(1);self.play(FadeIn(math_label("lower > upper  ⇒  contradiction",size=39,color=GAPC).move_to([0,-.7,0])),run_time=.8)
            n.at(3)
            self.wipe(title)
            baseline=Line([-5,-1.65,0],[5,-1.65,0],color=DIM);target=Line([-5,.35,0],[5,.35,0],color=GOOD,stroke_width=2);self.play(Create(baseline),Create(DashedVMobject(target,num_dashes=35)),FadeIn(T("target 8",size=25,color=GOOD).move_to([-4.4,.7,0])),run_time=.8)
            xs=[-4.2,-1.5,1.2,3.9];data=[(0,1,"1"),(2,9/4,"9/4"),(4,81/16,"81/16"),(6,729/64,"729/64")]
            n.at(4)
            for phrase,(x,(k,value,label)) in enumerate(zip(xs,data)):
                n.at_phrase(4,phrase)
                h=value/4
                bar=Rectangle(width=.85,height=h,stroke_color=PRED,fill_color=PRED,fill_opacity=.25).move_to([x,-1.65+h/2,0])
                labels=VGroup(math_label(label,size=28,color=TRUTH).move_to([x,-1.4+h,0]),math_label("k = "+str(k),size=26,color=DIM).move_to([x,-2.1,0]))
                self.play(GrowFromEdge(bar,DOWN),FadeIn(labels),run_time=.8)
            n.at(5);self.play(FadeIn(self.caption("(3/2)⁶ = 729/64 > 8",size=32,color=GOOD)),run_time=.7)
            n.at(7);self.play(Transform(title,fitted(B("The growth mechanism still needs justified inputs",size=39)).move_to(title)),run_time=.8)
        self.wipe()

    def threshold(self):
        with self.narrate("threshold") as n:
            title=self.heading("Compute a sufficient order")
            self.play(FadeIn(math_label("some sufficiently large k",size=43,color=DIM).move_to([0,.5,0])),run_time=.7)
            n.at(1);self.play(FadeIn(math_label("→ a computed sufficient bound",size=38,color=GOOD).move_to([0,-.8,0])),run_time=.75)
            n.at(2)
            self.wipe(title)
            self.popup("lw-geometric-index","Rational base > 1 · rational target ≥ 0 · precision fuel from Part Four")
            n.at(4)
            self.wipe(title)
            self.play(FadeIn(self.code("(lw-geometric-index 3/2 8) → 17",size=35).move_to([0,.8,0])),run_time=.8)
            n.at(5);self.play(FadeIn(self.caption("Sufficient and conservative · not the first crossing",y=-.55,color=TRUTH,size=28)),run_time=.7)
            n.at(6)
            self.wipe(title)
            self.play(FadeIn(math_label("baseᵏ ≥ 1 + k(base − 1)",size=44,color=PRED).move_to([0,.85,0])),run_time=.8)
            n.at(7);self.play(FadeIn(math_label("1 + 17(3/2 − 1) = 19/2 > 8",size=41,color=GOOD).move_to([0,-.6,0])),run_time=.8)
            n.at(8)
            self.wipe(title)
            self.popup("video-geometric-demo","Every natural k ≥ 17 reaches the target · a certified project component",kind="defthm",page_size=18)
        self.wipe()

    def rh(self):
        with self.narrate("rh") as n:
            title=self.heading("Why every exponent just above 1/2 would suffice")
            self.play(FadeIn(math_label("For each 0 < ε < 1/2: recurring ceilings at θ = 1/2 + ε",size=30,color=GOOD).move_to([0,.75,0])),run_time=.85)
            n.at(2);self.play(FadeIn(self.caption("C may depend on ε · for that ε, C stays fixed across windows",y=-.5,size=25,color=TRUTH)),run_time=.7)
            n.at(3)
            self.wipe(title)
            axis=RationalRuler(.45,.85,[(.5,"1/2"),(.75,"β")],y=-.4);beta=Dot(axis.point(.75),color=HYPO,radius=.09);self.play(FadeIn(axis),FadeIn(beta),run_time=.8)
            n.at(4);self.play(FadeIn(math_label("ε = (β − 1/2)/2 > 0",size=36,color=PRED).move_to([0,1.1,0])),run_time=.75)
            n.at(5);middle=Dot(axis.point(.625),color=GOOD,radius=.09);self.play(FadeIn(middle),FadeIn(math_label("1/2 < θ = 1/2 + ε < β",size=35,color=GOOD).move_to([0,-1.65,0])),run_time=.8)
            n.at(6);self.play(Create(cross_mark(size=.3).move_to(beta)),run_time=.65)
            n.at(7)
            self.wipe(title)
            self.play(FadeIn(math_label("β = 3/4    ε = 1/8    θ = 5/8",size=40,color=TRUTH).move_to([0,.75,0])),run_time=.8)
            n.at(8);self.play(FadeIn(math_label("1/2 < 5/8 < 3/4 < 1",size=44,color=GOOD).move_to([0,-.65,0])),run_time=.75)
            n.at(9)
            self.wipe(title)
            self.popup("video-midpoint-gap","Rational β in (1/2,1) · choose ε halfway across the positive gap",kind="defthm",page_size=14)
            n.at(11)
            self.wipe(title)
            picture=self.zero_map();self.play(FadeIn(picture),FadeIn(lines("No right-side zeros", "+ reflection", "⇒ every zero on 1/2",size=29,color=GOOD).move_to([3.1,.15,0])),run_time=.9)
            n.at(12);self.play(FadeIn(self.caption("The recurring ceilings are inputs to this implication",size=25,color=TRUTH)),run_time=.7)
        self.wipe()

    def scope(self):
        with self.narrate("scope") as n:
            title=self.heading("Make the relevant existence steps explicit")
            n.at(1);classical=self.chip("classical bridge: ceilings ⇒ zero-free region",TRUTH,width=11).move_to([0,1,0]);self.play(FadeIn(classical),run_time=.8)
            n.at(2);arithmetic=self.chip("explicit bounds, finite computations, checked witnesses",PRED,width=11).move_to([0,-.3,0]);self.play(FadeIn(arithmetic),run_time=.8)
            n.at(4);composition=self.chip("interpretation + hypotheses + final composition",GOOD,width=11).move_to([0,-1.6,0]);self.play(FadeIn(composition),run_time=.8)
            n.at(6);self.play(FadeIn(self.caption("The target includes an arithmetic interpretation",size=26,color=GOOD)),run_time=.7)
            n.at(7)
            self.wipe(title)
            self.play(FadeIn(lines("This is one component to investigate.","Other reductions may be possible.","A full RH proof in Peano Arithmetic is not ruled out.",size=31,buff=.55,color=TRUTH).move_to([0,.1,0])),run_time=1)
        self.wipe()

    def next(self):
        with self.narrate("next") as n:
            title=self.heading("The bridge gives the evaluator a purpose")
            steps=VGroup(*[self.chip(text,color,width=9) for text,color in [("a recurring ceiling controls positive contributions",GOOD),("a concentrated reading gives a coefficient estimate",PRED),("a nearby pole forces a competing scale",HYPO)]]).arrange(DOWN,buff=.35).move_to([0,-.05,0])
            n.at(1);self.play(FadeIn(steps[0]),run_time=.7)
            n.at(2);self.play(FadeIn(steps[1]),run_time=.7)
            n.at(3);self.play(FadeIn(steps[2]),run_time=.7)
            n.at(4);self.play(FadeIn(self.caption("Contradiction after the geometry, tails, and constants are justified",size=23,color=TRUTH)),run_time=.7)
            n.at(6)
            self.wipe(title)
            self.play(FadeIn(math_label("Part Six · Explicit kernels and error budgets",size=39,color=TRUTH).move_to([0,.6,0])),run_time=.85)
            n.at(7);self.play(FadeIn(self.caption("Turn weighted readings into finite rational computations",y=-.85,size=29,color=GOOD)),run_time=.75)
        self.wipe()
