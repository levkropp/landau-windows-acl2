"""Part Three: a finite scan, grid coverage, and a conditional success proof."""
from fractions import Fraction
from lesson_scene import *
from lesson_source import PagedSourcePopup
from part_two import RationalRuler


ADDRESSES=[Fraction(i,8) for i in range(9)]
VALUES=[1-4*abs(x-Fraction(7,16)) for x in ADDRESSES]
SAMPLES=[(v-Fraction(1,8),v+Fraction(1,8)) for v in VALUES]


def math_label(text,size=38,color=INK):
    return fitted(T(text,size=size,color=color,font="Cambria"),12.0)


class SamplePlot(VGroup):
    def __init__(self,addresses=ADDRESSES,values=VALUES,samples=SAMPLES,
                 labels=None,width=10.4,**kwargs):
        super().__init__(**kwargs)
        self.addresses=list(addresses);self.plot_width=width
        self.minimum=float(min(addresses));self.maximum=float(max(addresses))
        self.zero=-.2;self.vertical_scale=1.35
        self.threshold=Line([-width/2,self.zero,0],[width/2,self.zero,0],color=GAPC,stroke_width=2)
        self.axis=Line([-width/2,-2.25,0],[width/2,-2.25,0],color=FAINT)
        self.bars=VGroup();self.value_dots=VGroup();self.address_labels=VGroup()
        labels=labels or [str(x) for x in addresses]
        for i,(x,value,(lo,hi)) in enumerate(zip(addresses,values,samples)):
            color=GOOD if lo>0 else DIM
            self.bars.add(VGroup(Line(self.point(x,lo),self.point(x,hi),color=color,stroke_width=7),
                                Dot(self.point(x,lo),radius=.055,color=color),
                                Dot(self.point(x,hi),radius=.055,color=color)))
            self.value_dots.add(Dot(self.point(x,value),radius=.07,color=TRUTH))
            self.address_labels.add(math_label(labels[i],size=23,color=DIM).move_to([self.point(x,0)[0],-2.6,0]))
        self.add(self.threshold,self.axis,self.bars,self.value_dots,self.address_labels)

    def point(self,x,y):
        return np.array([-self.plot_width/2+(float(x)-self.minimum)/(self.maximum-self.minimum)*self.plot_width,
                         self.zero+float(y)*self.vertical_scale,0])

    def curve(self):
        return VMobject(color=PRED,stroke_width=3).set_points_as_corners(
            [self.point(0,Fraction(-3,4)),self.point(Fraction(7,16),1),self.point(1,Fraction(-5,4))])


class PartThree(LessonScene):
    manifest_file="manifest-part03.json"
    timing_file="timing-part03.json"
    review_label="PART THREE · REVIEW 01"
    lesson_methods=("opening","scan","search_code","result","soundness","termination",
                    "grid_code","mesh","coverage","drop_bound","precision","margin",
                    "complete","worked","failure","next")

    def popup(self,name,note="",kind="defun",page_size=7):
        popup=PagedSourcePopup("teaching-part03.lisp",name,note,kind=kind,page_size=page_size)
        self.play(FadeIn(popup,scale=.96),run_time=.8)
        return popup

    def grid(self,step=Fraction(1,8),y=-.35):
        count=int(1/step)+1
        return RationalRuler(0,1,[(float(i*step),str(i*step)) for i in range(count)],y=y)

    def opening(self):
        with self.narrate("opening") as n:
            title=self.heading("Find a certificate, and say where it is")
            self.play(FadeIn(self.chip("lower > threshold",GOOD,width=6).move_to([0,.65,0])),run_time=.7)
            n.at(1);self.play(FadeIn(math_label("Which address has a certified value?",size=34,color=TRUTH).move_to([0,-.65,0])),run_time=.7)
            n.at(3);self.play(FadeIn(self.caption("A loop can stop with no result",color=GAPC,size=29)),run_time=.6)
            n.at(4)
            self.wipe(title)
            stages=VGroup(*[self.chip(s,c,width=3.5) for s,c in [("build addresses",PRED),("scan intervals",TRUTH),("prove success",GOOD)]]).arrange(RIGHT,buff=.35).move_to([0,.25,0])
            self.play(FadeIn(stages[0]),run_time=.5)
            n.at_phrase(4,1);self.play(FadeIn(stages[1]),run_time=.5)
            n.at_phrase(4,2);self.play(FadeIn(stages[2]),run_time=.5)
            n.at(6)
            self.play(FadeIn(self.caption("One example: a peak between rational grid points",y=-1.4,color=TRUTH,size=28)),run_time=.65)
            n.at(9)
            self.play(Transform(title,fitted(B("Part Three · A finite search that must succeed",size=40)).move_to(title)),run_time=.8)
        self.wipe()

    def scan(self):
        with self.narrate("scan") as n:
            title=self.heading("Scan lower endpoints, from left to right")
            plot=SamplePlot(addresses=[0,1,2,3],values=VALUES[:4],samples=SAMPLES[:4],labels=["0","1","2","3"],width=9)
            self.play(FadeIn(plot),run_time=.85)
            self.play(FadeIn(self.caption("threshold = 0 · positions numbered from zero",y=1.65,size=25)),run_time=.6)
            n.at(2)
            focus=SurroundingRectangle(plot.bars[0],buff=.16,color=TRUTH)
            status=self.caption("[−7/8, −5/8]   lower = −7/8",color=TRUTH,size=28)
            self.play(Create(focus),FadeIn(status),run_time=.75)
            n.at(3);self.play(Transform(status,self.caption("−7/8 > 0 is false · continue",color=GAPC,size=28)),run_time=.65)
            n.at(4)
            self.play(Transform(focus,SurroundingRectangle(plot.bars[1],buff=.16,color=TRUTH)),Transform(status,self.caption("−3/8 > 0 is false · continue",color=GAPC,size=28)),run_time=.75)
            n.at(5)
            self.play(Transform(focus,SurroundingRectangle(plot.bars[2],buff=.16,color=GOOD)),Transform(status,self.caption("[1/8, 3/8]   lower = 1/8",color=GOOD,size=28)),run_time=.75)
            n.at(6);self.play(Indicate(plot.bars[2][1],color=GOOD),Transform(status,self.caption("1/8 > 0 · stop at this interval",color=GOOD,size=28)),run_time=.8)
            n.at(7);self.play(Indicate(plot.bars[3],color=GOOD),run_time=.9)
            n.at(9);self.play(Indicate(plot.address_labels[2],color=TRUTH),run_time=.9)
            n.at(10);self.play(Transform(status,self.caption("index 2 = third item · numerical address comes later",color=TRUTH,size=26)),run_time=.7)
        self.wipe()

    def search_code(self):
        with self.narrate("search_code") as n:
            self.heading("Define the scan before abbreviating its name")
            popup=self.popup("lw-first-above","Proper finite sample lists · nil is the failure result",page_size=5)
            n.at(2);focus=popup.focus(0);self.play(Create(focus),run_time=.6)
            n.at(4);self.play(Transform(focus,popup.focus(1)),run_time=.6)
            n.at(5);self.play(Transform(focus,popup.focus(2)),run_time=.6)
            n.at(6)
            self.play(Transform(focus,popup.focus(3)),Transform(popup.footer,T("caar samples = car (car samples): lower endpoint of the first interval",size=20,color=TRUTH).move_to(popup.footer)),run_time=.7)
            n.at(8);self.play(Transform(focus,popup.focus(4)),run_time=.6)
            n.at(9)
            self.play(FadeOut(focus),run_time=.3);popup.turn_page(self,1)
            n.at(10);focus=popup.focus(5);self.play(Create(focus),run_time=.6)
            n.at(11);self.play(Transform(popup.footer,T("let binds the recursive result to the local name found",size=23,color=TRUTH).move_to(popup.footer)),run_time=.65)
            n.at(13);self.play(Transform(focus,popup.focus(6)),run_time=.65)
            n.at(14);self.play(Transform(popup.footer,T("Tail index + 1 = index in the original list",size=25,color=GOOD).move_to(popup.footer)),run_time=.65)
            n.at(15)
            self.play(FadeOut(focus),ReplacementTransform(popup,popup.badge("(lw-first-above threshold samples)",(0,.1,0),width=10.5)),run_time=.9)
        self.wipe()

    def result(self):
        with self.narrate("result") as n:
            title=self.heading("The returned position and the sampled address")
            answer=self.code("'(0 1/8 . 3/8)",size=37).move_to([0,.7,0])
            n.at(1);self.play(FadeIn(answer),run_time=.65)
            n.at(2)
            self.play(Transform(answer,self.code("'(1 1/8 . 3/8)",size=37).move_to(answer)),run_time=.7)
            n.at_phrase(2,1);self.play(Transform(answer,self.code("'(2 1/8 . 3/8)",size=37).move_to(answer)),run_time=.7)
            n.at(4);self.play(FadeIn(math_label("result = (index . interval)",size=34,color=TRUTH).move_to([0,-.5,0])),run_time=.65)
            n.at(5)
            parts=VGroup(self.code("car result → 2",size=29),self.code("cdr result → '(1/8 . 3/8)",size=29)).arrange(DOWN,buff=.35).move_to([0,-1.9,0]);self.play(FadeIn(parts),run_time=.75)
            n.at(6);self.play(FadeIn(self.caption("nil = failure · 0 is a number, not false",color=GAPC,size=25)),run_time=.6)
            n.at(8)
            self.wipe(title)
            grid=self.grid();self.play(FadeIn(grid),run_time=.8)
            n.at(9);self.play(Indicate(grid.submobjects[2+2*2],color=TRUTH),run_time=.8)
            n.at(10);self.play(FadeIn(self.code("(nth 2 '(0 1/8 1/4 3/8 1/2 5/8 3/4 7/8 1))",size=25).move_to([0,1.05,0])),run_time=.7)
            n.at(11);self.play(FadeIn(Dot(grid.point(.25),color=GOOD,radius=.11)),FadeIn(math_label("index 2  →  address 1/4",size=39,color=GOOD).move_to([0,-1.7,0])),run_time=.8)
            n.at(12);self.play(FadeIn(self.caption("List position and grid coordinate are different objects",color=TRUTH,size=26)),run_time=.65)
        self.wipe()

    def soundness(self):
        with self.narrate("soundness") as n:
            title=self.heading("A returned certificate has to mean something")
            n.at(1)
            facts=VGroup(self.chip("index is natural",PRED,width=5.8),self.chip("index is within the list",PRED,width=5.8),self.chip("returned interval = nth sample",GOOD,width=8)).arrange(DOWN,buff=.3).move_to([0,-.2,0])
            self.play(FadeIn(facts[:2]),run_time=.75)
            n.at(2);self.play(FadeIn(facts[2]),run_time=.7)
            n.at(5)
            popup=self.popup("lw-encloses-values","At each position: the interval contains the corresponding rational value")
            n.at(6);focus=popup.focus(4);self.play(Create(focus),run_time=.65)
            n.at(7);self.play(Transform(focus,popup.focus(2)),run_time=.65)
            n.at(8);self.play(Transform(popup.footer,T("The evaluator must justify this enclosure premise",size=24,color=TRUTH).move_to(popup.footer)),run_time=.7)
            n.at(9)
            self.wipe(title)
            self.play(FadeIn(math_label("threshold < lower ≤ value",size=43,color=GOOD).move_to([0,.3,0])),run_time=.75)
            n.at(10)
            theorem=self.popup("lw-first-above-value-gt","Proof hints guide ACL2; the implication is the mathematical claim",kind="defthm",page_size=9)
            n.at(11);self.play(Indicate(theorem.body,color=GOOD),run_time=.9)
        self.wipe()

    def termination(self):
        with self.narrate("termination") as n:
            title=self.heading("Stopping is different from succeeding")
            remaining=VGroup(*[self.chip(str(k),PRED,width=1.2) for k in [4,3,2,1,0]]).arrange(RIGHT,buff=.55).move_to([0,.65,0])
            self.play(FadeIn(remaining[0]),run_time=.6)
            n.at(1);self.play(LaggedStart(*[FadeIn(x) for x in remaining[1:]],lag_ratio=.25),run_time=1.1)
            n.at(2);self.play(FadeIn(math_label("remaining list length decreases",size=33,color=TRUTH).move_to([0,-.65,0])),run_time=.7)
            n.at(4);self.play(FadeIn(self.caption("Termination permits the answer nil",color=GAPC,size=29)),run_time=.65)
            n.at(5)
            self.wipe(title)
            plot=SamplePlot(addresses=[0,1],values=[VALUES[0],VALUES[-1]],samples=[SAMPLES[0],SAMPLES[-1]],labels=["0","1"])
            self.play(FadeIn(plot),run_time=.8)
            n.at(6)
            self.play(Create(plot.curve()),FadeIn(Dot(plot.point(Fraction(7,16),1),color=TRUTH,radius=.1)),run_time=1)
            self.play(FadeIn(math_label("F(x) = 1 − 4|x − 7/16|",size=31,color=TRUTH).move_to([0,1.6,0])),run_time=.65)
            n.at(8);self.play(FadeIn(self.caption("Two endpoint samples · no qualifying lower endpoint · nil",color=GAPC,size=25)),run_time=.7)
            n.at(10);self.play(Indicate(plot.curve(),color=TRUTH),run_time=.9)
            n.at(11);self.play(Transform(title,fitted(B("Teaching example · the gap can hide a peak",size=40)).move_to(title)),run_time=.75)
        self.wipe()

    def grid_code(self):
        with self.narrate("grid_code") as n:
            title=self.heading("Build every address with exact arithmetic")
            self.play(FadeIn(math_label("count     start     step",size=38,color=TRUTH).move_to([0,.6,0])),run_time=.7)
            n.at(2);self.play(FadeIn(self.caption("count = 0 → empty list",y=-.7,color=PRED,size=29)),run_time=.6)
            n.at(4)
            popup=self.popup("video-uniform-grid","Teaching constructor · a natural count, rational start and step")
            focus=popup.focus(1);self.play(Create(focus),run_time=.6)
            n.at(5);self.play(Transform(focus,popup.focus(4)),run_time=.65)
            n.at(6)
            self.wipe(title)
            grid=self.grid();self.play(FadeIn(grid),FadeIn(self.code("(video-uniform-grid 9 0 1/8)",size=32).move_to([0,1.15,0])),run_time=.8)
            n.at(7);self.play(FadeIn(math_label("9 points, 8 gaps",size=35,color=GOOD).move_to([0,-1.55,0])),run_time=.65)
            n.at(9)
            self.wipe(title)
            grid=self.grid(Fraction(1,2));call=self.code("(video-uniform-grid 3 0 1/2)",size=32).move_to([0,1.1,0])
            self.play(FadeIn(grid),FadeIn(call),run_time=.7)
            n.at_phrase(9,1);self.play(Transform(grid,self.grid(Fraction(1,4))),Transform(call,self.code("(video-uniform-grid 5 0 1/4)",size=32).move_to(call)),run_time=1)
            n.at_phrase(9,2);self.play(Transform(grid,self.grid()),Transform(call,self.code("(video-uniform-grid 9 0 1/8)",size=32).move_to(call)),run_time=1)
            n.at(10);self.play(FadeIn(self.caption("The project window grid has additional endpoint obligations",size=24,color=TRUTH)),run_time=.65)
        self.wipe()

    def mesh(self):
        with self.narrate("mesh") as n:
            title=self.heading("A checked list of bounded gaps")
            grid=self.grid();self.play(FadeIn(grid),run_time=.75)
            n.at(3)
            arrow=DoubleArrow(grid.point(.375)+UP*.45,grid.point(.5)+UP*.45,buff=0,color=TRUTH,tip_length=.12)
            self.play(Create(arrow),FadeIn(math_label("every gap ≤ mesh = 1/8",size=34,color=TRUTH).move_to([0,1.05,0])),run_time=.8)
            n.at(4)
            popup=self.popup("lw-meshp","cadr addresses selects the second address · nondecreasing order",page_size=5)
            n.at(5);popup.turn_page(self,1)
            n.at(6);self.play(Indicate(popup.body,color=TRUTH),run_time=.9)
            n.at(7)
            last=self.popup("lw-last-address","On a valid nonempty mesh: follow the tail to the final address")
            n.at(8);self.play(Indicate(last.body,color=TRUTH),run_time=.9)
            n.at(9)
            theorem=self.popup("video-uniform-grid-is-mesh","Positive count · rational start and step · nonnegative step",kind="defthm",page_size=10)
            n.at(10);self.play(Indicate(theorem.body,color=GOOD),run_time=.9)
            n.at(11);self.play(Transform(theorem.footer,T("Worked example: 9 points, start 0, step 1/8",size=24,color=GOOD).move_to(theorem.footer)),run_time=.7)
        self.wipe()

    def coverage(self):
        with self.narrate("coverage") as n:
            title=self.heading("Coverage comes from the gap bound")
            grid=self.grid();point=Dot(grid.point(7/16),color=TRUTH,radius=.1)
            self.play(FadeIn(grid),run_time=.75)
            n.at(1);self.play(FadeIn(point),FadeIn(math_label("point between the first and last address",size=31,color=TRUTH).move_to([0,1.1,0])),run_time=.75)
            n.at(2);self.play(point.animate.move_to(grid.point(.5)),run_time=.8)
            n.at(3);self.play(point.animate.move_to(grid.point(7/16)),run_time=.8)
            n.at(4)
            near=Dot(grid.point(.375),color=GOOD,radius=.095)
            self.play(FadeIn(near),Create(DoubleArrow(grid.point(.375)+DOWN*.65,grid.point(7/16)+DOWN*.65,buff=0,color=GOOD,tip_length=.09)),run_time=.8)
            n.at(5);self.play(FadeIn(math_label("distance = 1/16 ≤ mesh = 1/8",size=34,color=GOOD).move_to([0,-1.9,0])),run_time=.65)
            n.at(6)
            nearby=self.popup("lw-some-nearby","abs(address − point) is distance · look for at least one qualifying address")
            n.at(7);self.play(Indicate(nearby.body,color=TRUTH),run_time=.9)
            n.at(8);self.popup("lw-mesh-covers-point","Nonnegative mesh + sorted bounded gaps + point inside the span",kind="defthm",page_size=12)
            n.at(9)
            self.wipe(title)
            grid=self.grid();self.play(FadeIn(grid),FadeIn(Dot(grid.point(7/16),color=TRUTH,radius=.1)),run_time=.75)
            self.play(FadeIn(Dot(grid.point(.375),color=GOOD,radius=.095)),FadeIn(Dot(grid.point(.5),color=GOOD,radius=.095)),run_time=.65)
            self.play(FadeIn(math_label("3/8     <     7/16     <     1/2",size=36,color=TRUTH).move_to([0,1.1,0])),run_time=.65)
            n.at(11);self.play(FadeIn(self.caption("A nearby address still needs a lower bound on its value",size=26,color=TRUTH)),run_time=.65)
        self.wipe()

    def drop_bound(self):
        with self.narrate("drop_bound") as n:
            title=self.heading("Distance controls the possible loss in value")
            plot=SamplePlot();self.play(FadeIn(plot.threshold),FadeIn(plot.axis),Create(plot.curve()),run_time=.9)
            marker=Dot(plot.point(7/16,1),color=TRUTH,radius=.105)
            n.at(1);self.play(FadeIn(marker),FadeIn(math_label("peak = 1      rate = 4",size=33,color=TRUTH).move_to([0,1.65,0])),run_time=.75)
            n.at(3)
            self.play(marker.animate.move_to(plot.point(5/16,Fraction(1,2))),run_time=1.2)
            self.play(FadeIn(self.caption("distance 1/8 × rate 4 = possible loss 1/2",color=GOOD,size=27)),run_time=.65)
            n.at(5);self.play(FadeIn(math_label("A lower bound, not an equality requirement",size=28,color=PRED).move_to([0,-2.4,0])),run_time=.65)
            n.at(6)
            self.wipe(title)
            formula=math_label("value ≥ peak − rate × |address − point|",size=39,color=TRUTH).move_to([0,.5,0]);self.play(FadeIn(formula),run_time=.8)
            n.at(7)
            popup=self.popup("lw-lower-lipschitz","A supplied lower bound at every aligned rational address and value",page_size=5)
            n.at(9);self.play(Indicate(popup.body,color=PRED),run_time=.9)
            n.at(10);popup.turn_page(self,1)
            n.at(11);self.play(Indicate(popup.body,color=TRUTH),run_time=.9)
            n.at(12);self.play(Transform(popup.footer,T("The search uses this hypothesis; it does not establish it",size=23,color=TRUTH).move_to(popup.footer)),run_time=.7)
        self.wipe()

    def precision(self):
        with self.narrate("precision") as n:
            title=self.heading("Pay for spatial loss and numerical uncertainty")
            costs=VGroup(self.chip("rate × mesh",PRED,width=4.5),self.chip("interval width",TRUTH,width=4.5)).arrange(RIGHT,buff=.7).move_to([0,.4,0])
            n.at(1);self.play(FadeIn(costs),run_time=.75)
            n.at(2);self.play(Indicate(costs[0],color=PRED),run_time=.9)
            n.at(3);self.play(Indicate(costs[1],color=TRUTH),run_time=.9)
            n.at(4)
            popup=self.popup("lw-widths-at-most","Full width = upper − lower · compare with the supplied width budget")
            n.at(5);focus=popup.focus(3);self.play(Create(focus),run_time=.65)
            self.play(Transform(popup.footer,T("cdar samples = cdr(car samples): upper endpoint of the first interval",size=20,color=TRUTH).move_to(popup.footer)),run_time=.65)
            n.at(6);self.play(Transform(focus,popup.focus(4)),run_time=.65)
            n.at(7)
            self.wipe(title)
            axis=RationalRuler(.5,1,[(.625,"5/8"),(.75,"3/4"),(.875,"7/8")],y=-.4)
            self.play(FadeIn(axis),FadeIn(axis.band(.625,.875)),FadeIn(Dot(axis.point(.75),color=TRUTH,radius=.09)),run_time=.85)
            n.at(8);self.play(FadeIn(math_label("width = 7/8 − 5/8 = 1/4",size=36,color=TRUTH).move_to([0,1.05,0])),run_time=.7)
            n.at(9);self.play(FadeIn(math_label("radius = 1/8     width = 2 × radius",size=34,color=GOOD).move_to([0,-1.85,0])),run_time=.7)
            n.at(11);self.play(FadeIn(self.caption("Width matters only alongside a justified enclosure",color=GAPC,size=25)),run_time=.65)
        self.wipe()

    def margin(self):
        with self.narrate("margin") as n:
            title=self.heading("A strict margin pays both costs")
            inequality=math_label("peak > threshold + rate × mesh + width budget",size=38,color=TRUTH).move_to([0,.8,0]);self.play(FadeIn(inequality),run_time=.8)
            n.at(2)
            numbers=math_label("1 > 0 + 4 × (1/8) + 1/4",size=42,color=PRED).move_to([0,-.45,0]);self.play(FadeIn(numbers),run_time=.7)
            n.at(3);self.play(Transform(numbers,math_label("1 > 3/4",size=49,color=GOOD).move_to(numbers)),run_time=.75)
            n.at(4);self.play(FadeIn(self.caption("coverage → nearby address",y=-1.65,color=PRED,size=29)),run_time=.65)
            n.at(5);self.play(FadeIn(self.caption("value ≥ 1 − 1/2 = 1/2 > width budget 1/4",color=GOOD,size=27)),run_time=.7)
            n.at(6)
            value=self.popup("lw-some-value-above","Existence along a finite list of values")
            n.at(7)
            self.wipe(title)
            self.play(FadeIn(math_label("value > threshold + width budget",size=39,color=TRUTH).move_to([0,1,0])),run_time=.7)
            self.play(FadeIn(math_label("containment + width bound ⇒ lower > threshold",size=36,color=GOOD).move_to([0,-.5,0])),run_time=.7)
            n.at(9);lower=self.popup("lw-some-lower-above","At least one stored lower endpoint passes the threshold test")
            n.at(10);self.play(Indicate(lower.body,color=TRUTH),run_time=.9)
            n.at(11);theorem=self.popup("lw-first-above-complete","Non-nil search result iff at least one lower endpoint qualifies",kind="defthm")
            n.at(12);self.play(Indicate(theorem.body,color=GOOD),run_time=.9)
        self.wipe()

    def complete(self):
        with self.narrate("complete") as n:
            title=self.heading("The complete success theorem has hypotheses")
            theorem=self.popup("lw-grid-search-complete","Rational domains and the supplied parameters",kind="defthm",page_size=8)
            n.at(2);self.play(Indicate(theorem.body,color=PRED),run_time=.9)
            n.at(3);theorem.turn_page(self,1)
            n.at(4);self.play(Transform(theorem.footer,T("The point is inside the covered grid span",size=24,color=TRUTH).move_to(theorem.footer)),run_time=.65)
            n.at(5);self.play(Transform(theorem.footer,T("Strict peak margin pays rate × mesh and the full width budget",size=22,color=GOOD).move_to(theorem.footer)),run_time=.65)
            n.at(7);theorem.turn_page(self,2)
            self.play(Transform(theorem.footer,T("Transport + enclosures + width bounds ⇒ a successful scan",size=23,color=GOOD).move_to(theorem.footer)),run_time=.65)
            n.at(8);self.play(Indicate(theorem.body,color=GOOD),run_time=.9)
            n.at(9);self.play(Transform(theorem.footer,T(":hints guide proof search; they are not extra hypotheses",size=23,color=TRUTH).move_to(theorem.footer)),run_time=.65)
            n.at(10);theorem.turn_page(self,3)
            n.at(11);self.play(Transform(theorem.footer,T("A conditional success guarantee, with every premise stated",size=23,color=GOOD).move_to(theorem.footer)),run_time=.65)
            n.at(13)
            self.wipe(title)
            stages=VGroup(*[self.chip(s,c,width=3.6) for s,c in [("grid covers point",PRED),("value stays large",TRUTH),("interval certifies",GOOD)]]).arrange(RIGHT,buff=.3).move_to([0,.3,0]);self.play(FadeIn(stages),run_time=.85)
            n.at(14);self.play(FadeIn(self.caption("Rational theorem + explicit analytic interpretation",color=TRUTH,size=27)),run_time=.7)
        self.wipe()

    def worked(self):
        with self.narrate("worked") as n:
            title=self.heading("One example, all the hypotheses")
            plot=SamplePlot();self.play(FadeIn(plot),run_time=.9)
            n.at(1);self.play(Create(plot.curve()),FadeIn(Dot(plot.point(7/16,1),color=TRUTH,radius=.1)),run_time=.9)
            self.play(FadeIn(math_label("point = 7/16    peak = 1    rate = 4",size=29,color=TRUTH).move_to([0,1.65,0])),run_time=.7)
            n.at(3);self.play(Indicate(plot.value_dots,color=TRUTH),run_time=.9)
            n.at(4);self.play(FadeIn(self.caption("Every interval has width 1/4 and encloses its displayed value",size=24,color=TRUTH)),run_time=.7)
            n.at(6);self.play(Indicate(plot.bars[3],color=GOOD),Indicate(plot.bars[4],color=GOOD),run_time=.9)
            n.at(8)
            focus=SurroundingRectangle(plot.bars[0],buff=.14,color=TRUTH);self.play(Create(focus),run_time=.65)
            n.at_phrase(8,1);self.play(Transform(focus,SurroundingRectangle(plot.bars[1],buff=.14,color=TRUTH)),run_time=.65)
            n.at_phrase(8,2);self.play(Transform(focus,SurroundingRectangle(plot.bars[2],buff=.14,color=GOOD)),run_time=.65)
            n.at(9)
            self.play(Indicate(plot.address_labels[2],color=GOOD),run_time=.9)
            answer=self.code("result: '(2 1/8 . 3/8)   →   address 1/4",size=25,color=GOOD).move_to([0,-3.15,0])
            self.wipe(title,plot,focus)
            self.play(FadeIn(answer),run_time=.7)
            n.at(10);self.play(Indicate(plot.value_dots[2],color=TRUTH),run_time=.9)
            n.at(11);self.play(Indicate(plot.bars[2][1],color=GOOD),run_time=.9)
            n.at(12);self.play(Transform(title,fitted(B("The checked example agrees with the general guarantee",size=39)).move_to(title)),run_time=.8)
        self.wipe()

    def failure(self):
        with self.narrate("failure") as n:
            title=self.heading("A failed test is not a proof of a negative value")
            n.at(1);self.play(FadeIn(self.code("(lw-first-above 0 samples)  →  nil",size=31).move_to([0,1.1,0])),run_time=.75)
            n.at(3)
            axis=RationalRuler(-.25,.5,[(-.125,"−1/8"),(0,"0"),(.125,"1/8"),(.375,"3/8")],y=-.3)
            self.play(FadeIn(axis),FadeIn(axis.band(-.125,.375,color=GAPC)),FadeIn(Dot(axis.point(.125),color=TRUTH,radius=.1)),run_time=.85)
            self.play(FadeIn(math_label("value = 1/8 > 0",size=34,color=TRUTH).move_to([0,-1.55,0])),run_time=.7)
            n.at(5);self.play(FadeIn(self.caption("width = 1/2 · this positive value lacks the required margin",color=GAPC,size=24)),run_time=.7)
            n.at(6);self.play(Transform(title,fitted(B("Completeness applies when its hypotheses hold",size=40)).move_to(title)),run_time=.8)
            n.at(8)
            self.wipe(title)
            roles=VGroup(*[self.chip(s,c,width=3.5) for s,c in [("scan result",PRED),("accurate inputs",TRUTH),("success theorem",GOOD)]]).arrange(RIGHT,buff=.35).move_to([0,.3,0])
            self.play(FadeIn(roles),run_time=.85)
            n.at(10);self.play(FadeIn(self.caption("Keep each proof obligation explicit",size=30,color=TRUTH)),run_time=.65)
        self.wipe()

    def next(self):
        with self.narrate("next") as n:
            title=self.heading("Ready to supply the search with a signal")
            steps=VGroup(*[self.chip(s,c,width=7.5) for s,c in [("finite rational addresses",PRED),("interval certificates at those addresses",TRUTH),("a conditional theorem forcing success",GOOD)]]).arrange(DOWN,buff=.35).move_to([0,-.15,0])
            self.play(FadeIn(steps[0]),run_time=.65)
            n.at(1);self.play(FadeIn(steps[1]),run_time=.65)
            n.at(3);self.play(FadeIn(steps[2]),run_time=.65)
            n.at(5);self.play(FadeIn(self.caption("Next: construct the values and justify their bounds",color=TRUTH,size=27)),run_time=.7)
            n.at(7)
            self.wipe(title)
            self.play(FadeIn(math_label("Part Four · Prime powers and a smoothed signal",size=40,color=TRUTH).move_to([0,.4,0])),run_time=.8)
            n.at(9);self.play(FadeIn(self.caption("Keep the hypotheses and interpretation attached to the construction",size=24,color=GOOD)),run_time=.7)
        self.wipe()
