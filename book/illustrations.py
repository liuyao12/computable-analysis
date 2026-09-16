#!/usr/bin/env python3
"""Reproducible mathematical GIFs. Bounds/geometry are exact Fractions;
only raster placement is floating point. No pi or trigonometry is needed
for the circle artwork: use the same rational parametrization as the book.
The cosine rectangles and endpoint are evaluated independently from rational
polygon area bounds; a separate quadratic illustrates secant derivatives.
"""
from __future__ import annotations
from fractions import Fraction as Q
from pathlib import Path
import hashlib, json
from PIL import Image, ImageDraw, ImageFont
from functools import lru_cache
from numerical_examples import Clock, directed, example, point, sector_bounds
ROOT=Path(__file__).resolve().parents[1]
W,H,SCALE=800,640,2
PAPER='#faf9f5'; INK='#27382f'; MUTED='#788478'; GREEN='#456d55'; AREA='#dce8d7'; GOLD='#a87a46'; GAP='#ede0c9'; AXIS='#b7beb0'

def font(size,serif=False):
    paths=([Path('/usr/share/fonts/truetype/dejavu/DejaVuSerif.ttf')] if serif else
           [Path('/usr/share/fonts/truetype/dejavu/DejaVuSans.ttf')])
    for p in paths:
        if p.exists():return ImageFont.truetype(str(p),size*SCALE)
    raise RuntimeError('Install fonts-dejavu-core to render the mathematical illustrations')
FONTS={s:font(s) for s in [14,16,18,20,22,24]};FONTS['title']=font(28,True);FONTS['math']=font(27,True)

def canvas(title,sub):
    im=Image.new('RGB',(W*SCALE,H*SCALE),PAPER);d=ImageDraw.Draw(im)
    text(d,(32,25),title,'title');text(d,(32,69),sub,16,MUTED)
    return im,d

def text(d,p,t,f=18,color=INK,anchor=None):d.text(tuple(int(SCALE*v) for v in p),t,font=FONTS[f],fill=color,anchor=anchor)
def line(d,pts,color=INK,width=2):d.line([(int(SCALE*x),int(SCALE*y)) for x,y in pts],fill=color,width=max(1,int(width*SCALE)),joint='curve')
def poly(d,pts,fill):d.polygon([(int(SCALE*x),int(SCALE*y)) for x,y in pts],fill=fill)
def tangent_intersection(a,b):
    x,y=point(a);z,w=point(b);det=x*w-y*z
    return ((w-y)/det,(x-z)/det)
def fmt(q):return f'{float(q):.7f}'
def frac(q):return str(q.numerator) if q.denominator==1 else str(q)

def circle_frame(n):
    u=Q(2,3);P=point(u)
    im,d=canvas('Subdivide, project, enclose the area','Equal vertical steps vⱼ = j u/n; projection from (−1,0)')
    def xy(p):return (374+285*float(p[0]),426-285*float(p[1]))
    O=xy((0,0));start=xy((1,0));end=xy(P)
    arc=[xy(point(u*Q(j,180))) for j in range(181)]
    full=[xy(point(Q(j,180))) for j in range(181)]
    poly(d,[O]+arc,AREA)
    grid=[u*Q(j,n) for j in range(n+1)];lower=upper=Q(0)
    for a,b in zip(grid,grid[1:]):
        pa,pb=point(a),point(b);v=tangent_intersection(a,b)
        poly(d,[xy(pa),xy(v),xy(pb)],GAP)
        line(d,[xy(pa),xy(v),xy(pb)],GOLD,2)
        line(d,[xy(pa),xy(pb)],GREEN,2)
        if n<=8:line(d,[O,xy(pa)],'#a6b59c',.8)
        lower+=(b-a)*(1+a*b)/((1+a*a)*(1+b*b))
        upper+=(b-a)/(1+a*b)
    line(d,[(55,426),(725,426)],AXIS,1)
    line(d,[(374,447),(374,114)],AXIS,1)
    line(d,full,'#b1baa7',1.2);line(d,arc,GREEN,2.8)
    line(d,[O,start],INK,1.4);line(d,[O,end],INK,1.4)
    # Every equal subdivision of the VERTICAL segment is projected to
    # the circle from (-1,0). These are not equal-angle subarcs.
    base=xy((-1,0)); top=xy((0,u))
    for v in grid:
        line(d,[base,xy(point(v))],'#9eaec0',.9)
    line(d,[O,top],GOLD,4)
    for j,v in enumerate(grid):
        q=xy((0,v)); r=xy(point(v))
        line(d,[(q[0]-6,q[1]),(q[0]+6,q[1])],GOLD,1.5)
        for centre,color in [(q,GOLD),(r,GREEN)]:
            radius=2.2 if n>8 else 3.5
            d.ellipse(((centre[0]-radius)*SCALE,(centre[1]-radius)*SCALE,
                       (centre[0]+radius)*SCALE,(centre[1]+radius)*SCALE),fill=color)
        if n<=4 and 0<j<n:text(d,(q[0]-55,q[1]-8),f'{j}u/{n}',14,GOLD)
    for q in [O,start,end,base]:
        d.ellipse(((q[0]-4)*SCALE,(q[1]-4)*SCALE,(q[0]+4)*SCALE,(q[1]+4)*SCALE),fill=GREEN)
    text(d,(O[0]-15,O[1]+15),'0',16);text(d,(start[0]-5,start[1]+15),'1',16)
    text(d,(54,445),'(−1,0)',16);text(d,(288,top[1]-27),'(0,u)',18,GOLD)
    text(d,(end[0]+13,end[1]-17),'P(u)',20)
    text(d,(485,351),'A(u)','math',GREEN)
    text(d,(33,489),f'n = {n}   |   u = 2/3   |   equally spaced on the vertical segment',18)
    line(d,[(34,532),(67,532)],GREEN,3);text(d,(79,520),'Inner area  '+directed(lower),18)
    line(d,[(34,565),(67,565)],GOLD,3);text(d,(79,553),'Outer area  '+directed(upper,upper=True),18)
    text(d,(456,520),'Inner ≤ A(u) ≤ outer',18)
    text(d,(456,553),'Gap  '+directed(upper-lower,upper=True),18,MUTED)
    text(d,(33,605),'P(u) = ((1 − u²)/(1 + u²), 2u/(1 + u²))',16,MUTED)
    return im,{'subarcs':n,'u':str(u),'point':[str(v) for v in P],'lower':str(lower),'upper':str(upper),
      'verticalPoints':[[str(Q(0)),str(v)] for v in grid],
      'projectedPoints':[[str(c) for c in point(v)] for v in grid],
      'projectionOrigin':['-1','0']}

@lru_cache(maxsize=1)
def cosine_curve():
    clock=Clock(8192)
    return [(Q(j,720),sum(clock.cosine(Q(j,720)))/2) for j in range(241)]

def cosine_frame(n):
    row,samples=example(n);t=Q(row['t']);h=t/n
    im,d=canvas('The cosine integral: two computations','C decreases: right rectangles below, left rectangles above')
    def xy(x,y):return (80+638*float(x/t),414-278*float(y))
    for j in range(n):
        a,b=j*h,(j+1)*h;lo=samples[j+1][0];hi=samples[j][1]
        poly(d,[xy(a,0),xy(a,lo),xy(b,lo),xy(b,0)],AREA)
        poly(d,[xy(a,lo),xy(a,hi),xy(b,hi),xy(b,lo)],GAP)
        line(d,[xy(a,hi),xy(b,hi)],GOLD,1.7)
        line(d,[xy(a,lo),xy(b,lo)],GREEN,1.7)
        if n<=16:line(d,[xy(a,0),xy(a,hi)],AXIS,.8)
    line(d,[xy(0,0),xy(t+Q(1,60),0)],AXIS,1)
    line(d,[xy(0,Q(-1,20)),xy(0,Q(11,10))],AXIS,1)
    line(d,[xy(x,y) for x,y in cosine_curve()],INK,2.6)
    text(d,(43,410),'0',16);text(d,(668,429),'t = 1/3',16)
    text(d,(48,127),'1',16);text(d,(706,250),'C',20)
    text(d,(274,340),'∫₀ᵗ C(x) dx','math',GREEN)
    text(d,(32,476),f'{n} cells  |  integral bounds (rectangles)',18)
    text(d,(32,506),'['+row['lowerDisplay']+', '+row['upperDisplay']+']',24,GREEN)
    text(d,(450,507),'Gap '+directed(Q(row['gap']),upper=True),18,MUTED)
    text(d,(32,550),'Independent endpoint bounds: S(t)/π',18)
    text(d,(32,577),'['+row['endpointLowerDisplay']+', '+row['endpointUpperDisplay']+']',22)
    text(d,(32,612),'Rational polygon evaluation; all displayed interval endpoints round outwards.',14,MUTED)
    return im,row

def secant_frame(n):
    x=Q(1,2);h=Q(1,4*n)
    def f(v):return 1-v*v/2
    right=(f(x+h)-f(x))/h;left=(f(x)-f(x-h))/h
    im,d=canvas('Concavity encloses the derivative','Right secant ≤ derivative ≤ left secant; convexity reverses the roles')
    def xy(v,y):return (80+638*float(v),422-278*float(y))
    curve=[xy(Q(j,240),f(Q(j,240))) for j in range(241)]
    line(d,[xy(0,0),xy(Q(21,20),0)],AXIS,1)
    line(d,[xy(0,0),xy(0,Q(11,10))],AXIS,1)
    for slope,color in [(right,GREEN),(left,GOLD)]:
        line(d,[xy(Q(0),f(x)-slope*x),xy(Q(1),f(x)+slope*(1-x))],color,2)
    line(d,curve,INK,2.6)
    for v,color in [(x-h,GOLD),(x,INK),(x+h,GREEN)]:
        xx,yy=xy(v,f(v));line(d,[xy(v,0),(xx,yy)],AXIS,1)
        d.ellipse(((xx-4)*SCALE,(yy-4)*SCALE,(xx+4)*SCALE,(yy+4)*SCALE),fill=color)
    text(d,(359,441),'x = 1/2',16)
    text(d,(37,482),'f(x) = 1 − x²/2',20)
    text(d,(448,482),'h = '+str(h),18)
    text(d,(37,523),'Right slope  '+directed(right),20,GREEN)
    text(d,(37,560),'Left slope   '+directed(left,upper=True),20,GOLD)
    text(d,(448,523),"f′(1/2) = −1/2",20)
    text(d,(448,560),'Gap '+directed(left-right,upper=True),18,MUTED)
    text(d,(32,612),'A derivative requires the secant gap to shrink; convexity alone allows corners.',14,MUTED)
    return im,{'h':str(h),'x':str(x),'lower':str(right),'upper':str(left),'gap':str(left-right),'derivative':'-1/2'}

def build(out=None):
    out=out or ROOT/'blueprint/web/reading/animations';out.mkdir(parents=True,exist_ok=True)
    # Remove obsolete concave-INTEGRAL artwork from rebuilds.
    for suffix in ['gif','png']:(out/('concave.'+suffix)).unlink(missing_ok=True)
    report={'arctan':[],'cosine':[],'secants':[],'arctanNormalization':'pi = 4 A(1)',
      'scope':'Exact rational educational bounds; not executions of the literal Lean stage programs.',
      'integrationAssumption':'monotone integrand; no concavity or Lipschitz bound required',
      'differentiationAssumption':'convex or concave function with shrinking secant gap',
      'numericalMethod':'Rational chord/tangent area clock; bounded inversion; independent endpoint and rectangle sums; outward binary and decimal rounding.'}
    for name,fn in [('arctan',circle_frame),('cosine',cosine_frame),('secants',secant_frame)]:
        frames=[]
        for n in [1,2,4,8,16,32]:
            im,r=fn(n);report[name].append(r)
            frames.append(im.resize((W,H),Image.Resampling.LANCZOS))
        pal=frames[0].quantize(colors=192)
        indexed=[im.quantize(palette=pal,dither=Image.Dither.NONE) for im in frames]
        indexed[0].save(out/(name+'.gif'),save_all=True,append_images=indexed[1:],duration=[1600,1500,1500,1500,1500,2600],loop=0,disposal=2,optimize=False)
        frames[2].save(out/(name+'.png'))
    report['cosineTable']=[example(n)[0] for n in [8,32,128,512]]
    for name in ['arctan','cosine','secants']:
        for a,b in zip(report[name],report[name][1:]):
            assert Q(a['lower'])<=Q(b['lower'])<=Q(b['upper'])<=Q(a['upper'])
    report['files']={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(out.iterdir()) if p.suffix in ('.gif','.png')}
    (out/'manifest.json').write_text(json.dumps(report,indent=2)+'\n')
    return report
if __name__=='__main__':build()
