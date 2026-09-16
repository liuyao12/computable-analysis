#!/usr/bin/env python3
"""Reproducible mathematical GIFs. Bounds/geometry are exact Fractions;
only raster placement is floating point. No pi or trigonometry is needed
for the circle artwork: use the same rational parametrization as the book.
The concave illustration is an explicit quadratic, not a cosine evaluation.
"""
from __future__ import annotations
from fractions import Fraction as Q
from pathlib import Path
import hashlib, json
from PIL import Image, ImageDraw, ImageFont
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
def point(t):return ((1-t*t)/(1+t*t),2*t/(1+t*t))
def tangent_intersection(a,b):
    x,y=point(a);z,w=point(b);det=x*w-y*z
    return ((w-y)/det,(x-z)/det)
def fmt(q):return f'{float(q):.7f}'
def frac(q):return str(q.numerator) if q.denominator==1 else str(q)

def circle_frame(n):
    u=Q(2,3);P=point(u)
    im,d=canvas('Area before angle','A rational circle sector, with u = 2/3')
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
    # The secant from (-1,0) has rational slope u and crosses x=0 at y=u.
    line(d,[xy((-1,0)),end],'#99a497',1)
    for a in [O,start,end,xy((-1,0))]:
        d.ellipse((a[0]*SCALE-4*SCALE,a[1]*SCALE-4*SCALE,a[0]*SCALE+4*SCALE,a[1]*SCALE+4*SCALE),fill=GREEN)
    text(d,(O[0]-17,O[1]+14),'O',16);text(d,(start[0]-5,start[1]+15),'1',16)
    text(d,(72,446),'−1',16);text(d,(386,228),'u',20,GREEN)
    text(d,(end[0]+13,end[1]-17),'P(u)',20)
    text(d,(485,351),'A(u)','math',GREEN)
    text(d,(33,489),f'{n} rational subarc'+('' if n==1 else 's'),18)
    line(d,[(34,532),(67,532)],GREEN,3);text(d,(79,520),'Inner area  '+fmt(lower),18)
    line(d,[(34,565),(67,565)],GOLD,3);text(d,(79,553),'Outer area  '+fmt(upper),18)
    text(d,(456,520),'Inner ≤ A(u) ≤ outer',18)
    text(d,(456,553),'Gap  '+fmt(upper-lower),18,MUTED)
    text(d,(33,605),'P(u) = ((1 − u²)/(1 + u²), 2u/(1 + u²))',16,MUTED)
    return im,{'subarcs':n,'u':str(u),'point':[str(v) for v in P],'lower':str(lower),'upper':str(upper)}

def concave_frame(n):
    im,d=canvas('Concavity encloses the integral','Example: g(x) = 1 − x²/2, on [0,1]')
    def f(x):return 1-x*x/2
    def xy(x,y):return (80+638*float(x),438-290*float(y))
    curve=[xy(Q(j,240),f(Q(j,240))) for j in range(241)]
    poly(d,[xy(0,0)]+curve+[xy(1,0)],AREA)
    lower=upper=Q(0);h=Q(1,n)
    for j in range(n):
        a=j*h;b=(j+1)*h;m=(a+b)/2
        lo=[xy(a,f(a)),xy(b,f(b))]
        # For this illustrative quadratic the tangent is g(m)-m(x-m).
        # Its cell area is h*g(m), the midpoint upper bound. Numerical
        # midpoint construction uses only g(m), not any derivative oracle.
        ua=f(m)-m*(a-m);ub=f(m)-m*(b-m)
        poly(d,[xy(a,f(a)),xy(a,ua),xy(b,ub),xy(b,f(b))],GAP)
        line(d,[xy(a,ua),xy(b,ub)],GOLD,2.2);line(d,lo,GREEN,2.2)
        if n<=8:line(d,[xy(a,0),xy(a,ua)],AXIS,.8)
        lower+=h*(f(a)+f(b))/2;upper+=h*f(m)
    line(d,[xy(0,0),xy(Q(21,20),0)],AXIS,1)
    line(d,[xy(0,Q(-1,20)),xy(0,Q(11,10))],AXIS,1)
    line(d,curve,INK,2.6);text(d,(44,440),'0',16);text(d,(715,454),'1',16)
    text(d,(46,139),'1',16);text(d,(695,248),'g',20)
    text(d,(326,357),'∫ g','math',GREEN)
    text(d,(33,489),f'{n} equal cell'+('' if n==1 else 's'),18)
    line(d,[(34,532),(67,532)],GREEN,3);text(d,(79,520),'Chord sum  '+fmt(lower),18)
    line(d,[(34,565),(67,565)],GOLD,3);text(d,(79,553),'Midpoint sum  '+fmt(upper),18)
    text(d,(456,520),'Lower ≤ integral ≤ upper',18)
    text(d,(456,553),'Gap  '+fmt(upper-lower),18,MUTED)
    text(d,(33,605),'Supporting caps visualize the upper areas; midpoint values suffice.',14,MUTED)
    assert upper-lower==Q(1,8*n*n)
    assert lower<=Q(5,6)<=upper
    return im,{'cells':n,'lower':str(lower),'upper':str(upper),'gap':str(upper-lower),'integral':str(Q(5,6))}

def build(out=None):
    out=out or ROOT/'blueprint/web/reading/animations';out.mkdir(parents=True,exist_ok=True)
    report={'arctan':[],'concave':[],'arctanNormalization':'pi = 4 A(1)',
      'scope':'Exact rational geometry and bounds; educational raster illustrations, not new Lean certificates.',
      'concaveCaption':'Supporting lines are visual aids for this quadratic; midpoint area bound follows from concavity without differentiation.'}
    for name,fn in [('arctan',circle_frame),('concave',concave_frame)]:
        frames=[]
        for n in [1,2,4,8,16,32]:
            im,r=fn(n);report[name].append(r)
            frames.append(im.resize((W,H),Image.Resampling.LANCZOS))
        # One palette across frames prevents palette flicker; no external gifs.
        pal=frames[0].quantize(colors=192)
        indexed=[im.quantize(palette=pal,dither=Image.Dither.NONE) for im in frames]
        indexed[0].save(out/(name+'.gif'),save_all=True,append_images=indexed[1:],duration=[1400,1200,1200,1200,1200,2200],loop=0,disposal=2,optimize=False)
        frames[2].save(out/(name+'.png'))
    for a,b in zip(report['arctan'],report['arctan'][1:]):
        assert Q(a['lower'])<=Q(b['lower'])<=Q(b['upper'])<=Q(a['upper'])
    report['files']={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(out.iterdir()) if p.suffix in ('.gif','.png')}
    (out/'manifest.json').write_text(json.dumps(report,indent=2)+'\n')
    return report
if __name__=='__main__':build()
