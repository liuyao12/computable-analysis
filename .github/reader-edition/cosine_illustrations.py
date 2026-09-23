#!/usr/bin/env python3
"""Source-rendered circle geometry with Computer Modern LaTeX labels.

The rational chord/tangent construction is retained from the pinned reader's
book/illustrations.py. Only raster positions use floating point.
"""
from fractions import Fraction as Q
from functools import lru_cache
from io import BytesIO
import hashlib
import matplotlib
matplotlib.use('Agg')
matplotlib.rcParams['mathtext.fontset'] = 'cm'
matplotlib.rcParams['savefig.transparent'] = True
from matplotlib.font_manager import FontProperties
from matplotlib.mathtext import math_to_image
from PIL import Image, ImageDraw

W,H,SCALE=800,640,2
PAPER='#faf9f5'; INK='#27382f'; MUTED='#788478'; GREEN='#456d55'; AREA='#dce8d7'; GOLD='#a87a46'; GAP='#ede0c9'; AXIS='#b7beb0'

@lru_cache(maxsize=512)
def label_image(label, size, color, serif):
    output=BytesIO()
    math_to_image(label, output, prop=FontProperties(family='DejaVu Serif' if serif else 'DejaVu Sans',size=size),
                  dpi=72*SCALE,format='png',color=color)
    output.seek(0)
    return Image.open(output).convert('RGBA')

def label(im, x, y, value, size=18, color=INK, serif=False):
    rendered=label_image(value,size,color,serif)
    im.paste(rendered,(round(x*SCALE),round(y*SCALE)),rendered)

def canvas(title,sub):
    im=Image.new('RGB',(W*SCALE,H*SCALE),PAPER)
    text(im,(32,25),title,'title');text(im,(32,69),sub,16,MUTED)
    return im,im

def text(im,p,t,f=18,color=INK):
    label(im,*p,t,{'title':28,'math':27}.get(f,f),color,f=='title')
def line(im,pts,color=INK,width=2):
    ImageDraw.Draw(im).line([(round(SCALE*x),round(SCALE*y)) for x,y in pts],fill=color,width=max(1,round(width*SCALE)),joint='curve')
def poly(im,pts,fill):
    ImageDraw.Draw(im).polygon([(round(SCALE*x),round(SCALE*y)) for x,y in pts],fill=fill)
def point(u):return ((1-u*u)/(1+u*u),2*u/(1+u*u))
def directed(q,upper=False):
    scale=10**7
    k=-(-q.numerator*scale//q.denominator) if upper else q.numerator*scale//q.denominator
    return f'{k//scale}.{k%scale:07d}'

def tangent_intersection(a,b):
    x,y=point(a);z,w=point(b);det=x*w-y*z
    return ((w-y)/det,(x-z)/det)

def circle_frame(stage):
    n=1 << stage
    u=Q(2,3);P=point(u)
    im,d=canvas('Subdivide, project, enclose the area',r'Equal vertical steps; projection from $(-1,0)$')
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
        lower+=(b-a)*(1+a*b)/((1+a*a)*(1+b*b))
        upper+=(b-a)/(1+a*b)
    line(d,[(55,426),(725,426)],AXIS,1)
    line(d,[(374,447),(374,114)],AXIS,1)
    line(d,full,'#b1baa7',1.2);line(d,arc,GREEN,2.8)
    # Every equal subdivision of the VERTICAL segment is projected to
    # the circle from (-1,0). These are not equal-angle subarcs.
    base=xy((-1,0)); top=xy((0,u))
    for v in grid:
        line(d,[base,xy(point(v))],'#9eaec0',.9)
    line(d,[O,top],GOLD,4)
    for v in grid:
        q=xy((0,v)); r=xy(point(v))
        line(d,[(q[0]-6,q[1]),(q[0]+6,q[1])],GOLD,1.5)
        for centre,color in [(q,GOLD),(r,GREEN)]:
            radius=2.2 if n>8 else 3.5
            ImageDraw.Draw(d).ellipse(((centre[0]-radius)*SCALE,(centre[1]-radius)*SCALE,
                       (centre[0]+radius)*SCALE,(centre[1]+radius)*SCALE),fill=color)
    for q in [O,start,end,base]:
        ImageDraw.Draw(d).ellipse(((q[0]-4)*SCALE,(q[1]-4)*SCALE,(q[0]+4)*SCALE,(q[1]+4)*SCALE),fill=GREEN)
    text(d,(O[0]-15,O[1]+15),'$0$',16);text(d,(start[0]-5,start[1]+15),'$1$',16)
    text(d,(54,445),'$(-1,0)$',16);text(d,(top[0]-6,top[1]-30),'$u$',18,GOLD)
    text(d,(end[0]+13,end[1]-17),'$P(u)$',20)
    text(d,(485,351),'$A(u)$','math',GREEN)
    text(d,(33,489),rf'$n = {stage}$    $u = 2/3$    Equally spaced on the vertical segment',18)
    line(d,[(34,532),(67,532)],GREEN,3);text(d,(79,520),'Inner area  $'+directed(lower)+'$',18)
    line(d,[(34,565),(67,565)],GOLD,3);text(d,(79,553),'Outer area  $'+directed(upper,upper=True)+'$',18)
    text(d,(456,520),r'$\mathrm{Inner} \leq A(u) \leq \mathrm{outer}$',18)
    text(d,(456,553),'Gap  $'+directed(upper-lower,upper=True)+'$',18,MUTED)
    text(d,(33,605),r'$P(u) = ((1-u^2)/(1+u^2),\, 2u/(1+u^2))$',16,MUTED)
    return im,{'stage':stage,'subarcs':n,'u':str(u),'point':[str(v) for v in P],'lower':str(lower),'upper':str(upper),
      'verticalPoints':[[str(Q(0)),str(v)] for v in grid],
      'projectedPoints':[[str(c) for c in point(v)] for v in grid],
      'projectionOrigin':['-1','0']}


def make_circle_animation(out):
    out.mkdir(parents=True,exist_ok=True)
    frames=[];rows=[]
    for stage in range(1,5):
        im,row=circle_frame(stage);rows.append(row)
        frames.append(im.resize((W,H),Image.Resampling.LANCZOS))
    palette=frames[0].quantize(colors=192)
    indexed=[im.quantize(palette=palette,dither=Image.Dither.NONE) for im in frames]
    indexed[0].save(out/'arctan.gif',save_all=True,append_images=indexed[1:],
                    duration=[1600]*3+[2800],loop=0,disposal=2,optimize=False)
    frames[2].save(out/'arctan.png')
    for a,b in zip(rows,rows[1:]):
        assert Q(a['lower'])<=Q(b['lower'])<=Q(b['upper'])<=Q(a['upper'])
    return dict(frames=rows,mathFont='Computer Modern',stageConvention='subarcs = 2**n',
                gifSha256=hashlib.sha256((out/'arctan.gif').read_bytes()).hexdigest(),
                posterSha256=hashlib.sha256((out/'arctan.png').read_bytes()).hexdigest())
