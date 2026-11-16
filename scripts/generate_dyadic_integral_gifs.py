#!/usr/bin/env python3
"""Animate exact rational cell bounds and certified sinc enclosures."""

import argparse
from fractions import Fraction as Q
from functools import lru_cache
import math
from pathlib import Path

from PIL import Image, ImageDraw, ImageFont

ROOT = Path(__file__).resolve().parents[1]
W, H = 920, 535
L, TOP, R, BOTTOM = 84, 94, 886, 389
INK, MUTED, PAPER = '#202f2d', '#51615b', '#faf9f5'
LOW, HIGH, TURN = '#a1430e', '#096b70', '#735298'


def font(size):
    return ImageFont.load_default(size=size)


def atan_bounds(q):
    total = sum((-1)**k * q**(2*k+1)/(2*k+1) for k in range(12))
    return total, total + q**25/25


a, b = atan_bounds(Q(1,5))
c, d = atan_bounds(Q(1,239))
PI_LO, PI_HI = 16*a - 4*d, 16*b - 4*c


@lru_cache(maxsize=None)
def series_bounds(x, cosine=False):
    """Consecutive sums after the alternating tail is decreasing."""
    term, total, k = Q(1), Q(1), 0
    while True:
        start = 2*k + (1 if cosine else 2)
        term = -term*x*x/(start*(start+1))
        if start > x and abs(term) <= Q(1, 2**32):
            return min(total, total+term), max(total, total+term)
        total += term
        k += 1


@lru_cache(maxsize=None)
def cosine_dyadic(t, bits):
    if t == 0 or t == Q(1,2) or t == 1:
        value = 1-2*t
        return value, value
    if t > Q(1,2):
        lo, hi = cosine_dyadic(1-t,bits)
        return -hi, -lo
    lo, hi = cosine_dyadic(2*t,bits)
    return root_interval((1+lo)/2,(1+hi)/2,bits)


def root_interval(lo, hi, bits):
    scale = 2**bits
    lower = math.isqrt(math.floor(lo*scale**2))
    upper = math.isqrt(math.floor(hi*scale**2))
    if Q(upper,scale)**2 < hi:
        upper += 1
    return Q(lower,scale), Q(upper,scale)


@lru_cache(maxsize=None)
def sinc_at(t, m):
    if t == 0:
        return Q(1), Q(1)
    if t.denominator == 1:
        return Q(0), Q(0)
    # Use geometry at dyadic angles, reflecting to the first quadrant.
    turn = t % 2
    phase = turn % 1
    u = min(phase,1-phase)
    bits = m + 10 + 2*t.denominator.bit_length()
    cp, cq = cosine_dyadic(2*u,bits)
    sin_lo, sin_hi = root_interval((1-cq)/2,(1-cp)/2,bits)
    if turn > 1:
        sin_lo, sin_hi = -sin_hi, -sin_lo
    quotients = [v/(p*t) for v in (sin_lo,sin_hi) for p in (PI_LO,PI_HI)]
    scale = 2**m
    return Q(math.floor(min(quotients)*scale),scale), Q(math.ceil(max(quotients)*scale),scale)


def sinc_cell(a, b, m, at):
    if b <= 1:
        return at(b)[0], at(a)[1], False
    midpoint = (a+b)/2
    center = midpoint*(PI_LO+PI_HI)/2
    end = PI_HI*b
    radius = max(center - PI_LO*a, end - center)
    cos_lo, cos_hi = series_bounds(center, True)
    sinc_lo, sinc_hi = series_bounds(center)
    error = end*radius          # |(x cos x - sin x)'| <= x.
    if center*(cos_hi-sinc_lo) + error <= 0:
        return at(b)[0], at(a)[1], False
    if 0 <= center*(cos_lo-sinc_hi) - error:
        return at(a)[0], at(b)[1], False
    lo, hi = sinc_at(midpoint,m)
    variation = PI_HI*(b-a)/4   # |f(t) - f(midpoint)| <= pi*|t-midpoint|/2.
    amplitude = 1/(PI_LO*a)
    return max(-amplitude, lo-variation), min(amplitude, hi+variation), True


def graph(n, cutoff, sinc):
    nodes = [Q(k,2**n) for k in range(cutoff*2**n+1)]
    m = n+4
    if sinc:
        at = lambda t: sinc_at(t,m)
        cells = [sinc_cell(a,b,m,at) for a,b in zip(nodes,nodes[1:])]
        xmax = cutoff + (1 if cutoff > 2 else 0)
        ymin, ymax = -.37, 1.06
    else:
        at = lambda t: ((value := 1/(1+t*t)),value)
        cells = [(at(b)[0],at(a)[1],False) for a,b in zip(nodes,nodes[1:])]
        xmax = cutoff
        ymin, ymax = .42, 1.07
    image = Image.new('RGB',(W,H),PAPER)
    draw = ImageDraw.Draw(image)
    panel = Image.new('RGB',(R-L+1,BOTTOM-TOP+1),PAPER)
    plot = ImageDraw.Draw(panel)
    x = lambda t: float(t)/xmax*(R-L)
    y = lambda value: (ymax-float(value))/(ymax-ymin)*(BOTTOM-TOP)
    if xmax > cutoff:
        plot.rectangle((x(cutoff),0,x(xmax),BOTTOM-TOP),fill='#e9ede8')
    for ordinate in ([-.25,0,.25,.5,.75,1] if sinc else [.5,.625,.75,.875,1]):
        ordinate = Q(str(ordinate))
        plot.line((0,y(ordinate),R-L,y(ordinate)),fill='#d6ddd7' if ordinate else '#82918a')
        draw.text((L-12,TOP+y(ordinate)),f'{float(ordinate):g}',font=font(16),fill=MUTED,anchor='rm')
    for node in nodes:
        plot.line((x(node),0,x(node),BOTTOM-TOP),fill='#e4e8e1')
    if sinc:
        tick = Q(1,2) if xmax <= 2 else Q(1)
    else:
        tick = max(Q(1,2**n),Q(1,8))
    for index in range(int(xmax/tick)+1):
        val = index*tick
        draw.text((L+x(val),BOTTOM+10),f'{float(val):g}',font=font(15),fill=MUTED,anchor='mt')

    for (a,b),(lo,hi,turn) in zip(zip(nodes,nodes[1:]),cells):
        if turn:
            plot.rectangle((x(a),0,x(b),BOTTOM-TOP),fill='#f0eaf5')
        plot.rectangle((x(a),y(hi),x(b),y(lo)),fill='#dfcee9' if turn else '#e8e6cf')

    samples = [i*xmax/520 for i in range(521)]
    def curve(t):
        if not sinc:
            return 1/(1+t*t)
        return math.sin(math.pi*t)/(math.pi*t) if t else 1
    plot.line([(x(t),y(curve(t))) for t in samples],fill=INK,width=2)

    for idx, ((a,b),(lo,hi,_)) in enumerate(zip(zip(nodes,nodes[1:]),cells)):
        for position, color, height in ((0,LOW,lo),(1,HIGH,hi)):
            plot.line((x(a),y(height),x(b),y(height)),fill=color,width=3)
            if idx:
                prev = cells[idx-1][position]
                plot.line((x(a),y(prev),x(a),y(height)),fill=color,width=2)
    for node in nodes:
        lo, hi = at(node)
        pos, bottom, top = x(node), y(lo), y(hi)
        if lo == hi:
            plot.ellipse((pos-2,top-2,pos+2,top+2),fill=INK)
        else:
            plot.line((pos,top,pos,bottom),fill=INK,width=2)
            plot.line((pos-3,top,pos+3,top),fill=INK)
            plot.line((pos-3,bottom,pos+3,bottom),fill=INK)
    if xmax > cutoff:
        plot.line((x(cutoff),0,x(cutoff),BOTTOM-TOP),fill=MUTED,width=2)
        plot.text((x(cutoff)+(x(xmax)-x(cutoff))/2,16),'Tail',font=font(16),fill=INK,anchor='mt')

    image.paste(panel,(L,TOP))
    draw.rectangle((L,TOP,R,BOTTOM),outline='#a4b2a7',width=1)
    title = 'Sinc on dyadic multiples of pi' if sinc else 'Reciprocal quadratic on a dyadic grid'
    draw.text((L,18),title,font=font(27),fill=INK)
    eval_label = f' · sample precision level {m}' if sinc else ' · exact rational samples'
    draw.text((L,57),f'Grid stage {n}'+eval_label,font=font(17),fill=MUTED)
    draw.text((R,BOTTOM+30),'t  (multiples of pi)' if sinc else 'x',font=font(15),fill=MUTED,anchor='rt')
    legend = [(LOW,'Lower staircase'),(HIGH,'Upper staircase'),(INK,'Node enclosure' if sinc else 'Exact node value')]
    if sinc:
        legend.append((TURN,'Whole-cell bounds'))
    for (color,label),pos in zip(legend,(84,274,470,660)):
        draw.line((pos,451,pos+22,451),fill=color,width=4)
        draw.text((pos+30,451),label,font=font(16),fill=INK,anchor='lm')

    gap = sum((hi-lo)/2**n for lo,hi,_ in cells)
    if sinc:
        draw.text((L,487),
                  f'Cutoff in units of pi: {cutoff}    |    Window gap at most {ceil_decimal(PI_HI*gap)}'
                  f'    |    Tail bound {ceil_decimal(2/(PI_LO*cutoff))}',
                  font=font(17),fill=INK)
    else:
        draw.text((L,487),f'Area between the staircases: {float(gap):.5f} (rounded)',font=font(17),fill=INK)
    return image


def ceil_decimal(q):
    return f'{math.ceil(q*1000)/1000:.3f}'


def render(output, name, settings, sinc):
    stages = [graph(n,cutoff,sinc) for n,cutoff in settings]
    frames = [stages[0]]
    durations = [2200]
    for left,right in zip(stages,stages[1:]):
        for step in range(1,5):
            frames.append(Image.blend(left,right,step/5))
            durations.append(55)
        frames.append(right)
        durations.append(2100 if sinc else 1750)
    durations[-1] = 2850
    frames[0].save(output / f'{name}.png',optimize=True)
    frames[0].save(output / f'{name}.gif',save_all=True,append_images=frames[1:],
                   duration=durations,loop=0,optimize=True)


if __name__ == '__main__':
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument('--output',type=Path,default=ROOT/'textbook/assets')
    directory = cli.parse_args().output
    directory.mkdir(parents=True,exist_ok=True)
    render(directory,'dyadic-reciprocal-quadratic',[(n,1) for n in range(5)],False)
    render(directory,'dyadic-sinc-enclosures',
           [(0,2),(1,2),(2,2),(3,2),(4,3),(5,4),(6,6)],True)
