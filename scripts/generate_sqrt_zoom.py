#!/usr/bin/env python3
"""Render the three secant–tangent constructions. Requires Pillow and Matplotlib."""

import argparse
import math
from fractions import Fraction
from functools import lru_cache
from pathlib import Path

import matplotlib
import numpy as np
from matplotlib.font_manager import FontProperties
from matplotlib.mathtext import MathTextParser
from PIL import Image, ImageColor, ImageDraw, ImageFont

ROOT = Path(__file__).resolve().parents[1]
W, H = 880, 544
L, T, R, B = 92, 94, 850, 425
PW, PH = R-L, B-T
PAPER, PLOT = '#faf9f5', '#fffefa'
INK, MUTED, AXIS = '#20332e', '#4e6059', '#597468'
LOW, HIGH = '#ab471d', '#006c70'
GRID, MINOR = '#cfdad1', '#eaeee7'
TITLES = {
    'start': 'Begin with the two bounds',
    'project': 'Find both points on the parabola',
    'secant': 'Trace the secant through the two points',
    'tangent': 'Draw the tangent from the upper point',
    'zoom': 'Zoom in on the two crossings',
    'end': 'Read the tighter bracket',
}
MATH = MathTextParser('agg')


def intervals():
    a, b = Fraction(1), Fraction(2)
    bounds = [(a, b)]
    for _ in range(3):
        lower, upper = (2+a*b)/(a+b), (b+2/b)/2
        assert a < lower < upper < b and lower**2 < 2 < upper**2
        assert a*a + (a+b)*(lower-a) == b*b + 2*b*(upper-b) == 2
        bounds.append((lower, upper))
        a, b = lower, upper
    return bounds


@lru_cache(maxsize=None)
def font(size, family='Sans'):
    path = Path(matplotlib.get_data_path())/'fonts/ttf'/f'DejaVu{family}.ttf'
    return ImageFont.truetype(str(path), size)


@lru_cache(maxsize=None)
def formula(tex, size):
    raster = MATH.parse(f'${tex}$', dpi=72, prop=FontProperties(size=size))
    mask = Image.fromarray(np.asarray(raster.image))
    return mask.crop(mask.getbbox())


def math_label(image, x, y, tex, size, color, anchor='left'):
    mask = formula(tex, size)
    offset = {'left': 0, 'center': mask.width/2, 'right': mask.width}[anchor]
    image.paste(color, (round(x-offset), round(y-mask.height/2)), mask)


def fraction_tex(q):
    if q.denominator == 1:
        return str(q.numerator)
    return rf'\frac{{{q.numerator}}}{{{q.denominator}}}'


def camera(bounds):
    a, b = bounds
    return float((a+b)/2), float((a*a+b*b)/2), float(b-a)*1.60, float(b*b-a*a)*1.48


def zoom(start, finish, t):
    # Interpolate in magnification, keeping both new crossings in the window.
    k = t*t*(3-2*t)
    sx = start[2]*(finish[2]/start[2])**k
    sy = start[3]*(finish[3]/start[3])**k
    def center(old, new, span, wide, narrow):
        return new + (old-new)*(span-narrow)/(wide-narrow)
    return (center(start[0], finish[0], sx, start[2], finish[2]),
            center(start[1], finish[1], sy, start[3], finish[3]), sx, sy)


def ticks(lo, hi, target):
    power = math.floor(math.log10(target))
    step = min((m*10.0**e for e in range(power-1, power+2) for m in (1, 2, 5)),
               key=lambda s: abs(math.log(s/target)))
    digits = max(0, -math.floor(math.log10(step)+1e-10))
    for i in range(math.ceil(5*lo/step), math.floor(5*hi/step)+1):
        value = i*step/5
        yield value, None if i % 5 else f'{value:.{digits}f}'


def render(bounds, stage, phase, progress=1):
    a, b = map(float, bounds[stage])
    new_a, new_b = map(float, bounds[stage+1])
    view = camera(bounds[stage])
    if phase in ('zoom', 'end'):
        view = zoom(view, camera(bounds[stage+1]), progress)
    cx, cy, sx, sy = view
    x = lambda v: PW*(.5+(v-cx)/sx)
    y = lambda v: PH*(.5-(v-cy)/sy)
    level = y(2)
    phase_order = list(TITLES)
    def amount(step):
        difference = phase_order.index(phase)-phase_order.index(step)
        return progress if difference == 0 else float(difference > 0)
    guide, chord, tangent = (amount(name) for name in ('project', 'secant', 'tangent'))
    # Render plot strokes at double resolution and clip to the plot throughout.
    panel = Image.new('RGB', (2*PW, 2*PH), PLOT)
    pen = ImageDraw.Draw(panel)
    def line(points, color, width=1):
        pen.line([(round(2*u), round(2*v)) for u, v in points], fill=color,
                 width=round(2*width), joint='curve')
    def marker(u, v, color, square=False, size=4):
        box = ((u-size)*2, (v-size)*2, (u+size)*2, (v+size)*2)
        shape = pen.rectangle if square else pen.ellipse
        shape(box, fill=color, outline=PLOT, width=2)
    scene = Image.new('RGB', (W,H), PAPER)
    draw = ImageDraw.Draw(scene)
    xt = list(ticks(cx-sx/2, cx+sx/2, sx*118/PW))
    yt = list(ticks(cy-sy/2, cy+sy/2, sy*67/PH))
    for v, label in xt:
        line([(x(v),0), (x(v),PH)], GRID if label else MINOR)
    for v, label in yt:
        line([(0,y(v)), (PW,y(v))], GRID if label else MINOR)
        if label and 8 < y(v) < PH-8 and abs(y(v)-level) > 15:
            draw.text((L-9, T+y(v)), label, font=font(14), fill=MUTED, anchor='rm')
    line([(0,level), (PW,level)], AXIS, 1.6)
    samples = [cx+sx*(i/180-.5) for i in range(181)]
    line([(x(v), y(v*v)) for v in samples], INK, 3)
    for v, color, square in ((a, LOW, False), (b, HIGH, True)):
        if -8 < x(v) < PW+8:
            tip = level+(y(v*v)-level)*guide
            line([(x(v),level), (x(v),tip)], color, 1.6)
            marker(x(v),level,color,square)
            if guide:
                marker(x(v),tip,color,square,5)
    if chord:
        tip = a+(b-a)*chord
        line([(x(a),y(a*a)),(x(tip),y(a*a+(a+b)*(tip-a)))], LOW, 3)
    if tangent:
        # A broken stroke keeps the two lines distinguishable when nearly parallel.
        start_x, start_y = x(b), y(b*b)
        stop_x, stop_y = x(b+(new_b-b)*tangent), y(b*b+(2-b*b)*tangent)
        dx, dy = stop_x-start_x, stop_y-start_y
        length = math.hypot(dx,dy)
        if length:
            # Only dashes near the visible panel are needed during deep zooms.
            near = max(0, (start_x-PW-12)/(-dx)) if dx < 0 else 0
            far = min(1, (start_x+12)/(-dx)) if dx < 0 else 1
            for n in range(math.floor(near*length/13), math.ceil(far*length/13)):
                t0, t1 = max(0,n*13/length), min(1,(n*13+9)/length)
                line([(start_x+t0*dx,start_y+t0*dy),(start_x+t1*dx,start_y+t1*dy)],HIGH,3)
    lower_hit = chord >= (new_a-a)/(b-a)
    upper_hit = tangent == 1
    if lower_hit:
        marker(x(new_a),level,LOW,size=6)
    if upper_hit:
        marker(x(new_b),level,HIGH,True,size=5)
    scene.paste(panel.resize((PW,PH), Image.Resampling.LANCZOS), (L,T))
    draw.rectangle((L,T,R,B), outline=GRID)
    # Tick labels sit on the working horizontal. Back them with paper for clarity.
    for v, label in xt:
        u = L+x(v)
        if label and L+29 < u < R-29:
            draw.line((u,T+level,u,T+level+4), fill=AXIS)
            pos = (u,T+level+7)
            box = draw.textbbox(pos,label,font=font(14),anchor='mt')
            draw.rectangle((box[0]-2,box[1],box[2]+2,box[3]+1),fill=PLOT)
            draw.text(pos,label,font=font(14),fill=MUTED,anchor='mt')
    math_label(scene,L-8,T+level,'y=2',16,AXIS,'right')
    math_label(scene,R+8,T+level,'x',16,AXIS)
    # Label the old endpoints while constructing, then label each new crossing
    # on its outer side, even when both land on the very same display pixel.
    for v, tex, color in ((a,'a',LOW),(b,'b',HIGH)):
        if not lower_hit and 8 < x(v) < PW-8:
            math_label(scene,L+x(v)+7,T+level-14,tex,18,color)
    if lower_hit:
        math_label(scene,L+x(new_a)-8,T+level-13,"a'",18,LOW,'right')
    if upper_hit:
        math_label(scene,L+x(new_b)+5,T+level+31,"b'",18,HIGH)
    title = 'Use the crossings as the new bounds' if stage and phase == 'start' else TITLES[phase]
    draw.text((32,28),title,font=font(29,'Serif'),fill=INK,anchor='lm')
    draw.text((R,29),f'Round {stage+1} of 3',font=font(16),fill=MUTED,anchor='rm')
    # The key uses the same line patterns as the construction.
    draw.line((L,68,L+25,68),fill=INK,width=3)
    math_label(scene,L+33,67,'y=x^2',19,INK)
    draw.line((L+142,68,L+169,68),fill=LOW,width=3)
    draw.text((L+177,68),'Secant',font=font(16),fill=LOW,anchor='lm')
    for shift in (0,15):
        draw.line((L+275+shift,68,L+284+shift,68),fill=HIGH,width=3)
    draw.text((L+312,68),'Tangent',font=font(16),fill=HIGH,anchor='lm')
    draw.line((32,449,R,449),fill=GRID)
    for u, name, i, reached, color, label in (
        (L, 'a', 0, lower_hit, LOW, 'Lower bound'),
        (W//2+20, 'b', 1, upper_hit, HIGH, 'Upper bound'),
    ):
        draw.text((u,472),label,font=font(15),fill=MUTED,anchor='lm')
        prime = "'" if reached else ''
        q = bounds[stage+int(reached)][i]
        math_label(scene,u,510,name+prime+'='+fraction_tex(q),24,color)
    return scene


def animation(bounds):
    for stage in range(len(bounds)-1):
        yield render(bounds,stage,'start'), 1100
        for phase, count, pause in (('project',12,650), ('secant',18,900), ('tangent',15,1200),
                                    ('zoom',(20,28,40)[stage],1000)):
            for i in range(1,count+1):
                yield render(bounds,stage,phase,i/count), pause if i == count else 60
    yield render(bounds,2,'end'), 2200


def main():
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument('--output',type=Path,default=ROOT/'textbook/assets')
    output = cli.parse_args().output
    output.mkdir(parents=True,exist_ok=True)
    bounds = intervals()
    render(bounds,0,'tangent').save(output/'sqrt-secant-zoom.png',optimize=True)
    # Share an antialiasing palette across frames to avoid GIF color flicker.
    colors = []
    for background in (PAPER,PLOT):
        bg = ImageColor.getrgb(background)
        for color in (INK,MUTED,AXIS,LOW,HIGH,GRID,MINOR):
            fg = ImageColor.getrgb(color)
            for i in range(17):
                colors.append(tuple(round(a+(b-a)*i/16) for a,b in zip(bg,fg)))
    palette = Image.new('P',(1,1))
    palette.putpalette([channel for color in colors for channel in color])
    frames, times = [], []
    for image, duration in animation(bounds):
        frames.append(image.quantize(palette=palette,dither=Image.Dither.NONE))
        times.append(duration)
    frames[0].save(output/'sqrt-secant-zoom.gif',save_all=True,append_images=frames[1:],
                   duration=times,loop=0,optimize=True,disposal=1)


if __name__ == '__main__':
    main()
