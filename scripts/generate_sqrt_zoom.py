#!/usr/bin/env python3
"""Draw the square-root construction on a continuously zooming decimal grid."""

import argparse
from fractions import Fraction
import math
from pathlib import Path

from PIL import Image, ImageColor, ImageDraw, ImageFont

ROOT = Path(__file__).resolve().parents[1]
WIDTH, HEIGHT = 880, 544
LEFT, TOP, RIGHT, BOTTOM = 96, 58, 848, 448
PAPER, INK, MUTED = '#faf9f5', '#253634', '#55635f'
ORANGE, TEAL, PURPLE = '#ab490a', '#076b68', '#684492'


def font(size):
    return ImageFont.load_default(size=size)


def intervals():
    a, b = Fraction(1), Fraction(2)
    bounds = [(a, b)]
    for _ in range(3):
        lower, upper = (2 + a*b)/(a+b), (b + 2/b)/2
        assert a <= lower <= upper <= b
        assert lower**2 <= 2 <= upper**2
        a, b = lower, upper
        bounds.append((a, b))
    return bounds


def camera(stage, bounds):
    if stage == 0:
        return 1.16, 2.10, 2.38, 4.38
    a, b = bounds[stage]
    width = float(b-a) * 2.85
    return float((a+b)/2), 2.0, width, width * 1.8


def blend(color, opacity):
    background, foreground = ImageColor.getrgb(PAPER), ImageColor.getrgb(color)
    return tuple(round(a + (b-a)*opacity) for a, b in zip(background, foreground))


def decimal_ticks(lo, hi, pixels):
    target = (hi-lo) * 108 / pixels
    exponent = math.floor(math.log10(target))
    candidates = sorted((m * 10.0**power, max(0, -power))
                        for power in range(exponent-1, exponent+2) for m in (1, 2, 5))
    (fine, fine_digits), (coarse, coarse_digits) = next(
        (a, b) for a, b in zip(candidates, candidates[1:]) if a[0] <= target < b[0])
    t = math.log(target/fine)/math.log(coarse/fine)
    for step, places, opacity in ((coarse, coarse_digits, t), (fine, fine_digits, 1-t)):
        if opacity < .015:
            continue
        for n in range(math.ceil(lo*5/step), math.floor(hi*5/step)+1):
            value = n * step / 5
            if n % 5:
                yield value, None, opacity * .38
            else:
                yield value, format(value, f'.{places}f'), opacity


def labels(ticks, coordinate, spacing):
    used = []
    for value, label, alpha in sorted(ticks, key=lambda tick: -tick[2]):
        if label is None:
            continue
        position = coordinate(value)
        if all(abs(position-other) >= spacing for other in used):
            used.append(position)
            yield value, label, alpha


def frame(view, stage, bounds, transition=0):
    cx, cy, sx, sy = view
    xlo, xhi, ylo, yhi = cx-sx/2, cx+sx/2, cy-sy/2, cy+sy/2
    x = lambda v: LEFT + (float(v)-xlo) / sx * (RIGHT-LEFT)
    y = lambda v: BOTTOM - (float(v)-ylo) / sy * (BOTTOM-TOP)
    picture = Image.new('RGB', (WIDTH, HEIGHT), PAPER)
    draw = ImageDraw.Draw(picture)
    grid = Image.new('RGB', (RIGHT-LEFT+1, BOTTOM-TOP+1), PAPER)
    plot = ImageDraw.Draw(grid)
    px = lambda v: x(v)-LEFT
    py = lambda v: y(v)-TOP

    x_ticks = list(decimal_ticks(xlo, xhi, RIGHT-LEFT))
    y_ticks = list(decimal_ticks(ylo, yhi, BOTTOM-TOP))
    for value, _, alpha in x_ticks:
        plot.line((px(value), 0, px(value), BOTTOM-TOP), fill=blend('#bbc8c1', alpha))
    for value, label, alpha in labels(x_ticks, x, 77):
        if label and LEFT+27 <= x(value) <= RIGHT-27:
            draw.text((x(value), BOTTOM+9), label, font=font(15),
                      fill=blend(MUTED, max(.65, alpha)), anchor='mt')
    for value, _, alpha in y_ticks:
        plot.line((0, py(value), RIGHT-LEFT, py(value)), fill=blend('#bbc8c1', alpha))
    for value, label, alpha in labels(y_ticks, y, 44):
        if label and TOP+9 < y(value) < BOTTOM-9 and abs(y(value)-y(2)) > 13:
            draw.text((LEFT-10, y(value)), label, font=font(15),
                      fill=blend(MUTED, max(.65, alpha)), anchor='rm')

    a, b = bounds[stage]
    # Clip each graph to the part whose x-coordinates are visible.
    samples = [xlo+sx*i/160 for i in range(161)]
    plot.line([(px(t), py(t*t)) for t in samples], fill=INK, width=4)
    if stage+1 < len(bounds):
        next_a, next_b = bounds[stage+1]
        strength = 1-transition
        for intercept, slope, color in (
            (next_a, a+b, ORANGE), (next_b, 2*b, TEAL)
        ):
            plot.line([(px(t), py(2+float(slope)*(t-float(intercept)))) for t in (xlo,xhi)],
                      fill=blend(color, strength), width=3)
        for v, color in ((a, ORANGE), (b, TEAL)):
            if xlo <= v <= xhi and ylo <= v*v <= yhi:
                X, Y = px(v), py(v*v)
                plot.ellipse((X-5,Y-5,X+5,Y+5), fill=blend(color, strength))

    plot.line((0, py(2), RIGHT-LEFT, py(2)), fill='#7b8b83', width=1)
    if stage+1 < len(bounds):
        lower, upper = bounds[stage+1]
        alpha = 1-transition * .25
    else:
        lower, upper, alpha = a, b, 1
    level = py(2)
    for v, color in ((lower, ORANGE), (upper, TEAL)):
        X = px(v)
        if -5 <= X <= RIGHT-LEFT+5:
            plot.line((X, level, X, level+26), fill=blend(color, alpha), width=2)
            plot.ellipse((X-4, level-4, X+4, level+4), fill=blend(color, alpha))
    plot.line((px(lower), level+26, px(upper), level+26), fill=blend(PURPLE, alpha), width=6)
    picture.paste(grid, (LEFT, TOP))
    draw.rectangle((LEFT, TOP, RIGHT, BOTTOM), outline='#aebdb4', width=1)
    draw.text((LEFT-10,y(2)), '2', font=font(16), fill=INK, anchor='rm')
    draw.text((LEFT, 20), f'Stage {stage}   [{a}, {b}]', font=font(22), fill=INK)
    for position, color, text in (
        (96, INK, 'Parabola'), (237, ORANGE, 'Secant'), (361, TEAL, 'Tangent'),
        (494, PURPLE, 'Refined interval'),
    ):
        draw.line((position, 505, position+21, 505), fill=color, width=4)
        draw.text((position+31, 505), text, font=font(16), fill=INK, anchor='lm')
    return picture


def zoom_frames(bounds):
    views = [camera(i, bounds) for i in range(len(bounds))]
    images = [frame(views[0], 0, bounds)]
    times = [1450]
    for stage, (start, finish) in enumerate(zip(views, views[1:])):
        count = (26, 35, 59)[stage]
        for i in range(1, count):
            t = i/count
            k = t*t*(3-2*t)
            centers = [a+(b-a)*k for a,b in zip(start[:2], finish[:2])]
            spans = [a*(b/a)**k for a,b in zip(start[2:], finish[2:])]
            images.append(frame(centers+spans, stage, bounds, max(0, (t-.78)/.22)))
            times.append(50)
        images.append(frame(finish, stage+1, bounds))
        times.append(1300 if stage < 2 else 2200)
    # Reverse the camera through the same centers to avoid a jump on replay.
    reverse = [i for i in range(len(images)-2, 0, -2)]
    return images + [images[i] for i in reverse], times + [90 for i in reverse]


def main():
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument('--output', type=Path, default=ROOT/'textbook/assets')
    output = cli.parse_args().output
    output.mkdir(parents=True, exist_ok=True)
    frames, timing = zoom_frames(intervals())
    frames[0].save(output/'sqrt-secant-zoom.png', optimize=True)
    frames[0].save(output/'sqrt-secant-zoom.gif', save_all=True,
                   append_images=frames[1:], duration=timing, loop=0, optimize=True)


if __name__ == '__main__':
    main()
