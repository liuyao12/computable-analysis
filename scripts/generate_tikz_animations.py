#!/usr/bin/env python3
"""Render every blueprint animation from reproducible TikZ frames.

The Python portion computes exact finite meshes and writes TikZ.  Every
visible label, formula, curve, segment, and filled region is rendered by
LaTeX/TikZ; Pillow only assembles the rendered PDF pages into GIFs.
"""

from __future__ import annotations

import argparse
import math
import shutil
import subprocess
import tempfile
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path

from PIL import Image


ROOT = Path(__file__).resolve().parents[1]
ASSETS = ROOT / "blueprint" / "src" / "assets"
SOURCES = ASSETS / "tikz"
COLOURS = r"""
\definecolor{ink}{RGB}{28,41,56}
\definecolor{axis}{RGB}{100,116,139}
\definecolor{grid}{RGB}{203,213,225}
\definecolor{curve}{RGB}{30,64,175}
\definecolor{teal}{RGB}{13,148,136}
\definecolor{tealfill}{RGB}{176,227,219}
\definecolor{orange}{RGB}{234,88,12}
\definecolor{orangefill}{RGB}{254,215,170}
\definecolor{purple}{RGB}{126,34,206}
\definecolor{yellowfill}{RGB}{254,243,199}
\definecolor{yellowedge}{RGB}{202,138,4}
\definecolor{projection}{RGB}{148,163,184}
"""


@dataclass(frozen=True)
class Animation:
    name: str
    width: int
    height: int
    frames: tuple[str, ...]
    duration: tuple[int, ...]
    poster: int


def q(value: float | Fraction | int) -> str:
    return f"{float(value):.4f}".rstrip("0").rstrip(".")


def path(points: list[tuple[float, float]]) -> str:
    return " ".join(f"({q(x)},{q(y)})" for x, y in points)


def n(x: float, y: float, text: str, opts: str = "") -> str:
    extra = "," + opts if opts else ""
    return rf"\node[font=\small,text=ink{extra}] at ({q(x)},{q(y)}) {{{text}}};"


def dot(x: float, y: float, colour: str = "ink", radius: float = 1.6) -> str:
    return rf"\fill[{colour}] ({q(x)},{q(y)}) circle[radius={q(radius)}pt];"


def tex(width: int, height: int, body: str) -> str:
    return rf"""\documentclass{{article}}
\usepackage[paperwidth={width}pt,paperheight={height}pt,margin=0pt,noheadfoot]{{geometry}}
\usepackage{{tikz}}
\usetikzlibrary{{calc}}
{COLOURS}
\pagestyle{{empty}}
\setlength\parindent{{0pt}}
\setlength\topskip{{0pt}}
\begin{{document}}
\noindent\begin{{tikzpicture}}[baseline=(current bounding box.north),x=1pt,y=1pt,line cap=round,line join=round]
\useasboundingbox (0,0) rectangle ({width},{height});
{body}
\end{{tikzpicture}}
\end{{document}}
"""


def rational_kernel(value: Fraction) -> Fraction:
    return 1 / (1 + value * value)


def kernel_frame(cells: int) -> str:
    x0, y0, unit = 94, 34, 168
    out = [
        rf"\draw[axis,line width=.75pt] ({x0-13},{y0}) -- ({x0+unit+13},{y0});",
        rf"\draw[axis,line width=.75pt] ({x0},{y0-12}) -- ({x0},{y0+unit+13});",
    ]
    mesh = [Fraction(i, cells) for i in range(cells + 1)]
    for t in mesh:
        x = x0 + float(t) * unit
        out += [
            rf"\draw[grid,line width=.3pt] ({q(x)},{y0}) -- ({q(x)},{y0+unit});",
            rf"\draw[axis,line width=.55pt] ({q(x)},{y0-3}) -- ({q(x)},{y0+3});",
        ]
    for left, right in zip(mesh, mesh[1:]):
        lx, rx = x0 + float(left) * unit, x0 + float(right) * unit
        out += [
            rf"\path[fill=orangefill,draw=orange,line width=.45pt] ({q(lx)},{y0}) rectangle ({q(rx)},{q(y0+float(rational_kernel(left))*unit)});",
            rf"\path[fill=tealfill,draw=teal,line width=.45pt] ({q(lx)},{y0}) rectangle ({q(rx)},{q(y0+float(rational_kernel(right))*unit)});",
        ]
    curve = [(x0 + unit * i / 100, y0 + unit / (1 + (i / 100) ** 2)) for i in range(101)]
    out += [
        rf"\draw[curve,line width=1.1pt] plot[smooth] coordinates {{{path(curve)}}};",
        n(x0, y0 - 12, r"$0$", "anchor=north"),
        n(x0 + unit, y0 - 12, r"$1$", "anchor=north"),
        n(x0 - 10, y0 + unit, r"$1$", "anchor=east"),
        n(x0 + unit + 12, y0 - 2, r"$t$", "anchor=west"),
        n(x0 + 112, y0 + 100, r"$\frac{1}{1+t^2}$", "text=curve"),
    ]
    return "\n".join(out)


def kernel_animation(name: str) -> Animation:
    return Animation(name, 360, 230, tuple(kernel_frame(i) for i in (1, 2, 4, 8)), (1200, 1200, 1200, 1900), 3)


def partial_sine(value: Fraction, last: int) -> Fraction:
    return sum(
        Fraction(1 if i % 2 == 0 else -1, math.factorial(2 * i + 1)) * value ** (2 * i + 1)
        for i in range(last + 1)
    )


def sine_box(value: Fraction, last: int, guard: Fraction) -> tuple[Fraction, Fraction]:
    # These two endpoint samples are exact: sin(0) = 0 and sin(pi / 2) = 1.
    # All interior samples remain interval evaluations, even though the curve
    # itself is drawn smoothly as a visual guide.
    if value == 0:
        return Fraction(0), Fraction(0)
    if value == Fraction(1, 2):
        return Fraction(1), Fraction(1)
    lower = partial_sine(Fraction(333, 106) * value, last)
    upper = partial_sine(Fraction(355, 113) * value, last + 1)
    return max(Fraction(0), lower - guard), min(Fraction(1), upper + guard)


def sine_frame(cells: int, last: int, guard: Fraction) -> str:
    x0, y0, xunit, yunit = 58, 35, 224, 155
    out = [
        rf"\draw[axis,line width=.75pt] ({x0-12},{y0}) -- ({x0+xunit+13},{y0});",
        rf"\draw[axis,line width=.75pt] ({x0},{y0-11}) -- ({x0},{y0+yunit+13});",
    ]
    mesh = [Fraction(i, 2 * cells) for i in range(cells + 1)]
    boxes = {t: sine_box(t, last, guard) for t in mesh}
    for t in mesh:
        x = x0 + 2 * float(t) * xunit
        out += [
            rf"\draw[grid,line width=.3pt] ({q(x)},{y0}) -- ({q(x)},{y0+yunit});",
            rf"\draw[axis,line width=.55pt] ({q(x)},{y0-3}) -- ({q(x)},{y0+3});",
        ]
    for left, right in zip(mesh, mesh[1:]):
        lx, rx = x0 + 2 * float(left) * xunit, x0 + 2 * float(right) * xunit
        out += [
            rf"\path[fill=orangefill,draw=orange,line width=.45pt] ({q(lx)},{y0}) rectangle ({q(rx)},{q(y0+float(boxes[right][1])*yunit)});",
            rf"\path[fill=tealfill,draw=teal,line width=.45pt] ({q(lx)},{y0}) rectangle ({q(rx)},{q(y0+float(boxes[left][0])*yunit)});",
        ]
    curve = [(x0 + xunit * i / 150, y0 + yunit * math.sin(math.pi * i / 300)) for i in range(151)]
    out.append(rf"\draw[ink,line width=1.05pt] plot[smooth] coordinates {{{path(curve)}}};")
    for t in mesh:
        x = x0 + 2 * float(t) * xunit
        lower, upper = boxes[t]
        low, high = y0 + float(lower) * yunit, y0 + float(upper) * yunit
        if t == 0 or t == Fraction(1, 2):
            out.append(dot(x, low, "curve", 1.35))
            continue
        out += [
            rf"\draw[curve,line width=.8pt] ({q(x)},{q(low)}) -- ({q(x)},{q(high)});",
            rf"\draw[curve,line width=.6pt] ({q(x-2.5)},{q(low)}) -- ({q(x+2.5)},{q(low)});",
            rf"\draw[curve,line width=.6pt] ({q(x-2.5)},{q(high)}) -- ({q(x+2.5)},{q(high)});",
        ]
    out += [
        n(x0, y0 - 12, r"$0$", "anchor=north"),
        n(x0 + xunit, y0 - 12, r"$\frac12$", "anchor=north"),
        n(x0 - 10, y0 + yunit, r"$1$", "anchor=east"),
        n(x0 + xunit + 12, y0 - 2, r"$x$", "anchor=west"),
        n(x0 + 160, y0 + 109, r"$\sin(\pi x)$"),
    ]
    return "\n".join(out)


def sine_animation() -> Animation:
    stages = ((1, 1, Fraction(1, 2)), (2, 3, Fraction(1, 4)), (4, 5, Fraction(1, 8)), (8, 7, Fraction(1, 16)))
    return Animation("interval-sine-integral-stage", 360, 230, tuple(sine_frame(*stage) for stage in stages), (1200, 1200, 1200, 1900), 1)


def circle(value: float) -> tuple[float, float]:
    return ((1 - value * value) / (1 + value * value), 2 * value / (1 + value * value))


def tangent(left: tuple[float, float], right: tuple[float, float]) -> tuple[float, float]:
    determinant = left[0] * right[1] - left[1] * right[0]
    return ((right[1] - left[1]) / determinant, (left[0] - right[0]) / determinant)


def circle_frame(cells: int) -> str:
    x0, y0, radius = 166, 62, 106
    screen = lambda value: (x0 + radius * value[0], y0 + radius * value[1])
    origin, west, north, east = screen((0, 0)), screen((-1, 0)), screen((0, 1)), screen((1, 0))
    mesh = [i / cells for i in range(cells + 1)]
    samples, plotted = [circle(t) for t in mesh], []
    plotted = [screen(point) for point in samples]
    outer = [screen(tangent(a, b)) for a, b in zip(samples, samples[1:])]
    out = [
        rf"\draw[axis,line width=.75pt] ({q(west[0]-12)},{q(y0)}) -- ({q(east[0]+16)},{q(y0)});",
        rf"\draw[axis,line width=.75pt] ({q(x0)},{q(y0-10)}) -- ({q(x0)},{q(north[1]+15)});",
        rf"\draw[curve,line width=1pt] ({q(x0)},{q(y0)}) -- ({q(x0)},{q(north[1])});",
        rf"\draw[ink,line width=1.2pt] ({q(east[0])},{q(y0)}) arc[start angle=0,end angle=90,radius={radius}pt];",
        rf"\path[fill=tealfill] ({q(origin[0])},{q(origin[1])}) -- {path(plotted)} -- cycle;",
    ]
    for value, endpoint in zip(mesh, plotted):
        vertical = screen((0, value))
        out += [
            rf"\draw[projection,line width=.5pt] ({q(west[0])},{q(west[1])}) -- ({q(endpoint[0])},{q(endpoint[1])});",
            rf"\draw[grid,line width=.5pt] ({q(vertical[0]-3)},{q(vertical[1])}) -- ({q(vertical[0]+3)},{q(vertical[1])});",
            dot(*vertical, "axis", 1.3),
        ]
    out += [
        rf"\draw[teal,line width=1.1pt] plot coordinates {{{path(plotted)}}};",
        rf"\draw[orange,line width=1.1pt] plot coordinates {{{path([plotted[0], *outer, plotted[-1]])}}};",
    ]
    out += [dot(*point, "ink", 1.65) for point in plotted]
    out += [
        dot(*origin, "ink", 1.7),
        dot(*west, "ink", 1.7),
        n(west[0], west[1] - 13, r"$(-1,0)$", "anchor=north"),
        n(origin[0], origin[1] - 13, r"$0$", "anchor=north"),
        n(north[0] - 12, north[1], r"$1$", "anchor=east"),
        n(east[0] + 11, east[1] - 2, r"$P(0)$", "anchor=west"),
        n(north[0] + 11, north[1] + 2, r"$P(1)$", "anchor=west"),
    ]
    return "\n".join(out)


def circle_animation() -> Animation:
    return Animation("rational-circle-subdivision", 360, 190, tuple(circle_frame(i) for i in (1, 2, 4, 8)), (1200, 1200, 1200, 1800), 3)


def sqrt_states() -> list[tuple[Fraction, Fraction]]:
    a, b, result = Fraction(1), Fraction(2), []
    for _ in range(4):
        result.append((a, b))
        a, b = (2 + a * b) / (a + b), (b + 2 / b) / 2
    return result


def sqrt_frame(a: Fraction, b: Fraction) -> str:
    an, bn = (2 + a * b) / (a + b), (b + 2 / b) / 2
    x0, y0, unit = 43, 40, 72
    x, y = lambda value: x0 + float(value) * unit, lambda value: y0 + float(value) * unit
    out = [
        rf"\draw[axis,line width=.75pt] ({x0-8},{y0}) -- ({q(x(Fraction(47,20)))},{y0});",
        rf"\draw[axis,line width=.75pt] ({x0},{y0-8}) -- ({x0},{q(y(Fraction(23,5)))});",
    ]
    for i in range(1, 5):
        out.append(rf"\draw[grid,line width=.28pt] ({q(x(Fraction(i,2)))},{y0}) -- ({q(x(Fraction(i,2)))},{q(y(Fraction(9,2)))});")
    for i in range(1, 10):
        out.append(rf"\draw[grid,line width=.28pt] ({x0},{q(y(Fraction(i,2)))}) -- ({q(x(Fraction(9,4)))},{q(y(Fraction(i,2)))});")
    parabola = [(x(i / 100), y((i / 100) ** 2)) for i in range(226)]
    out += [
        rf"\draw[curve,line width=1.05pt] plot[smooth] coordinates {{{path(parabola)}}};",
        rf"\draw[axis,line width=.5pt] ({x0},{q(y(2))}) -- ({q(x(Fraction(9,4)))},{q(y(2))});",
        rf"\draw[orange,line width=1pt] ({q(x(a))},{q(y(a*a))}) -- ({q(x(b))},{q(y(b*b))});",
        rf"\draw[teal,line width=1pt] ({q(x(bn))},{q(y(2))}) -- ({q(x(b))},{q(y(b*b))});",
        rf"\draw[purple,line width=1.8pt] ({q(x(an))},{y0}) -- ({q(x(bn))},{y0});",
        rf"\draw[orange,line width=.65pt] ({q(x(an))},{q(y(2))}) -- ({q(x(an))},{y0});",
        rf"\draw[teal,line width=.65pt] ({q(x(bn))},{q(y(2))}) -- ({q(x(bn))},{y0});",
        dot(x(a), y(a*a), "orange"),
        dot(x(b), y(b*b), "teal"),
        dot(x(an), y(2), "orange"),
        dot(x(bn), y(2), "teal"),
        n(x(a)-6, y0-18, r"$a$", "anchor=north,text=orange"),
        n(x(b)+6, y0-18, r"$b$", "anchor=north,text=teal"),
        n(x0-8, y(2), r"$2$", "anchor=east"),
        n(x0, y0-12, r"$0$", "anchor=north"),
        n(x(1), y0-12, r"$1$", "anchor=north"),
        n(x(2), y0-12, r"$2$", "anchor=north"),
    ]
    return "\n".join(out)


def sqrt_animation() -> Animation:
    return Animation("sqrt-secant-tangent", 220, 380, tuple(sqrt_frame(*state) for state in sqrt_states()), (1400, 1200, 1200, 1900), 0)


def substitution_frame(cells: int) -> str:
    left, right, top, bottom = 57, 300, 135, 51
    x = lambda value: left + float(value) * (right - left)
    mesh = [Fraction(i, cells) for i in range(cells + 1)]
    out = [
        rf"\draw[axis,line width=.75pt] ({left-10},{top}) -- ({right+14},{top});",
        rf"\draw[axis,line width=.75pt] ({left-10},{bottom}) -- ({right+14},{bottom});",
    ]
    for value in mesh:
        t, image = x(value), x(value*value)
        out += [
            rf"\draw[grid,line width=.5pt] ({q(t)},{top-4}) -- ({q(image)},{bottom+4});",
            rf"\draw[axis,line width=.55pt] ({q(t)},{top-3.5}) -- ({q(t)},{top+3.5});",
            rf"\draw[curve,line width=.55pt] ({q(image)},{bottom-3.5}) -- ({q(image)},{bottom+3.5});",
            dot(t, top, "axis", 1.5),
            dot(image, bottom, "curve", 1.5),
        ]
    out += [
        n(left, top+12, r"$t_0$", "anchor=north"),
        n(right, top+12, r"$t_1$", "anchor=north"),
        n(right+13, top, r"$t$", "anchor=west"),
        n(right+13, bottom, r"$x=\varphi(t)=t^2$", "anchor=west"),
    ]
    return "\n".join(out)


def substitution_animation() -> Animation:
    return Animation("substitution-partition", 360, 170, tuple(substitution_frame(i) for i in (1, 2, 4, 8)), (1200, 1200, 1200, 1900), 2)


def ibp_frame(cells: int) -> str:
    left, bottom, unit, ruler = 77, 67, 190, 29
    mesh = [Fraction(i, cells) for i in range(cells + 1)]
    f, g = mesh, [value*value for value in mesh]
    x, y = lambda value: left + float(value)*unit, lambda value: bottom + float(value)*unit
    out = [
        rf"\draw[axis,line width=.75pt] ({left-10},{bottom}) -- ({left+unit+14},{bottom});",
        rf"\draw[axis,line width=.75pt] ({left},{bottom-10}) -- ({left},{bottom+unit+13});",
        rf"\draw[axis,line width=.75pt] ({left},{ruler}) -- ({left+unit},{ruler});",
    ]
    for value in f:
        out += [
            rf"\draw[grid,line width=.3pt] ({q(x(value))},{bottom}) -- ({q(x(value))},{bottom+unit});",
            rf"\draw[axis,line width=.55pt] ({q(x(value))},{ruler-3}) -- ({q(x(value))},{ruler+3});",
        ]
    for value in g[1:]:
        out.append(rf"\draw[grid,line width=.3pt] ({left},{q(y(value))}) -- ({left+unit},{q(y(value))});")
    curve = [(x(i/100), y((i/100)**2)) for i in range(101)]
    out.append(rf"\draw[ink,line width=.85pt] plot[smooth] coordinates {{{path(curve)}}};")
    for lf, rf_, lg, rg in zip(f, f[1:], g, g[1:]):
        out.append(rf"\path[fill=yellowfill] ({q(x(lf))},{q(y(lg))}) rectangle ({q(x(rf_))},{q(y(rg))});")
    horizontal, vertical = [(x(f[0]), y(g[0]))], [(x(f[0]), y(g[0]))]
    for lf, rf_, lg, rg in zip(f, f[1:], g, g[1:]):
        horizontal += [(x(rf_), y(lg)), (x(rf_), y(rg))]
        vertical += [(x(lf), y(rg)), (x(rf_), y(rg))]
    out += [
        rf"\draw[orange,line width=.9pt] plot coordinates {{{path(horizontal)}}};",
        rf"\draw[teal,line width=.9pt] plot coordinates {{{path(vertical)}}};",
        *[dot(x(fv), y(gv), "ink", 1.45) for fv, gv in zip(f, g)],
        n(left, ruler-11, r"$t_0$", "anchor=north"),
        n(left+unit, ruler-11, r"$t_1$", "anchor=north"),
        n(left+unit+12, ruler, r"$t$", "anchor=west"),
        n(left+unit+13, bottom, r"$f(t)$", "anchor=west"),
        n(left, bottom+unit+11, r"$g(t)$", "anchor=south"),
    ]
    return "\n".join(out)


def ibp_animation() -> Animation:
    return Animation("integration-by-parts-cell", 360, 275, tuple(ibp_frame(i) for i in (1, 2, 4, 8, 16)), (1050, 1050, 1050, 1050, 1900), 4)


def ftc_frame(cells: int) -> str:
    base, pleft, dleft, unit = 45, 63, 246, 100
    px, dx, y = lambda v: pleft+float(v)*unit, lambda v: dleft+float(v)*unit, lambda v: base+float(v)*unit
    out = []
    for left, label, height in ((pleft, r"$F(t)=t^2$", 1), (dleft, r"$F'(t)=2t$", 2)):
        out += [
            rf"\draw[axis,line width=.75pt] ({left-10},{base}) -- ({left+unit+12},{base});",
            rf"\draw[axis,line width=.75pt] ({left},{base-10}) -- ({left},{q(y(height)+10)});",
            rf"\draw[grid,line width=.3pt] ({left+unit/2},{base}) -- ({left+unit/2},{q(y(height))});",
            n(left, base-11, r"$0$", "anchor=north"),
            n(left+unit, base-11, r"$1$", "anchor=north"),
            n(left, y(height)+8, label, "anchor=south"),
        ]
    primitive = [(px(i/100), y((i/100)**2)) for i in range(101)]
    derivative = [(dx(i/100), y(2*i/100)) for i in range(101)]
    out += [
        rf"\draw[purple,line width=1.05pt] plot[smooth] coordinates {{{path(primitive)}}};",
        rf"\draw[purple,line width=1.8pt] ({q(px(1))},{base}) -- ({q(px(1))},{q(y(1))});",
    ]
    mesh = [Fraction(i, cells) for i in range(cells+1)]
    for left, right in zip(mesh, mesh[1:]):
        out += [
            rf"\path[fill=orangefill,draw=orange,line width=.4pt] ({q(dx(left))},{base}) rectangle ({q(dx(right))},{q(y(2*right))});",
            rf"\path[fill=tealfill,draw=teal,line width=.4pt] ({q(dx(left))},{base}) rectangle ({q(dx(right))},{q(y(2*left))});",
        ]
    out += [
        rf"\draw[curve,line width=1.05pt] plot coordinates {{{path(derivative)}}};",
        n(px(1)-3, y(1)+11, r"$F(1)-F(0)$", "anchor=south west,text=purple"),
        n(pleft+unit+11, base, r"$t$", "anchor=west"),
        n(dleft+unit+11, base, r"$t$", "anchor=west"),
    ]
    return "\n".join(out)


def ftc_animation() -> Animation:
    return Animation("ftc-endpoint-comparison", 370, 270, tuple(ftc_frame(i) for i in (1, 2, 4, 8)), (1200, 1200, 1200, 1900), 2)


def sinc(value: float) -> float:
    return 1 if value == 0 else math.sin(math.pi*value)/(math.pi*value)


def single_turn_frame(turn_left: Fraction, turn_right: Fraction, cells: int) -> str:
    left, base, trig, vertical = 47, 112, 45, 112
    x, y = lambda v: left+float(v)*math.pi*trig, lambda v: base+float(v)*vertical
    out = [
        rf"\draw[axis,line width=.75pt] ({left-10},{q(y(0))}) -- ({q(x(2)+12)},{q(y(0))});",
        rf"\draw[axis,line width=.75pt] ({left},{q(y(-.28)-10)}) -- ({left},{q(y(1.04)+10)});",
    ]
    for value in (Fraction(1,2), Fraction(1), Fraction(3,2)):
        out.append(rf"\draw[grid,line width=.3pt] ({q(x(value))},{q(y(-.28))}) -- ({q(x(value))},{q(y(1.04))});")
    for value in (-.25, .25, .5, .75, 1):
        out.append(rf"\draw[grid,line width=.3pt] ({left},{q(y(value))}) -- ({q(x(2))},{q(y(value))});")
    def tail(start: Fraction, stop: Fraction) -> None:
        mesh = [start+(stop-start)*Fraction(i,cells) for i in range(cells+1)]
        for a, b in zip(mesh, mesh[1:]):
            lo, hi = sorted((sinc(float(a)), sinc(float(b))))
            out.extend([
                rf"\path[fill=orangefill,draw=orange,line width=.3pt] ({q(x(a))},{q(y(0))}) rectangle ({q(x(b))},{q(y(hi))});",
                rf"\path[fill=tealfill,draw=teal,line width=.3pt] ({q(x(a))},{q(y(0))}) rectangle ({q(x(b))},{q(y(lo))});",
            ])
    tail(Fraction(0), turn_left)
    tail(turn_right, Fraction(2))
    out.append(rf"\path[fill=yellowfill,draw=yellowedge,line width=.55pt] ({q(x(turn_left))},{q(y(-.25))}) rectangle ({q(x(turn_right))},{q(y(0))});")
    curve = [(x(i/300), y(sinc(i/300))) for i in range(601)]
    out += [
        rf"\draw[ink,line width=1.05pt] plot[smooth] coordinates {{{path(curve)}}};",
        rf"\draw[yellowedge,line width=.65pt] ({q(x(turn_left))},{q(y(-.25))}) -- ({q(x(turn_left))},{q(y(1.04))});",
        rf"\draw[yellowedge,line width=.65pt] ({q(x(turn_right))},{q(y(-.25))}) -- ({q(x(turn_right))},{q(y(1.04))});",
        n(x(0), y(0)-12, r"$0$", "anchor=north"),
        n(x(1), y(0)-12, r"$1$", "anchor=north"),
        n(x(2), y(0)-12, r"$2$", "anchor=north"),
        n(x(turn_left)-4, y(0)-23, r"$\ell$", "anchor=north east,text=yellowedge"),
        n(x(turn_right)+4, y(0)-23, r"$r$", "anchor=north west,text=yellowedge"),
        n(x(2)+10, y(0), r"$t$", "anchor=west"),
        n(left+8, y(.88), r"$\frac{\sin(\pi t)}{\pi t}$", "anchor=west"),
    ]
    return "\n".join(out)


def single_turn_animation() -> Animation:
    turns = ((Fraction(1), Fraction(3,2)), (Fraction(7,5), Fraction(29,20)), (Fraction(143,100), Fraction(287,200)), (Fraction(7151,5000), Fraction(3576,2500)))
    return Animation("single-turn-integral", 360, 210, tuple(single_turn_frame(a,b,2**i) for i,(a,b) in enumerate(turns)), (1250,1250,1250,1900), 1)


def words(steps: int) -> list[list[int]]:
    if steps == 0:
        return [[]]
    old = words(steps-1)
    return old + [[steps-1,*word] for word in old]


def peano_frame(steps: int) -> str:
    colours, left, top, tile, row = ("teal","orange","purple"), 125, 190, 33, 26
    out = []
    for number, word in enumerate(words(steps)):
        y = top-number*row
        if not word:
            out += [
                rf"\path[fill=grid,draw=axis,line width=.45pt] ({left},{y}) rectangle ({left+tile},{y+18});",
                n(left+tile/2,y+9,r"$I$"),
            ]
        for column, index in enumerate(word):
            x = left+column*(tile+5)
            out += [
                rf"\path[fill={colours[index]}] ({x},{y}) rectangle ({x+tile},{y+18});",
                rf"\node[font=\small,text=white] at ({x+tile/2},{y+9}) {{$B_{index}$}};",
            ]
    timeline = 28
    out.append(rf"\draw[axis,line width=.65pt] ({left-48},{timeline}) -- ({left+3*(tile+5)+12},{timeline});")
    for index in range(3):
        x = left+index*(tile+5)+tile/2
        out += [
            rf"\draw[axis,line width=.5pt] ({x},{timeline-3}) -- ({x},{timeline+3});",
            n(x,timeline-10,"$"+str(index)+"$","anchor=north"),
        ]
    out.append(n(left-58,timeline,r"$t$","anchor=east"))
    return "\n".join(out)


def peano_animation() -> Animation:
    return Animation("peano-baker-words", 320, 230, tuple(peano_frame(i) for i in range(4)), (1050,1050,1250,1900), 3)


def all_animations() -> tuple[Animation, ...]:
    return (
        circle_animation(),
        kernel_animation("arctan-rectangle-enclosure"),
        sine_animation(),
        sqrt_animation(),
        substitution_animation(),
        ibp_animation(),
        single_turn_animation(),
        ftc_animation(),
        peano_animation(),
    )


def render(animation: Animation) -> None:
    source_dir = SOURCES / animation.name
    source_dir.mkdir(parents=True, exist_ok=True)
    temporary = Path(tempfile.mkdtemp(prefix=animation.name+"-", dir="/tmp"))
    try:
        rendered: list[Path] = []
        for index, body in enumerate(animation.frames):
            source = source_dir / f"frame-{index+1}.tex"
            source.write_text(tex(animation.width, animation.height, body))
            output = temporary / f"frame-{index+1}"
            output.mkdir()
            result = subprocess.run(
                ["pdflatex", "-interaction=batchmode", "-halt-on-error", f"-output-directory={output}", str(source)],
                cwd=output, text=True, capture_output=True,
            )
            if result.returncode:
                raise RuntimeError(f"TikZ compilation failed for {source.relative_to(ROOT)}:\n{result.stdout}\n{result.stderr}")
            pdf = output / (source.stem+".pdf")
            prefix = output / "rendered"
            subprocess.run(["pdftoppm","-png","-r","160",str(pdf),str(prefix)],check=True)
            rendered.append(output/"rendered-1.png")
        frames = [Image.open(image).convert("RGB") for image in rendered]
        width, height = max(frame.width for frame in frames), max(frame.height for frame in frames)
        gif_frames = []
        for frame in frames:
            canvas = Image.new("RGB",(width,height),"white")
            canvas.paste(frame,((width-frame.width)//2,(height-frame.height)//2))
            gif_frames.append(canvas)
        gif, png = ASSETS/(animation.name+".gif"), ASSETS/(animation.name+".png")
        gif_frames[animation.poster].save(png,format="PNG",optimize=True)
        gif_frames[0].save(gif,format="GIF",save_all=True,append_images=gif_frames[1:],duration=list(animation.duration),loop=0,disposal=2,optimize=True)
        print("wrote",gif.relative_to(ROOT))
        print("wrote",png.relative_to(ROOT))
    finally:
        shutil.rmtree(temporary,ignore_errors=True)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    options = [animation.name for animation in all_animations()]
    parser.add_argument("--only",choices=options)
    selected = parser.parse_args().only
    for animation in all_animations():
        if selected is None or animation.name == selected:
            render(animation)


if __name__ == "__main__":
    main()
