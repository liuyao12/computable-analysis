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
% Integral diagrams use exactly one semantic palette: blue for the
% lower-only part, yellow for the upper-only (or still unresolved) part, and
% green for their common part.  The common part is explicit rather than an
% alpha blend, so the three meanings stay distinct after GIF quantization.
\definecolor{blue}{RGB}{0,114,178}
\definecolor{bluefill}{RGB}{86,180,233}
\definecolor{yellow}{RGB}{230,159,0}
\definecolor{yellowfill}{RGB}{255,218,102}
\definecolor{green}{RGB}{0,128,84}
\definecolor{greenfill}{RGB}{89,190,142}
\definecolor{orange}{RGB}{234,88,12}
\definecolor{orangefill}{RGB}{254,215,170}
\definecolor{purple}{RGB}{126,34,206}
\definecolor{yellowedge}{RGB}{202,138,4}
\definecolor{projection}{RGB}{148,163,184}
\colorlet{under}{blue}
\colorlet{underfill}{bluefill}
\colorlet{over}{yellow}
\colorlet{overfill}{yellowfill}
\colorlet{shared}{green}
\colorlet{sharedfill}{greenfill}
\colorlet{gap}{yellow}
\colorlet{gapfill}{yellowfill}
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


def polygon(points: list[tuple[float, float]]) -> str:
    return " -- ".join(f"({q(x)},{q(y)})" for x, y in points)


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


def positive_estimate_cell(
    left: float, right: float, baseline: float, lower: float, upper: float,
    line_width: float,
) -> list[str]:
    """Render a nested positive lower/upper estimate with semantic fills.

    Blue and yellow are the two estimate colours; green is the part common to
    both.  This explicit partition is intentionally used instead of relying
    on raster alpha compositing, so every GIF has the same three-colour
    meaning.
    """
    return [
        rf"\path[fill=sharedfill] ({q(left)},{q(baseline)}) rectangle ({q(right)},{q(lower)});",
        rf"\path[fill=overfill] ({q(left)},{q(lower)}) rectangle ({q(right)},{q(upper)});",
        rf"\draw[under,draw opacity=.8,line width={q(line_width)}pt] ({q(left)},{q(baseline)}) rectangle ({q(right)},{q(lower)});",
        rf"\draw[over,draw opacity=.8,line width={q(line_width)}pt] ({q(left)},{q(baseline)}) rectangle ({q(right)},{q(upper)});",
    ]


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
        out += positive_estimate_cell(
            lx, rx, y0,
            y0 + float(rational_kernel(right)) * unit,
            y0 + float(rational_kernel(left)) * unit,
            .45,
        )
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


def rational_sqrt_bounds(value: Fraction, bits: int) -> tuple[Fraction, Fraction]:
    """A rational enclosing interval for sqrt(value), via integer arithmetic."""
    if value == 0:
        return Fraction(0), Fraction(0)
    scale = 1 << bits
    numerator = value.numerator * scale * scale
    quotient = numerator // value.denominator
    lower_int = math.isqrt(quotient)
    return Fraction(lower_int, scale), Fraction(lower_int + 1, scale)


def viete_pi_bounds(depth: int) -> tuple[Fraction, Fraction]:
    """Return the consecutive Viète nested-radical bounds used at a stage.

    The animation is deliberately schematic about the underlying evaluator,
    but the pointwise boxes now come from a genuine nested-radical precision
    schedule rather than one shared arbitrary guard.
    """
    radical_lo, radical_hi = rational_sqrt_bounds(Fraction(2), 24)
    factor_lo, factor_hi = rational_sqrt_bounds(radical_lo / 2, 24)
    product_lo, product_hi = factor_lo, factor_hi
    for _ in range(max(0, depth - 1)):
        radical_lo, _ = rational_sqrt_bounds(2 + radical_lo, 24)
        _, radical_hi = rational_sqrt_bounds(2 + radical_hi, 24)
        factor_lo, _ = rational_sqrt_bounds((2 + radical_lo) / 4, 24)
        _, factor_hi = rational_sqrt_bounds((2 + radical_hi) / 4, 24)
        product_lo *= factor_lo
        product_hi *= factor_hi
    lower = 2 / product_hi
    upper = 2 / product_lo
    return lower, upper


def sine_box(value: Fraction, stage: int) -> tuple[float, float]:
    # The integral is restricted to [0, 1/2].  At dyadic inputs in this
    # interval, the sine values can be evaluated by the usual half-angle
    # nested-radical chain.  The drawing suppresses that implementation and
    # shows only its stage-dependent output enclosure.  The deliberately
    # visible guard represents the finite radical depth at the current stage;
    # it also grows mildly with the angle, so all bars are not identical.
    if value == 0:
        return 0.0, 0.0
    if value == Fraction(1, 2):
        return 1.0, 1.0
    pi_lower, pi_upper = viete_pi_bounds(stage + 2)
    pi_mid = (pi_lower + pi_upper) / 2
    angle = value * pi_mid
    terms = stage + 2
    estimate = sum(
        (1 if index % 2 == 0 else -1)
        * angle ** (2 * index + 1)
        / math.factorial(2 * index + 1)
        for index in range(terms + 1)
    )
    # The half-angle/nested-radical work is performed only to the current
    # finite stage.  Keep a visible, location-dependent guard in the drawing:
    # later stages narrow it, while points farther from zero carry slightly
    # more propagated angle uncertainty.  This is a visual enclosure budget,
    # not a claim that the displayed irrational value has been attained.
    radical_guard = Fraction(3, 2 ** (stage + 5)) * (1 + 2 * value)
    input_error = value * (pi_upper - pi_lower) + radical_guard
    remainder = abs(angle) ** (2 * terms + 3) / math.factorial(2 * terms + 3)
    guard = max(input_error + remainder, Fraction(1, 2 ** (stage + 5)))
    return float(max(Fraction(0), estimate - guard)), float(min(Fraction(1), estimate + guard))


def sine_frame(stage: int) -> str:
    # This is the integral on [0, 1/2], not the whole sine arch on [0, 1].
    x0, y0, xunit, yunit = 52, 35, 280, 155
    out = [
        rf"\draw[axis,line width=.75pt] ({x0-12},{y0}) -- ({x0+xunit+13},{y0});",
        rf"\draw[axis,line width=.75pt] ({x0},{y0-11}) -- ({x0},{y0+yunit+13});",
    ]
    cells = 2 ** stage
    mesh = [Fraction(i, 2 * cells) for i in range(cells + 1)]
    boxes = {t: sine_box(t, stage) for t in mesh}
    for t in mesh:
        x = x0 + 2 * float(t) * xunit
        out += [
            rf"\draw[grid,line width=.3pt] ({q(x)},{y0}) -- ({q(x)},{y0+yunit});",
            rf"\draw[axis,line width=.55pt] ({q(x)},{y0-3}) -- ({q(x)},{y0+3});",
        ]
    for left, right in zip(mesh, mesh[1:]):
        lx, rx = x0 + 2 * float(left) * xunit, x0 + 2 * float(right) * xunit
        lower = min(boxes[left][0], boxes[right][0])
        upper = max(boxes[left][1], boxes[right][1])
        # sin(pi*x) has one known turning point.  A cell containing x=1/2
        # must include the peak in its upper rectangle even when the mesh has
        # not yet placed a sample point at that turn.
        if left <= Fraction(1, 2) <= right:
            upper = 1.0
        out += positive_estimate_cell(
            lx, rx, y0,
            y0 + lower * yunit,
            y0 + upper * yunit,
            .45,
        )
    curve = [
        (x0 + xunit * i / 150, y0 + yunit * math.sin(math.pi * i / 300))
        for i in range(151)
    ]
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
        n(x0 + xunit / 2, y0 - 12, r"$\frac14$", "anchor=north"),
        n(x0 + xunit, y0 - 12, r"$\frac12$", "anchor=north"),
        n(x0 - 10, y0 + yunit, r"$1$", "anchor=east"),
        n(x0 + xunit + 12, y0 - 2, r"$x$", "anchor=west"),
        n(x0 + 125, y0 + 109, r"$\sin(\pi x)$"),
        n(x0 + xunit / 2, y0 + yunit + 19,
          rf"$\int_0^{{1/2}}\sin(\pi x)\,dx$",
          "anchor=south"),
    ]
    return "\n".join(out)


def sine_animation() -> Animation:
    stages = (0, 1, 2, 3)
    return Animation("interval-sine-integral-stage", 360, 230, tuple(sine_frame(stage) for stage in stages), (1200, 1200, 1200, 1900), 1)


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
        rf"\path[fill=overfill] ({q(origin[0])},{q(origin[1])}) -- {polygon([plotted[0], *outer, plotted[-1]])} -- cycle;",
        rf"\path[fill=sharedfill] ({q(origin[0])},{q(origin[1])}) -- {polygon(plotted)} -- cycle;",
        rf"\draw[under,draw opacity=.8,line width=.45pt] ({q(origin[0])},{q(origin[1])}) -- {polygon(plotted)} -- cycle;",
        rf"\draw[over,draw opacity=.8,line width=.45pt] ({q(origin[0])},{q(origin[1])}) -- {polygon([plotted[0], *outer, plotted[-1]])} -- cycle;",
    ]
    for value, endpoint in zip(mesh, plotted):
        vertical = screen((0, value))
        out += [
            rf"\draw[projection,line width=.5pt] ({q(west[0])},{q(west[1])}) -- ({q(endpoint[0])},{q(endpoint[1])});",
            rf"\draw[grid,line width=.5pt] ({q(vertical[0]-3)},{q(vertical[1])}) -- ({q(vertical[0]+3)},{q(vertical[1])});",
            dot(*vertical, "axis", 1.3),
        ]
    out += [
        rf"\draw[under,line width=1.1pt] plot coordinates {{{path(plotted)}}};",
        rf"\draw[over,line width=1.1pt] plot coordinates {{{path([plotted[0], *outer, plotted[-1]])}}};",
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
    left, right = 57, 300
    t_base, x_base, height = 136, 39, 45
    x = lambda value: left + float(value) * (right - left)
    mesh = [Fraction(i, cells) for i in range(cells + 1)]
    out = [
        rf"\draw[axis,line width=.75pt] ({left-10},{t_base}) -- ({right+14},{t_base});",
        rf"\draw[axis,line width=.75pt] ({left},{t_base-8}) -- ({left},{t_base+height+11});",
        rf"\draw[axis,line width=.75pt] ({left-10},{x_base}) -- ({right+14},{x_base});",
        rf"\draw[axis,line width=.75pt] ({left},{x_base-8}) -- ({left},{x_base+height+11});",
    ]
    for start, stop in zip(mesh, mesh[1:]):
        lx, rx = x(start), x(stop)
        lower_height = 2 * float(start) * height
        curve_points = [(lx, t_base + lower_height)] + [
            (x(start + (stop - start) * Fraction(k, 16)),
             t_base + 2 * float(start + (stop - start) * Fraction(k, 16)) * height)
            for k in range(17)
        ] + [(rx, t_base + lower_height)]
        out += [
            rf"\path[fill=gapfill] plot[smooth] coordinates {{{path(curve_points)}}} -- cycle;",
            rf"\path[fill=underfill,draw=under,draw opacity=.8,line width=.4pt] ({q(lx)},{t_base}) rectangle ({q(rx)},{q(t_base+lower_height)});",
            rf"\path[fill=underfill,draw=under,draw opacity=.8,line width=.4pt] ({q(x(start*start))},{x_base}) rectangle ({q(x(stop*stop))},{q(x_base+height)});",
        ]
    for value in mesh:
        t, image = x(value), x(value * value)
        out += [
            rf"\draw[projection,line width=.45pt] ({q(t)},{t_base-4}) -- ({q(image)},{x_base+height+4});",
            rf"\draw[axis,line width=.55pt] ({q(t)},{t_base-3.5}) -- ({q(t)},{t_base+3.5});",
            rf"\draw[axis,line width=.55pt] ({q(image)},{x_base-3.5}) -- ({q(image)},{x_base+3.5});",
        ]
    top_curve = [(x(i / 80), t_base + 2 * (i / 80) * height) for i in range(81)]
    out += [
        rf"\draw[curve,line width=1.05pt] plot[smooth] coordinates {{{path(top_curve)}}};",
        rf"\draw[curve,line width=1.05pt] ({left},{q(x_base+height)}) -- ({right},{q(x_base+height)});",
        n(left, t_base-12, r"$0$", "anchor=north"),
        n(right, t_base-12, r"$1$", "anchor=north"),
        n(left, x_base-12, r"$0$", "anchor=north"),
        n(right, x_base-12, r"$1$", "anchor=north"),
        n(right+13, t_base-2, r"$t$", "anchor=west"),
        n(right+13, x_base-2, r"$x$", "anchor=west"),
        n(left+60, t_base+41, r"$\int_0^1 2t\,dt$", "anchor=south"),
        n(left+60, x_base+height+10, r"$\int_0^1 1\,dx$", "anchor=south"),
        n(right+18, 86, r"$x=t^2$", "anchor=west,text=axis"),
    ]
    return "\n".join(out)


def substitution_animation() -> Animation:
    return Animation("substitution-partition", 360, 245, tuple(substitution_frame(i) for i in (1, 2, 4, 8)), (1200, 1200, 1200, 1900), 2)


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
        out += [
            rf"\path[fill=sharedfill,draw=shared,draw opacity=.8,line width=.3pt] ({q(x(lf))},{bottom}) rectangle ({q(x(rf_))},{q(y(lg))});",
            rf"\path[fill=sharedfill,draw=shared,draw opacity=.8,line width=.3pt] ({left},{q(y(lg))}) rectangle ({q(x(lf))},{q(y(rg))});",
            rf"\path[fill=gapfill,draw=gap,draw opacity=.8,line width=.4pt] ({q(x(lf))},{q(y(lg))}) rectangle ({q(x(rf_))},{q(y(rg))});",
        ]
    horizontal, vertical = [(x(f[0]), y(g[0]))], [(x(f[0]), y(g[0]))]
    for lf, rf_, lg, rg in zip(f, f[1:], g, g[1:]):
        horizontal += [(x(rf_), y(lg)), (x(rf_), y(rg))]
        vertical += [(x(lf), y(rg)), (x(rf_), y(rg))]
    out += [
        rf"\draw[ink,line width=.8pt] plot coordinates {{{path(horizontal)}}};",
        rf"\draw[ink,line width=.8pt] plot coordinates {{{path(vertical)}}};",
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
        rf"\draw[ink,line width=1.05pt] plot[smooth] coordinates {{{path(primitive)}}};",
        rf"\draw[ink,line width=1.8pt] ({q(px(1))},{base}) -- ({q(px(1))},{q(y(1))});",
    ]
    mesh = [Fraction(i, cells) for i in range(cells+1)]
    for left, right in zip(mesh, mesh[1:]):
        out += positive_estimate_cell(
            dx(left), dx(right), base, y(2 * left), y(2 * right), .4
        )
    out += [
        rf"\draw[curve,line width=1.05pt] plot coordinates {{{path(derivative)}}};",
        n(px(1)-3, y(1)+11, r"$F(1)-F(0)$", "anchor=south west,text=ink"),
        n(pleft+unit+11, base, r"$t$", "anchor=west"),
        n(dleft+unit+11, base, r"$t$", "anchor=west"),
    ]
    return "\n".join(out)


def ftc_animation() -> Animation:
    return Animation("ftc-endpoint-comparison", 370, 270, tuple(ftc_frame(i) for i in (1, 2, 4, 8)), (1200, 1200, 1200, 1900), 2)


def sinc(value: float) -> float:
    """The rational-input test function x |-> sin(pi x) / x.

    The value at zero is pi, so it is an interval value in the eventual raw
    evaluator.  Here the plotted curve is only a guide; the animated cells
    still stand for rational enclosures.
    """
    return math.pi if value == 0 else math.sin(math.pi*value)/value


def single_turn_frame(turn_left: Fraction, turn_right: Fraction, cells: int) -> str:
    left, base, trig, vertical = 47, 84, 45, 44
    x, y = lambda v: left+float(v)*math.pi*trig, lambda v: base+float(v)*vertical
    out = [
        rf"\draw[axis,line width=.75pt] ({left-10},{q(y(0))}) -- ({q(x(2)+12)},{q(y(0))});",
        rf"\draw[axis,line width=.75pt] ({left},{q(y(-.9)-10)}) -- ({left},{q(y(3.65)+10)});",
    ]
    for value in (Fraction(1,2), Fraction(1), Fraction(3,2)):
        out.append(rf"\draw[grid,line width=.3pt] ({q(x(value))},{q(y(-.9))}) -- ({q(x(value))},{q(y(3.65))});")
    for value in (-.75, -.5, -.25, .5, 1, 2, 3):
        out.append(rf"\draw[grid,line width=.3pt] ({left},{q(y(value))}) -- ({q(x(2))},{q(y(value))});")
    mesh = [Fraction(2*i, cells) for i in range(cells+1)]
    turn = 1.430296653
    gap_values = (sinc(float(turn_left)), sinc(turn), sinc(float(turn_right)))
    gap_lo, gap_hi = min(gap_values), max(gap_values)
    for a, b in zip(mesh, mesh[1:]):
            va, vb = sinc(float(a)), sinc(float(b))
            if b <= turn_left:
                # The function is decreasing before the unique interior turn.
                lo, hi = vb, va
                kind = "decreasing"
            elif a >= turn_right:
                # It is increasing after the turn.
                lo, hi = va, vb
                kind = "increasing"
            else:
                # This is the one cell whose finite critical-point bracket is
                # needed.  Include the turn value with both endpoints.
                lo, hi = min(va, vb, sinc(turn)), max(va, vb, sinc(turn))
                kind = "turn"
            # A signed lower/upper cell has a common part and, away from the
            # axis, exactly one exclusive strip.  Draw that partition
            # explicitly.  This preserves the under/over semantics while
            # keeping the shared green unmistakable in the GIF's negative
            # lobe; alpha compositing alone was too close to blue there.
            left_px, right_px, zero = q(x(a)), q(x(b)), q(y(0))
            if lo >= 0:
                out.extend([
                    rf"\path[fill=sharedfill] ({left_px},{zero}) rectangle ({right_px},{q(y(lo))});",
                    rf"\path[fill=overfill] ({left_px},{q(y(lo))}) rectangle ({right_px},{q(y(hi))});",
                ])
            elif hi <= 0:
                out.extend([
                    rf"\path[fill=sharedfill] ({left_px},{zero}) rectangle ({right_px},{q(y(hi))});",
                    rf"\path[fill=underfill] ({left_px},{q(y(hi))}) rectangle ({right_px},{q(y(lo))});",
                ])
            else:
                out.extend([
                    rf"\path[fill=overfill] ({left_px},{zero}) rectangle ({right_px},{q(y(hi))});",
                    rf"\path[fill=underfill] ({left_px},{zero}) rectangle ({right_px},{q(y(lo))});",
                ])
            out.extend([
                rf"\draw[over,draw opacity=.8,line width=.3pt] ({left_px},{zero}) rectangle ({right_px},{q(y(hi))});",
                rf"\draw[under,draw opacity=.8,line width=.3pt] ({left_px},{zero}) rectangle ({right_px},{q(y(lo))});",
            ])
            if kind == "turn":
                out.append(rf"\draw[gap,line width=.55pt] ({left_px},{q(y(lo))}) rectangle ({right_px},{q(y(hi))});")
    curve = [(x(i/300), y(sinc(i/300))) for i in range(601)]
    out += [
        rf"\draw[ink,line width=1.05pt] plot[smooth] coordinates {{{path(curve)}}};",
        rf"\draw[gap,line width=.65pt] ({q(x(turn_left))},{q(y(gap_lo))}) -- ({q(x(turn_left))},{q(y(gap_hi))});",
        rf"\draw[gap,line width=.65pt] ({q(x(turn_right))},{q(y(gap_lo))}) -- ({q(x(turn_right))},{q(y(gap_hi))});",
        dot(x(turn), y(sinc(turn)), "gap", 1.45),
        n(x(0), y(0)-12, r"$0$", "anchor=north"),
        n(x(1), y(0)-12, r"$1$", "anchor=north"),
        n(x(2), y(0)-12, r"$2$", "anchor=north"),
        n(x(turn_left)-4, y(0)-23, r"$\ell$", "anchor=north east,text=gap"),
        n(x(turn_right)+4, y(0)-23, r"$r$", "anchor=north west,text=gap"),
        n(x(2)+10, y(0), r"$x$", "anchor=west"),
        n(x(Fraction(1,4)), y(3.36), r"$\frac{\sin(\pi x)}{x}$", "anchor=west"),
        n(x(Fraction(1,4)), y(-.75),
          r"equal cells: decreasing / turn-cell / increasing",
          "anchor=west,text=ink"),
    ]
    return "\n".join(out)


def single_turn_animation() -> Animation:
    turns = ((Fraction(1), Fraction(3,2)), (Fraction(7,5), Fraction(29,20)), (Fraction(143,100), Fraction(287,200)), (Fraction(7151,5000), Fraction(3576,2500)))
    return Animation("single-turn-integral", 360, 270, tuple(single_turn_frame(a,b,2**i) for i,(a,b) in enumerate(turns)), (1250,1250,1250,1900), 1)


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
