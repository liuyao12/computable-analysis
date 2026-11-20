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
from preface_sqrt_tables import decimal_bounds


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
    # Keep a printable source for each settled stage of a continuous animation.
    source_frames: tuple[int, ...] = ()


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


def rectangle_plot() -> list[str]:
    return [
        r"\definecolor{paper}{HTML}{FAF9F5}",
        r"\definecolor{graph}{HTML}{20332E}",
        r"\colorlet{lowerbound}{shared!85!graph}",
        r"\colorlet{upperbound}{yellow!59!graph}",
        r"\colorlet{addition}{lowerbound!76!sharedfill}",
        r"\colorlet{cutoff}{yellow!85!overfill}",
        r"\fill[paper] (0,0) rectangle (259,261);",
        r"\begin{scope}[shift={(37,45)},x=184pt,y=184pt]",
    ]


def rectangle_bound_labels(lower: Fraction, upper: Fraction) -> list[str]:
    bounds = decimal_bounds(lower, upper, minimum_places=3)
    lines = []
    for x, name, value, color in zip((37, 145), ("a", "b"), bounds, ("lowerbound", "upperbound")):
        if "." in value:
            value = value.rstrip("0").rstrip(".")
        lines.append(rf"\node[anchor=west,inner sep=0pt,text={color},font=\large] at ({x},14) {{\({name}={value}\)}};")
    return lines


def kernel_frame(cells: int, phase: str, progress: float) -> str:
    mesh = [Fraction(i, cells) for i in range(cells + 1)]
    fine = [(x, rational_kernel(x)) for x in mesh]
    coarse = fine[::2] if cells > 1 else fine
    clearing = phase == "clear"
    settled = clearing and progress == 1
    active = fine if clearing else coarse
    out = rectangle_plot()

    def stairs(samples):
        lower, upper = [], []
        for (left, high), (right, low) in zip(samples, samples[1:]):
            lower.extend([(left, low), (right, low)])
            upper.extend([(left, high), (right, high)])
        return polygon(lower), polygon(upper)

    lower, upper = stairs(active)
    for line, color in ((upper, "overfill"), (lower, "sharedfill")):
        out.append(rf"\fill[{color}] (0,0) -- {line} -- (1,0) -- cycle;")

    strength = progress if phase == "highlight" else (1-progress if clearing else 0)
    if strength:
        # On the left half the midpoint raises the floor. On the right it lowers the ceiling.
        addition = "sharedfill" if clearing else "overfill"
        removal = "paper" if clearing else "overfill"
        for i in range(1, cells, 2):
            (left, high), (mid, height), (right, low) = fine[i-1:i+2]
            out += [
                rf"\fill[addition!{q(100*strength)}!{addition}] ({q(left)},{q(low)}) rectangle ({q(mid)},{q(height)});",
                rf"\fill[cutoff!{q(100*strength)}!{removal}] ({q(mid)},{q(height)}) rectangle ({q(right)},{q(high)});",
            ]
    for line, color in ((lower, "lowerbound"), (upper, "upperbound")):
        out.append(rf"\draw[{color},line width=.65pt] {line};")
    if clearing and not settled:
        for line, color in zip(stairs(coarse), ("lowerbound", "upperbound")):
            out.append(rf"\draw[{color},opacity={q(1-progress)},line width=.65pt] {line};")
        out.append(rf"\draw[upperbound,opacity={q(1-progress)},line width=.65pt] "
                   rf"(1,{q(active[-2][1])}) -- (1,{q(coarse[-2][1])});")
    out.append(rf"\draw[upperbound,line width=.65pt] (1,0) -- (1,{q(active[-2][1])});")

    if not settled:
        rise = progress if phase == "rays" else 1
        trace = progress if phase == "rectangles" else int(phase in ("highlight", "clear"))
        opacity = q(1-progress if clearing else 1)
        for i in range(1, cells, 2):
            (left, high), (mid, height), (right, low) = fine[i-1:i+2]
            if rise:
                out.append(rf"\draw[graph!72!paper,opacity={opacity},line width=.8pt,dash pattern=on 2.6pt off 2pt] "
                           rf"({q(mid)},0) -- ({q(mid)},{q(height*rise)});")
            if trace:
                for x, y, color in ((left, low, "lowerbound"), (right, high, "upperbound")):
                    # The two new edges grow together from the sample on the curve.
                    edges = [(mid+(x-mid)*trace, height), (mid, height), (mid, height+(y-height)*trace)]
                    out.append(rf"\draw[{color},opacity={opacity},line width=1.15pt,dash pattern=on 3pt off 2pt] {polygon(edges)};")

    curve = [(x/100, 1/(1+(x/100)**2)) for x in range(101)]
    out += [
        r"\draw[graph,line width=.8pt] (-.04,0) -- (1.06,0);",
        r"\draw[graph,line width=.8pt] (0,0) -- (0,1.055);",
        rf"\draw[graph,line width=1.15pt] plot[smooth] coordinates {{{path(curve)}}};",
        n(0, -.01, r"\(0\)", "anchor=north"), n(1, -.01, r"\(1\)", "anchor=north"),
        n(-.02, 1, r"\(1\)", "anchor=east"), n(1.065, 0, r"\(x\)", "anchor=west"),
        n(0, 1.06, r"\(y\)", "anchor=south"),
        n(.54, .808, r"\(\displaystyle\int_0^1 \frac{dx}{1+x^2}\)", "anchor=south west"),
    ]
    for x in mesh:
        out.append(rf"\filldraw[fill=graph,draw=paper,line width=.35pt] ({q(x)},0) circle[radius=1.55pt];")
    for x, y in (coarse if phase == "rays" and progress < 1 else fine):
        out.append(dot(x, y, "graph", 1.4))
    out.append(r"\end{scope}")
    samples = fine if settled else coarse
    heights = [h for _, h in samples]
    count = len(samples)-1
    out.extend(rectangle_bound_labels(sum(heights[1:])/count, sum(heights[:-1])/count))
    return "\n".join(out)


def kernel_animation(name: str) -> Animation:
    return refinement_animation(name, 259, 261, 1, kernel_frame, "rectangles")


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


def sine_box(x: Fraction, stage: int) -> tuple[Fraction, Fraction]:
    """Enclose sin(pi*x/2) at a dyadic node, rounding each half-angle radical outward."""
    if not 0 <= x <= 1 or x.denominator & (x.denominator - 1):
        raise ValueError("A dyadic point of the unit interval is required")

    def radical(t, bits):
        if t == 0 or t == 1:
            return t, t
        # cos(pi*t) is +sin(pi*(1-2*t)/2) on the left and changes sign on the right.
        lo, hi = radical(abs(2*t-1), bits + 3)
        if t <= Fraction(1, 2):
            lo, hi = -hi, -lo
        low, _ = rational_sqrt_bounds((1+lo)/2, bits)
        _, high = rational_sqrt_bounds((1+hi)/2, bits)
        return low, min(Fraction(1), high)

    if x in (0, 1):
        return x, x
    bits = 2*max(stage, x.denominator.bit_length()-1) + 8
    lo, hi = radical(x, bits)
    radius = Fraction(1, 2**(stage+3))

    def margin(clearance):
        # Near a square edge, taper the padding rather than pinning a cap to
        # the edge. Both caps can then move inward on every refinement.
        if clearance >= 2*radius:
            return radius
        return clearance * (1 - clearance/(4*radius))

    return lo-margin(lo), hi+margin(1-hi)


def sine_frame(cells: int, phase: str, progress: float) -> str:
    stage = cells.bit_length()-1
    mesh = [Fraction(i, cells) for i in range(cells+1)]
    coarse = mesh[::2] if cells > 1 else mesh
    boxes = {x: sine_box(x, stage) for x in mesh}
    previous_boxes = {x: sine_box(x, max(0, stage-1)) for x in coarse}
    if phase == "rays":
        # Tighten the previously visible bars in place as the new guides rise.
        p = Fraction(progress).limit_denominator()
        for x in coarse:
            old = previous_boxes[x]
            boxes[x] = tuple((1-p)*a + p*b for a, b in zip(old, boxes[x]))

    clearing = phase == "clear"
    settled = clearing and progress == 1
    active = mesh if clearing else coarse
    shaded = boxes if clearing else previous_boxes
    out = rectangle_plot()
    out.append(r"\definecolor{errorbar}{HTML}{793653}")

    def stairs(nodes, heights):
        lower, upper = [], []
        for left, right in zip(nodes, nodes[1:]):
            lower += [(left, heights[left][0]), (right, heights[left][0])]
            upper += [(left, heights[right][1]), (right, heights[right][1])]
        return polygon(lower), polygon(upper)

    lower, upper = stairs(active, shaded)
    for line, color in ((upper, "overfill"), (lower, "sharedfill")):
        out.append(rf"\fill[{color}] (0,0) -- {line} -- (1,0) -- cycle;")

    strength = progress if phase == "highlight" else (1-progress if clearing else 0)
    if strength:
        add_base = "sharedfill" if clearing else "overfill"
        cut_base = "paper" if clearing else "overfill"
        for i, (left, right) in enumerate(zip(mesh, mesh[1:])):
            # Compare each new cell with the last settled rectangle, including
            # the strips gained or removed when an existing bar tightens.
            parent = i//2
            old_lo = previous_boxes[coarse[parent]][0]
            old_hi = previous_boxes[coarse[parent+1]][1]
            lo, hi = boxes[left][0], boxes[right][1]
            if lo > old_lo:
                out.append(rf"\fill[addition!{q(100*strength)}!{add_base}] ({q(left)},{q(old_lo)}) rectangle ({q(right)},{q(lo)});")
            if hi < old_hi:
                out.append(rf"\fill[cutoff!{q(100*strength)}!{cut_base}] ({q(left)},{q(hi)}) rectangle ({q(right)},{q(old_hi)});")

    for line, color in ((lower, "lowerbound"), (upper, "upperbound")):
        out.append(rf"\draw[{color},line width=.65pt] {line};")
    if clearing and not settled:
        for line, color in zip(stairs(coarse, previous_boxes), ("lowerbound", "upperbound")):
            out.append(rf"\draw[{color},opacity={q(1-progress)},line width=.65pt] {line};")
    if not settled:
        rise = progress if phase == "rays" else 1
        trace = progress if phase == "rectangles" else int(phase in ("highlight", "clear"))
        opacity = q(1-progress if clearing else 1)
        if rise:
            for mid in mesh[1::2]:
                lo = boxes[mid][0]
                out.append(rf"\draw[graph!72!paper,opacity={opacity},line width=.8pt,dash pattern=on 2.6pt off 2pt] "
                           rf"({q(mid)},0) -- ({q(mid)},{q(lo*rise)});")
        if trace:
            for left, mid, right in zip(mesh, mesh[1:], mesh[2:]):
                lo, hi = boxes[mid]
                for cap, end, color in ((lo, right, "lowerbound"), (hi, left, "upperbound")):
                    out.append(rf"\draw[{color},opacity={opacity},line width=1.15pt,dash pattern=on 3pt off 2pt] "
                               rf"({q(mid)},{q(cap)}) -- ({q(mid+(end-mid)*trace)},{q(cap)});")

    # Only the reference curve uses floating-point sine. All construction lines use the boxes.
    curve = [(i/120, math.sin(math.pi*i/240)) for i in range(121)]
    out += [
        r"\draw[graph!48!paper,line width=.55pt] (0,1) -- (1,1) -- (1,0);",
        r"\draw[graph,line width=.8pt] (-.04,0) -- (1.06,0);",
        r"\draw[graph,line width=.8pt] (0,0) -- (0,1.055);",
        rf"\draw[graph,line width=1.05pt] plot[smooth] coordinates {{{path(curve)}}};",
        n(0, -.01, r"\(0\)", "anchor=north"), n(1, -.01, r"\(1\)", "anchor=north"),
        n(-.02, 1, r"\(1\)", "anchor=east"), n(1.065, 0, r"\(x\)", "anchor=west"),
        n(0, 1.06, r"\(y\)", "anchor=south"),
    ]
    for x in mesh:
        out.append(rf"\filldraw[fill=graph,draw=paper,line width=.35pt] ({q(x)},0) circle[radius=1.55pt];")
    out += [dot(0, 0, "graph", 1.4), dot(1, 1, "graph", 1.4)]
    for i, x in enumerate(mesh[1:-1], 1):
        alpha = min(1, max(0, (progress-.75)*4)) if phase == "rays" and i % 2 else 1
        if alpha:
            lo, hi = boxes[x]
            out.append(rf"\draw[errorbar,opacity={q(alpha)},line width=1.25pt] "
                       rf"({q(x)},{q(lo)}) -- ({q(x)},{q(hi)});")
            for cap in (lo, hi):
                out.append(rf"\draw[errorbar,opacity={q(alpha)},line width=1.25pt] "
                           rf"({q(x-.014)},{q(cap)}) -- ({q(x+.014)},{q(cap)});")
    out += [
        r"\end{scope}",
        n(128, 246, r"\(\displaystyle\int_0^1\sin\!\left(\frac{\pi}{2}x\right)\,dx\)"),
        n(221, 246, rf"\(n={stage}\)", "anchor=east"),
    ]
    count = len(active)-1
    out.extend(rectangle_bound_labels(sum(shaded[x][0] for x in active[:-1])/count,
                                      sum(shaded[x][1] for x in active[1:])/count))
    return "\n".join(out)


def sine_animation() -> Animation:
    return refinement_animation("interval-sine-integral-stage", 259, 261, 1, sine_frame, "rectangles")


def circle(value: Fraction) -> tuple[Fraction, Fraction]:
    return ((1 - value * value) / (1 + value * value), 2 * value / (1 + value * value))


def tangent(left: tuple[Fraction, Fraction], right: tuple[Fraction, Fraction]) -> tuple[Fraction, Fraction]:
    determinant = left[0] * right[1] - left[1] * right[0]
    return ((right[1] - left[1]) / determinant, (left[0] - right[0]) / determinant)


def circle_area_bounds(points):
    """Sum the oriented triangle areas about the quarter-disk's center."""
    def twice_area(p, q):
        return p[0]*q[1] - p[1]*q[0]
    lower = upper = Fraction(0)
    for p, q in zip(points, points[1:]):
        vertex = tangent(p, q)
        lower += twice_area(p, q)/2
        upper += (twice_area(p, vertex) + twice_area(vertex, q))/2
    return lower, upper


def circle_frame(cells: int, phase: str, progress: float, *, arctan: bool = False) -> str:
    x0, y0, radius = 180, (18 if arctan else 40), 154
    screen = lambda value: (x0 + radius * value[0], y0 + radius * value[1])
    origin, west, east = screen((0, 0)), screen((-1, 0)), screen((1, 0))
    end = Fraction(2, 3) if arctan else Fraction(1)
    mesh = [end * Fraction(i, cells) for i in range(cells + 1)]
    samples = [circle(t) for t in mesh]
    plotted = [screen(point) for point in samples]
    def corners(points):
        return [screen(tangent(a, b)) for a, b in zip(points, points[1:])]

    def between(a, b, t):
        return tuple(u + (v-u)*t for u, v in zip(a, b))

    outer = corners(samples)
    previous = samples[::2] if cells > 1 else []
    old_arc = [screen(p) for p in previous]
    old_outer = corners(previous)
    clearing = phase == "clear"
    settled = clearing and progress == 1
    arc, vertices = (plotted, outer) if clearing else (old_arc, old_outer)
    trace = progress if phase == "triangles" else int(phase in ("highlight", "clear"))
    highlight = progress if phase == "highlight" else (1-progress if clearing else 0)
    guides = 1-progress if clearing else 1
    out = [
        r"\definecolor{paper}{HTML}{FAF9F5}",
        r"\definecolor{semicircle}{HTML}{20332E}",
        r"\colorlet{lowerbound}{shared!85!semicircle}",
        r"\colorlet{upperbound}{yellow!59!semicircle}",
        rf"\fill[paper] (0,0) rectangle (360,{190 if arctan else 212});",
        r"\colorlet{lowerarea}{sharedfill}",
        r"\colorlet{upperarea}{overfill}",
        r"\colorlet{addition}{lowerbound!76!lowerarea}",
        r"\colorlet{cutoff}{yellow!85!upperarea}",
        r"\tikzset{chord/.style={lowerbound,line width=.65pt},"
        r"tangent/.style={upperbound,line width=.65pt},"
        r"chord trace/.style={chord,line width=1.25pt,dash pattern=on 5.5pt off 2.3pt},"
        r"tangent trace/.style={tangent,line width=1.25pt,dash pattern=on 3.7pt off 2.2pt}}",
    ]
    def fill(points, color):
        out.append(rf"\fill[{color}] {polygon(points)} -- cycle;")

    def stroke(points, style):
        out.append(rf"\draw[{style}] {polygon(points)};")

    if arc:
        fill([origin, arc[0], *vertices, arc[-1]], "upperarea")
        fill([origin, *arc], "lowerarea")

    if highlight:
        strength = q(100*highlight)
        for j, corner in enumerate(old_outer):
            # The new chord pair adds this triangle to the inscribed polygon.
            fill(plotted[2*j:2*j+3], f"addition!{strength}!{'lowerarea' if clearing else 'upperarea'}")
            # The new tangent cuts off exactly the old outer vertex.
            fill([outer[2*j], corner, outer[2*j+1]],
                 f"cutoff!{strength}!{'paper' if clearing else 'upperarea'}")

    out += [
        rf"\draw[semicircle,line width=.85pt] {polygon([west, east])};",
        rf"\draw[semicircle,line width=1.2pt] ({q(east[0])},{y0}) arc[start angle=0,end angle=180,radius={radius}pt];",
    ]
    if arctan:
        stroke([origin, plotted[-1]], "semicircle,line width=.65pt")
        stroke([west, plotted[-1]], "semicircle!42!paper,line width=.5pt")
    if not settled:
        travel = progress if phase == "rays" else 1
        for j in range(1, cells, 2):
            mark, endpoint = screen((0, mesh[j])), plotted[j]
            # Every ray passes its own marked point at the same beat and
            # reaches the arc at the same beat, despite their different lengths.
            tip = (between(west, mark, 2*travel) if travel <= .5
                   else between(mark, endpoint, 2*travel-1))
            if travel:
                stroke([west, tip], f"semicircle!72!paper,opacity={q(guides)},line width=.8pt,dash pattern=on 2.6pt off 2pt")
    if arc and (not clearing or settled):
        stroke(arc, "chord")
        stroke([arc[0], *vertices, arc[-1]], "tangent")
    if previous and not settled:
        for j, corner in enumerate(old_outer):
            a, middle, b = plotted[2*j:2*j+3]
            left, right = outer[2*j:2*j+2]
            if clearing:
                # These pieces of the old tangents survive the corner cut.
                stroke([a, left], "tangent")
                stroke([right, b], "tangent")
                stroke([a, b], f"chord,opacity={q(guides)}")
                stroke([left, corner, right], f"tangent,opacity={q(guides)}")
            if trace:
                stroke([between(middle, a, trace), middle, between(middle, b, trace)], "chord trace")
                stroke([between(middle, left, trace), middle, between(middle, right, trace)], "tangent trace")
    out.append(dot(*west, "semicircle", 1.6))
    reached_arc = phase != "rays" or progress == 1
    out += [dot(*point, "lowerbound", 1.7) for point in (plotted if reached_arc else old_arc)]
    for x, y in (outer if trace == 1 else old_outer):
        out.append(rf"\fill[upperbound] ({q(x-1.4)},{q(y-1.4)}) rectangle ({q(x+1.4)},{q(y+1.4)});")
    if arctan:
        out.append(r"\definecolor{inputsegment}{HTML}{E47773}")
        stroke([origin, screen((0, 1))], "semicircle,line width=.65pt")
        stroke([origin, screen((0, end))], "inputsegment,line width=2.4pt")
    for value in mesh:
        x, y = screen((0, value))
        out.append(rf"\filldraw[fill=semicircle,draw=paper,line width=.35pt] ({q(x)},{q(y)}) circle[radius=1.55pt];")
    if arctan:
        x, y = screen((0, end))
        out.append(rf"\node[anchor=south east,inner sep=1pt,text=semicircle,font=\large] at ({q(x-2)},{q(y+2)}) {{\(t\)}};")
        x, y = screen((.72, .78))
        out.append(rf"\node[anchor=west,inner sep=1pt,text=semicircle,font=\large] at ({q(x)},{q(y)}) {{\(\arctan(t)\)}};")
    else:
        measured = previous if previous and not settled else samples
        lower, upper = decimal_bounds(*circle_area_bounds(measured), minimum_places=1)
        for x, name, value, color in ((44, "a", lower, "lowerbound"), (212, "b", upper, "upperbound")):
            out.append(rf"\node[anchor=west,inner sep=0pt,text={color},font=\large] at ({x},15) {{\({name}={value}\)}};")
    return "\n".join(out)


def circle_animation(*, arctan: bool = False) -> Animation:
    return refinement_animation("arctan-sector" if arctan else "rational-circle-subdivision",
                                360, 190 if arctan else 212, 2 if arctan else 1,
                                lambda cells, phase, p: circle_frame(cells, phase, p, arctan=arctan), "triangles")


def refinement_animation(name, width, height, first, frame, outline_phase) -> Animation:
    frames = [frame(first, "clear", 1)]
    durations, settled = [1400], [0]
    for multiplier in (2, 4, 8):
        cells = first * multiplier
        frames.append(frame(cells, "rays", 0))
        durations.append(330)
        for phase, steps, hold in (("rays", 16, 330), (outline_phase, 12, 260),
                                   ("highlight", 5, 950), ("clear", 8, 1100)):
            for step in range(1, steps+1):
                frames.append(frame(cells, phase, step/steps))
                durations.append(hold if step == steps else 60)
        settled.append(len(frames)-1)
    durations[-1] = 1900
    return Animation(name, width, height, tuple(frames),
                     tuple(durations), settled[-1], tuple(settled))


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


def single_turn_frame(stage: int) -> str:
    origin_x, origin_y = 46, 45
    x = lambda t: origin_x + 274 * float(t)
    y = lambda value: origin_y + 370 * float(value)
    turn = Fraction(1, 3)
    height = Fraction(4, 9)
    spacing = Fraction(1, 2**stage)

    def quadratic(t):
        return (t - turn)**2

    out = [
        rf"\draw[axis] ({origin_x-8},{origin_y}) -- (333,{origin_y});",
        rf"\draw[axis] ({origin_x},37) -- ({origin_x},223);",
    ]
    mesh = [i*spacing for i in range(2**stage + 1)]
    for left, right in zip(mesh, mesh[1:]):
        exceptional = left < turn < right
        low, high = (0, height) if exceptional else sorted((quadratic(left), quadratic(right)))
        out += positive_estimate_cell(x(left), x(right), origin_y, y(low), y(high), .45)
        if exceptional:
            out.append(rf"\draw[gap,line width=1.3pt] ({q(x(left))},{origin_y}) rectangle ({q(x(right))},{q(y(height))});")
    curve = [(x(Fraction(i, 120)), y(quadratic(Fraction(i, 120)))) for i in range(121)]
    out += [
        rf"\draw[curve,line width=1.1pt] plot[smooth] coordinates {{{path(curve)}}};",
        dot(x(turn), origin_y, "curve"),
        n(x(0), 32, r"$0$"),
        n(x(turn), 32, r"$1/3$"),
        n(x(1), 32, r"$1$"),
        n(181, 247, rf"$(t-1/3)^2\qquad n={stage}$"),
        n(181, 14, rf"Fixed heights $0$ and $4/9$\quad exceptional width $2^{{-{stage}}}$"),
    ]
    return "\n".join(out)


def single_turn_animation() -> Animation:
    return Animation("single-turn-integral", 360, 270,
                     tuple(single_turn_frame(stage) for stage in range(5)),
                     (1250, 1250, 1250, 1250, 1900), 2)


def improper_frame(stage: int, gaussian: bool) -> str:
    radius = stage + 1
    spacing = Fraction(1, 2**stage)
    left = -radius if gaussian else Fraction(1, radius)
    right = radius
    x_min = -4 if gaussian else 0
    x_max = 4
    x = lambda t: 44 + 276 * (float(t) - x_min) / (x_max - x_min)
    y = lambda v: 78 + (115 if gaussian else 115/math.pi) * v
    if gaussian:
        curve_value = lambda t: math.exp(-t*t)
        function = r"$e^{-t^2}$"
        tail = rf"$[-{radius},{radius}]\qquad\mathrm{{tail\ budget}}\  C/{radius}$"
    else:
        curve_value = lambda t: math.sin(math.pi*t)/t if t else math.pi
        function = r"$\sin(\pi t)/t$"
        tail = rf"$[1/{radius},{radius}]\qquad\mathrm{{error\ budget}}\ 10/{radius}$"
    mesh = [left] + [j*spacing for j in range(math.floor(left/spacing)+1, math.ceil(right/spacing))] + [right]
    out = [
        rf"\path[fill=sharedfill!20] ({q(x(left))},46) rectangle ({q(x(right))},202);",
        rf"\draw[axis] (38,78) -- (330,78);",
    ]
    for t in mesh:
        out.append(rf"\draw[grid,line width=.35pt] ({q(x(t))},51) -- ({q(x(t))},198);")
    for t in range(x_min, x_max+1):
        out.append(n(x(t), 39, rf"${t}$"))
    curve = [(x(t), y(curve_value(t))) for i in range(401) for t in [x_min+(x_max-x_min)*i/400]]
    out += [
        rf"\draw[curve,line width=1pt] plot[smooth] coordinates {{{path(curve)}}};",
        n(181, 222, rf"{function}\qquad $n={stage}$".replace(r"\qquad", r"\hspace{1em}")),
        n(181, 17, tail),
    ]
    return "\n".join(out)


def improper_animation(name: str, gaussian: bool) -> Animation:
    return Animation(name, 360, 240, tuple(improper_frame(stage, gaussian) for stage in range(4)),
                     (1300, 1300, 1300, 2000), 2)


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
        circle_animation(arctan=True),
        kernel_animation("arctan-rectangle-enclosure"),
        sine_animation(),
        sqrt_animation(),
        substitution_animation(),
        ibp_animation(),
        single_turn_animation(),
        improper_animation("gaussian-dyadic-windows", True),
        improper_animation("dirichlet-dyadic-windows", False),
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
            output = temporary / f"frame-{index+1}"
            output.mkdir()
            if not animation.source_frames:
                source = source_dir / f"frame-{index+1}.tex"
            elif index in animation.source_frames:
                source = source_dir / f"frame-{animation.source_frames.index(index)+1}.tex"
            else:
                source = output / "motion.tex"
            source.write_text(tex(animation.width, animation.height, body))
            result = subprocess.run(
                ["pdflatex", "-interaction=batchmode", "-halt-on-error", f"-output-directory={output}", str(source)],
                cwd=output, text=True, capture_output=True,
            )
            if result.returncode:
                raise RuntimeError(f"TikZ compilation failed for {source}:\n{result.stdout}\n{result.stderr}")
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
