#!/usr/bin/env python3
"""Update only the two published chapters about proper and improper integration."""
import argparse
import shutil
from html import escape
from pathlib import Path
from apply_chapter_gifs import update_gaussian_figure, update_integral_figure

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("site", type=Path)
args = parser.parse_args()
site = args.site
assets = Path(__file__).resolve().parents[1] / "blueprint" / "src" / "assets"
destination = "reading/integral-grid"
(site / destination).mkdir(parents=True, exist_ok=True)


def replace_once(page, old, new):
    if page.count(old) != 1:
        raise SystemExit(f"Unexpected integral chapter markup: {old[:100]}")
    return page.replace(old, new, 1)


def figure(name, caption):
    return (f'<figure class="chapter-visual"><img src="{destination}/{name}.gif" '
            f'alt="{escape(caption, quote=True)}" loading="lazy" style="max-width:100%;height:auto">'
            f'<figcaption>{caption}</figcaption></figure>')


asset_names = (
    "single-turn-integral",
    "dirichlet-dyadic-windows",
)
for name in asset_names:
    shutil.copyfile(assets / f"{name}.gif", site / destination / f"{name}.gif")

chapter = site / "ch-integrals.html"
page = chapter.read_text()
if 'id="dyadic-ftc-examples"' not in page:
    page = replace_once(page, 'src="images/img-0003.gif"',
                        f'src="{destination}/arctan-rectangle-enclosure.gif"')
    page = replace_once(page, 'src="images/img-0004.gif"',
                        f'src="{destination}/interval-sine-integral-stage.gif"')
    turned = figure("single-turn-integral",
                    "The cell containing one third gets narrower while its two heights stay fixed.")
    examples = r"""
<section id="dyadic-ftc-examples">
<h2>FTC with supplied certificates</h2>
<p>A fixed-grid integral supplies certified cell ranges with shrinking total error.
The endpoint function supplies a different certificate. Its increments must obey the derivative bounds on each segment.
Summing the increments telescopes, so the integral equals the endpoint difference.
Lean checks this in <code>FTCStepQuadrature.dyadic_ftc</code>.</p>
<p>The reciprocal integral uses endpoint heights (1/t) on this grid.
Its accumulation has derivative (1/x) on the positive represented inputs.
For (1/(1+t^2)), Lean identifies the integral from zero with the geometric
arctangent on the unit chart.</p>
<h3>The squares of sine and cosine</h3>
<p>Let (S(t)=sin(pi t)) and (C(t)=cos(pi t)).
Their derivative laws give ((S^2+C^2)'=0) and ((SC)'=pi(C^2-S^2)).
The initial values give (S^2+C^2=1). For (0le ale ble1), the fixed-grid integrals satisfy</p>
<p>[
int_a^b S(t)^2 ,dt simeq rac{b-a}{2} -
 rac{S(b)C(b)-S(a)C(a)}{2pi},qquad
int_a^b C(t)^2 ,dt simeq rac{b-a}{2} +
 rac{S(b)C(b)-S(a)C(a)}{2pi}.
]</p>
<p>For ([a,b]=[0,1/2]), the product vanishes at both endpoints and each integral equals (1/4).</p>
</section>
"""
    start = '<h2 id="a0000000015">4.4 Finite rules for integrals</h2>'
    page = replace_once(page, start, turned + examples + start)
    chapter.write_text(page)

update_integral_figure(site)

chapter = site / "ch-improper-parameters.html"
page = chapter.read_text()
if 'id="dyadic-improper-examples"' not in page:
    figures = r"""
<section id="dyadic-improper-examples">
<h2>Fixed grids inside moving windows</h2>
<p>For the Gaussian, Lean computes the finite integrals of (e^{-t^2}) on
([-R,R]) using the integer-first dyadic grid. The separate tail estimate
certifies the improper integral. Lean proves agreement with the independent
Taylor quadrature mass. Identifying that mass with (sqrt{pi}) remains open.</p>
"""
    figures += figure("gaussian-dyadic-windows",
                      "The Gaussian window expands and the finite grid refines.")
    figures += r"""
<p>For the Dirichlet integral, the coordinate (t=x/pi) gives the integrand
(sin(pi t)/t). The left cutoff tends to zero as the right cutoff grows.
The finite windows use clipped dyadic cells and the tail estimate comes
from cancellation. Lean checks agreement with Feynman's parameter computation
and the exact value (pi/2).</p>
"""
    figures += figure("dirichlet-dyadic-windows",
                      "The Dirichlet windows omit less near zero and capture more oscillations.")
    figures += "</section>\n"
    start = '<h2 id="thm:parameter-majorant">11.2 Parameter series with an integrable majorant</h2>'
    page = replace_once(page, start, figures + start)
    chapter.write_text(page)

update_gaussian_figure(site)
print("Applied five regenerated GIFs and the checked integral examples to the two existing chapters.")
