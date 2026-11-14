#!/usr/bin/env python3
"""Apply the integral chapter revision to its existing verified Pages HTML."""
import argparse
from pathlib import Path

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("site", type=Path)
args = parser.parse_args()
page = args.site / "ch-integrals.html"
original = page.read_text()
html = original


def replace_once(old, new):
    global html
    if html.count(old) != 1:
        raise SystemExit(f"Unexpected integral chapter markup: {old[:100]}")
    html = html.replace(old, new, 1)


replace_once(
    'A sample tells us the value at one point; it can miss a narrow peak elsewhere in the cell. For this rectangle construction, the first task is therefore to bound the whole cell, so multiplying by its length gives a justified contribution.',
    r'The grid is the same for every integrand: level \(0\) uses the integers, level \(1\) adds the half-integers, and level \(n\) uses \(k/2^n\). A sample can miss a peak elsewhere in its cell, so certify a bound on the whole cell before multiplying by its length.',
)
replace_once(
    '<p> A rational tagged partition is </p>',
    r'''<p>Keep the points of the grid inside \([a,b]\) and include the two endpoints. For example, \([1/3,8/3]\) starts with \(1/3,1,2,8/3\); only the end cells are clipped. On \([1,3]\), the decreasing rate \(1/t\) uses \([1,2]\) and \([2,3]\) at level \(0\). The right endpoint values sum to \(5/6\), and the left endpoint values sum to \(3/2\). At level \(1\), insert \(3/2\) and \(5/2\).</p>
<p>With a rational tag in each cell, the partition has the form</p>''',
)
replace_once(
    'A supplied sequence of partitions and sound cell enclosures is an integral construction if its rectangle widths shrink to every positive rational tolerance.',
    'At each level of the fixed dyadic grid, supply sound cell enclosures. This is an integral construction if the total upper-minus-lower rectangle area tends to zero.',
)
replace_once(
    'Changing tags, using unequal subdivisions, or refining values faster than the mesh therefore does not change the integral.',
    'Different precision schedules and other subdivisions give equivalent values when their soundness and shrinking gaps are proved. Some existing Lean evaluators still use a uniform grid scaled to the interval or a cell count chosen from a tolerance.',
)
replace_once(
    r'choose mesh at most \(\mu _g(\eta )\) and evaluate',
    r'take a dyadic level with \(2^{-n}\le\mu_g(\eta)\) and evaluate',
)
replace_once(
    'A finite partition into monotone pieces gives the same result.',
    r'''On cells known to be monotone, use the corresponding endpoint bounds.</p>
<p>On cells containing an unresolved turn, the heights can stay fixed as the cells get narrower. For \(g(t)=(t-1/3)^2\) on \([0,1]\), use \(0\) and \(4/9\) on the one cell containing \(1/3\). Its contribution to the uncertainty is at most \((4/9)2^{-n}\). More generally, fixed heights work when the total length of the exceptional cells tends to zero. If that length does not shrink, use a shrinking oscillation bound instead; a supplied Lipschitz constant \(C\) gives the bound \(C2^{-n}\), even when the function has infinitely many turns.</p>
<p>For an improper integral, use the same grid on each finite truncation. Prove a separate bound on the omitted tail and choose the cutoff and grid level so that both errors tend to zero.''',
)
page.write_text(html)
print("Updated the existing integral chapter; all other Pages files are untouched.")
