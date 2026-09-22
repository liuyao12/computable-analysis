#!/usr/bin/env python3
"""Add the checked Leibniz dependency note without changing existing reader content."""
import argparse
import hashlib
import json
import re
from pathlib import Path


def digest(data):
    return hashlib.sha256(data).hexdigest()


def install(site, revision, audit, closure):
    assert re.fullmatch(r'[0-9a-f]{40}', revision)
    log = audit.read_text()
    assert 'PASS: distinct elaborated proof paths' in log
    assert 'error:' not in log and 'sorryAx' not in log
    text = closure.read_text()
    computational, taylor = text.split('\n\nTAYLOR / FTC\n')
    mesh = 'ComputableAnalysis.PiProofs.leibnizEqualsRectangleRawAtOne_finiteRiemannBridge'
    ftc = 'ComputableAnalysis.Taylor.ArctanKernel.kernelPartial_exactCellOrder'
    assert mesh in computational.splitlines() and ftc not in computational.splitlines()
    assert ftc in taylor.splitlines() and mesh not in taylor.splitlines()
    page = site / 'ch-infinite-series.html'
    before = page.read_bytes()
    original = before.decode()
    assert 'id="leibniz-geometric-benchmark"' not in original
    marker = '</div></article>'
    assert original.count(marker) == 1
    source = f'https://github.com/liuyao12/computable-analysis/blob/{revision}/ComputableAnalysis/'
    section = r'''
<section id="leibniz-geometric-benchmark" aria-labelledby="leibniz-benchmark-title" style="scroll-margin-top:6rem">
<h2 id="leibniz-benchmark-title">6.6 Alternative computations of π</h2>
<p>The canonical value remains the geometric exhaustion construction
\(\pi=4A(1)\). The Leibniz series is a certified alternative computation:</p>
<div class="displaymath">\[\pi=4\left(1-\frac13+\frac15-\cdots\right).\]</div>
<p>For the inclusive partial sum \(S_N=4\sum_{k=0}^{N}(-1)^k/(2k+1)\),
the explicit bound is \(|S_N-\pi|\leq 4/(2N+3)\). The interval inequalities
hold for every series index and every independently chosen geometric stage.</p>
<p>Two checked proofs reach the same geometric value. The computational proof
uses finite rational rectangle-sum invariants and a vanishing mesh-error
bound. The second proof integrates the finite geometric identity</p>
<div class="displaymath">\[\frac1{1+x^2}=\sum_{k=0}^{N}(-1)^k x^{2k}
+(-1)^{N+1}\frac{x^{2N+2}}{1+x^2}.\]</div>
<p>Quantitative monomial primitive certificates give exact integral order
for every degree. They yield
\(A(1)=\sum_{k=0}^{N}(-1)^k/(2k+1)+R_N\), with
\(|R_N|\leq 1/(2N+3)\). Neither proof uses the other's comparison theorem.</p>
<pre style="overflow-x:auto;font-size:12px;line-height:1.7">                 Leibniz theorem
          /                         \
 interval invariant              arctan expansion
        |                              |
 geometric exhaustion          finite geometric identity
        |                              |
     geometric π                 FTC + remainder</pre>
<p>The reusable components are alternating-prefix bounds, finite geometric
division, certified interval convergence, and finite-difference integral order.
</p>
<p><a href="SOURCELeibnizPi.lean">Computational theorem</a> ·
<a href="SOURCELeibnizPiTaylor.lean">FTC theorem and remainder</a> ·
<a href="reading/leibniz-dependency-closure.txt">Elaborated dependency closure</a></p>
</section>
'''.replace('SOURCE', source)
    after = original.replace(marker, section + marker)
    assert after.replace(section, '', 1) == original
    protected = {str(p.relative_to(site)): digest(p.read_bytes())
                 for p in site.rglob('*') if p.is_file() and p != page}
    page.write_text(after)
    out = site / 'reading'
    out.mkdir(exist_ok=True)
    (out / 'leibniz-dependency-closure.txt').write_bytes(closure.read_bytes())
    (out / 'leibniz-proof-check.log').write_bytes(audit.read_bytes())
    assert all(digest((site / p).read_bytes()) == h for p, h in protected.items())
    report = {
        'proofSourceCommit': revision,
        'canonicalPi': 'ComputableAnalysis.piCircleArea',
        'theorems': ['ComputableAnalysis.pi_eq_leibniz', 'ComputableAnalysis.pi_eq_leibniz_taylor'],
        'independentProofPaths': True,
        'allPreviousContentPreserved': True,
        'interactiveGraphAdded': False,
        'previousPageSha256': digest(before),
        'pageSha256': digest(page.read_bytes()),
        'auditSha256': digest(audit.read_bytes()),
        'closureSha256': digest(closure.read_bytes()),
    }
    (out / 'leibniz-benchmark.json').write_text(json.dumps(report, indent=2) + '\n')
    print('PASS: Leibniz note added; all prior page content and other artifacts preserved')


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--site', type=Path, required=True)
    parser.add_argument('--revision', required=True)
    parser.add_argument('--audit', type=Path, required=True)
    parser.add_argument('--closure', type=Path, required=True)
    args = parser.parse_args()
    install(args.site, args.revision, args.audit, args.closure)
