#!/usr/bin/env python3
"""Add a checked ODE supplement while preserving all prior reader bytes."""
import argparse
import hashlib
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
PAGE = 'fuchs-painleve.html'
MARKER = '<!-- algebraic-ode -->'
EXPECTED = ['Expr.evalRaw_valid', 'Expr.evalRaw_equiv', 'Expr.evalRaw_ofRat',
            'Fuchs.polynomial_classification', 'Fuchs.polynomial_equation',
            'Fuchs.radical_euler', 'Painleve.affine_classification',
            'Painleve.simple_pole_classification', 'Painleve.poleSolution',
            'Tests.negativePole_represented']

def sha(data):
    return hashlib.sha256(data).hexdigest()

def install(site, revision, audit):
    assert re.fullmatch(r'[0-9a-f]{40}', revision)
    log = audit.read_text()
    assert 'error:' not in log and 'sorryAx' not in log
    for name in EXPECTED:
        assert "'ComputableAnalysis.AlgebraicODE." + name + "' depends on axioms:" in log, name
    before = {str(p.relative_to(site)): p.read_bytes() for p in site.rglob('*') if p.is_file()}
    assert PAGE not in before
    page = (ROOT / 'book/algebraic-ode/index.html').read_text().replace('__REVISION__', revision)
    assert '__REVISION__' not in page and 'general classification remains open' in page
    (site / PAGE).write_text(page)
    additions = {}
    for name in ['index.html', 'ch-differential-equations.html']:
        original = before[name].decode()
        assert MARKER not in original and '</article>' in original
        addition = MARKER + '<section class="fm-reader-link"><h2>Fuchs–Painlevé</h2><p>Algebraic differential equations on the computable-analysis foundation: checked Euler–Fuchs coefficients and Painlevé II algebraic seeds.</p><p><a href="fuchs-painleve.html">Read the subproject and formalization comparisons →</a></p></section>' + MARKER
        updated = original.replace('</article>', addition + '</article>', 1)
        assert updated.replace(addition, '', 1) == original
        (site / name).write_text(updated)
        additions[name] = addition
    for name, data in before.items():
        actual = (site / name).read_bytes()
        if name in additions:
            actual = actual.decode().replace(additions[name], '', 1).encode()
        assert actual == data, name
    (site / 'reading/algebraic-ode-axioms.log').write_text(log)
    report = {'proofSourceCommit': revision, 'page': PAGE,
              'pageSha256': sha((site / PAGE).read_bytes()),
              'auditSha256': sha(log.encode()), 'auditedDeclarations': EXPECTED,
              'allPreviousContentPreserved': True,
              'changedReaderPages': list(additions),
              'previousFileHashes': {name: sha(data) for name, data in before.items()},
              'generalClassificationProved': False, 'mathlibDependency': False}
    (site / 'reading/algebraic-ode-edition.json').write_text(json.dumps(report, indent=2) + '\n')
    print('PASS: checked Fuchs–Painlevé supplement; every prior reader byte preserved')

if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--site', type=Path, required=True)
    ap.add_argument('--revision', required=True)
    ap.add_argument('--audit', type=Path, required=True)
    args = ap.parse_args()
    install(args.site, args.revision, args.audit)
