#!/usr/bin/env python3
"""Publish the checked real-domain zeta supplement, preserving prior content."""
import argparse
import hashlib
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
PAGE = 'zeta-real.html'
MARKER = '<!-- zeta-real -->'
EXPECTED = ['ComputableAnalysis.ZetaReal.coefficient_step', 'ComputableAnalysis.ZetaReal.magnitude_decay', 'ComputableAnalysis.ZetaReal.moment_bound', 'ComputableAnalysis.ZetaReal.rectangle_outer_tail', 'ComputableAnalysis.ZetaReal.rectangle_inner_tail', 'ComputableAnalysis.ZetaReal.outerBudget_dyadic_shrinks', 'ComputableAnalysis.ZetaReal.approx_cauchy', 'ComputableAnalysis.ZetaReal.raw_valid', 'ComputableAnalysis.ZetaReal.continuous', 'ComputableAnalysis.ZetaReal.domainReal_inChart', 'ComputableAnalysis.ZetaReal.zeta_valid', 'ComputableAnalysis.ZetaReal.zeta_equiv', 'ComputableAnalysis.ZetaReal.raw_chart_equiv', 'ComputableAnalysis.ZetaReal.binomial_equation', 'ComputableAnalysis.ZetaReal.binomial_unique', 'ComputableAnalysis.ZetaReal.rectangle_dirichlet', 'ComputableAnalysis.ZetaReal.dirichletRaw_valid', 'ComputableAnalysis.ZetaReal.inversePowerRaw_valid', 'ComputableAnalysis.ZetaReal.inversePowerRaw_enclosure', 'ComputableAnalysis.ZetaReal.dirichlet_convergence', 'ComputableAnalysis.ZetaReal.zeta_integer_equiv', 'ComputableAnalysis.ZetaReal.zeta_three_equiv', 'ComputableAnalysis.ZetaReal.Tests.threeHalves_coefficient', 'ComputableAnalysis.ZetaReal.Tests.threeHalves_rectangle', 'ComputableAnalysis.ZetaReal.Tests.delayedThree_same_zeta']

EXPECTED += ['ComputableAnalysis.Basel.leibniz_square_error', 'ComputableAnalysis.Basel.zeta_leibniz_square_budget', 'ComputableAnalysis.Basel.eulerBasel', 'ComputableAnalysis.Basel.EulerSieve.sieve_cons', 'ComputableAnalysis.Basel.EulerSieve.sieve_error', 'ComputableAnalysis.Basel.zetaTwo_equiv_finiteEulerProduct', 'ComputableAnalysis.Basel.prime_unbounded_of_piSquare_irrational', 'ComputableAnalysis.Basel.real_zeta_two_equiv_piSquaredOverSix']

def sha(data):
    return hashlib.sha256(data).hexdigest()

def install(site, revision, audit):
    assert re.fullmatch(r'[0-9a-f]{40}', revision)
    log = audit.read_text()
    assert 'error:' not in log and 'sorryAx' not in log
    for name in EXPECTED:
        assert "'" + name + "' depends on axioms:" in log, name
    assert not re.search(r'ComputableAnalysis\.ZetaReal\.[^\s,\]]*\.ax_', log)
    before = {str(p.relative_to(site)): p.read_bytes() for p in site.rglob('*') if p.is_file()}
    assert PAGE not in before
    page = (ROOT / 'book/zeta-real/index.html').read_text().replace('__REVISION__', revision)
    assert '__REVISION__' not in page and 'analytic continuation remain open' in page
    (site / PAGE).write_text(page)
    additions = {}
    for name in ['index.html', 'ch-transforms-zeta.html']:
        original = before[name].decode()
        assert MARKER not in original and '</article>' in original
        addition = MARKER + r'<section class="fm-reader-link"><h2>Zeta for real exponents</h2><p>A checked interval computation on the whole real half-line \(s&gt;1\): finite Dirichlet sums, uniform tail estimates, adaptive real inputs, and agreement with every earlier integer zeta value.</p><p><a href="zeta-real.html">Read the construction and checked boundary →</a></p></section>' + MARKER
        updated = original.replace('</article>', addition + '</article>', 1)
        assert updated.replace(addition, '', 1) == original
        (site / name).write_text(updated)
        additions[name] = addition
    for name, data in before.items():
        actual = (site / name).read_bytes()
        if name in additions:
            actual = actual.decode().replace(additions[name], '', 1).encode()
        assert actual == data, name
    (site / 'reading/zeta-real-axioms.log').write_text(log)
    report = {'proofSourceCommit': revision, 'page': PAGE,
              'pageSha256': sha((site / PAGE).read_bytes()),
              'auditSha256': sha(log.encode()), 'auditedDeclarations': EXPECTED,
              'allPreviousContentPreserved': True,
              'changedReaderPages': list(additions),
              'previousFileHashes': {name: sha(data) for name, data in before.items()},
              'baselProved': True, 'primesFromPiSquaredIrrationality': True, 'piSquaredIrrationalityIntegrated': False, 'piSquaredIrrationalityPublished': True, 'realInputsAboveOne': True, 'logExpBridgeProved': False, 'analyticContinuationProved': False, 'mathlibDependency': False}
    (site / 'reading/zeta-real-edition.json').write_text(json.dumps(report, indent=2) + '\n')
    print('PASS: checked real-domain zeta supplement; every prior reader byte preserved')

if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--site', type=Path, required=True)
    ap.add_argument('--revision', required=True)
    ap.add_argument('--audit', type=Path, required=True)
    args = ap.parse_args()
    install(args.site, args.revision, args.audit)
