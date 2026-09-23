#!/usr/bin/env python3
"""Publish the audited finite integration milestone without replacing the book."""
import argparse
import hashlib
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
PAGE = 'rational-primitives.html'
MARKER = '<!-- rational-primitives -->'
EXPECTED = [
    'RationalExpressionNormalization.compile_correct',
    'RationalPrimitiveFormula.quadraticPrimitive_correct',
    'RationalPrimitiveFormula.NormalForm.primitive_correct',
    'RationalPrimitiveFormula.Decomposition.primitive_correct',
    'RationalPrimitiveFormula.Decomposition.primitive_regular',
    'TrigonometricRationalization.Expr.pullback_correct',
    'TrigonometricRationalization.Expr.pullback_defined_iff',
    'TrigonometricRationalization.rational_circle_chart_cover',
    'TrigonometricRationalization.Expr.antipodal_pullback_correct',
    'RationalPrimitiveExamples.twoPoles_primitive',
    'RationalPrimitiveExamples.repeatedQuadratic_derivative',
    'RationalPrimitiveExamples.doubleInverse_undefined',
    'RationalPrimitiveExamples.zeroTimesPole_undefined',
    'RationalPrimitiveExamples.onePlusCosine_pullback',
    'RationalPrimitiveExamples.cosecant_pullback_pole',
    'RationalPrimitiveExamples.zeroDenominator_pullback',
]


def sha(data):
    return hashlib.sha256(data).hexdigest()


def install(site, revision, audit):
    assert re.fullmatch(r'[0-9a-f]{40}', revision)
    log = audit.read_text()
    assert 'error:' not in log and 'sorryAx' not in log
    assert 'PASS: rational primitive algebra;' in log
    assert 'general decomposition and analytic realization remain open' in log
    for name in EXPECTED:
        assert 'CHECKED ComputableAnalysis.' + name + '\n' in log, name
    before = {str(p.relative_to(site)): p.read_bytes() for p in site.rglob('*') if p.is_file()}
    assert PAGE not in before
    page = (ROOT / 'book/rational-primitives/index.html').read_text().replace('__REVISION__', revision)
    assert '__REVISION__' not in page
    assert 'The general analytic theorem remains open.' in page
    assert 'MathJax' in page and '<sup>' not in page and '<sub>' not in page
    (site / PAGE).write_text(page)
    additions = {}
    for name in ['index.html', 'ch-integrals.html']:
        original = before[name].decode()
        assert MARKER not in original and '</article>' in original
        addition = (MARKER + '<section class="fm-reader-link"><h2>Elementary primitives</h2>'
                    '<p>Checked finite partial-fraction integration and rational circle substitution; '
                    'the general analytic theorem remains open.</p>'
                    '<p><a href="rational-primitives.html">Read the proofs and remaining obligations</a>'
                    '</p></section>' + MARKER)
        (site / name).write_text(original.replace('</article>', addition + '</article>', 1))
        additions[name] = addition
    for name, original in before.items():
        actual = (site / name).read_bytes()
        if name in additions:
            actual = actual.decode().replace(additions[name], '', 1).encode()
        assert actual == original, name
    (site / 'reading/rational-primitives-audit.log').write_text(log)
    report = {'proofSourceCommit': revision, 'page': PAGE,
              'pageSha256': sha((site / PAGE).read_bytes()), 'auditSha256': sha(log.encode()),
              'auditedDeclarations': EXPECTED, 'allPreviousContentPreserved': True,
              'generalAnalyticTheoremProved': False, 'formalPartialFractionIntegrationProved': True,
              'domainPreservingRationalizationProved': True, 'mathlibDependency': False,
              'changedReaderPages': list(additions)}
    (site / 'reading/rational-primitives-edition.json').write_text(json.dumps(report, indent=2) + '\n')
    print('PASS: rational primitive supplement; every prior reader byte preserved')


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--site', type=Path, required=True)
    parser.add_argument('--revision', required=True)
    parser.add_argument('--audit', type=Path, required=True)
    args = parser.parse_args()
    install(args.site, args.revision, args.audit)
