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
            'Tests.negativePole_represented',
            'Fuchs.Frobenius.Equation.residual_split',
            'Fuchs.Frobenius.Equation.indicial_obstruction',
            'Fuchs.Frobenius.Equation.coeff_isSolution',
            'Fuchs.Frobenius.Equation.solution_unique',
            'Fuchs.Frobenius.Equation.resonance_compatibility',
            'Fuchs.Frobenius.Equation.truncation_residual',
            'Fuchs.Laguerre.polynomial_exact_degree',
            'Fuchs.Laguerre.differential_equation',
            'Fuchs.Laguerre.firstDerivativeCertificate',
            'Fuchs.Laguerre.secondDerivativeCertificate',
            'Fuchs.Laguerre.algebraic_relation',
            'Tests.resonant_no_nonzero_leading',
            'Fuchs.Frobenius.Equation.indicial_lower_bound',
            'Fuchs.Frobenius.Equation.coeff_growth',
            'Fuchs.Frobenius.Equation.factorRaw_valid',
            'Fuchs.Frobenius.Equation.factorRaw_precision',
            'Fuchs.Frobenius.Equation.factorRaw_contains_prefix',
            'Tests.besselZero_factor_valid',
            'Tests.signedSeries_factor_valid']
EXPECTED = ['ComputableAnalysis.AlgebraicODE.' + n for n in EXPECTED] + [
    'ComputableAnalysis.FormalPowerSeries.geometricRaw_valid',
    'ComputableAnalysis.FormalPowerSeries.geometricRaw_contains_prefix',
    'ComputableAnalysis.FormalPowerSeries.geometricRaw_equiv',
]

EXPECTED += [
    'ComputableAnalysis.LinearODE.normBound_exact',
    'ComputableAnalysis.LinearODE.normBound_from_initial_boxes',
    'ComputableAnalysis.LinearODE.weighted_step_factor',
    'ComputableAnalysis.LinearODE.LinearSolution.fuchs_growth',
    'ComputableAnalysis.LinearODE.LinearSolution.moderate_growth',
    'ComputableAnalysis.LinearODE.LinearSolution.constant',
    'ComputableAnalysis.AlgebraicODE.Fuchs.Growth.companion_apply',
    'ComputableAnalysis.AlgebraicODE.Fuchs.Growth.rayMatrix_pole_bound',
    'ComputableAnalysis.AlgebraicODE.Fuchs.Growth.fuchs_ray_growth',
    'ComputableAnalysis.AlgebraicODE.Fuchs.Growth.fuchs_ray_moderate',
    'ComputableAnalysis.AlgebraicODE.Fuchs.Growth.reciprocalSolution',
    'ComputableAnalysis.AlgebraicODE.Fuchs.Growth.reciprocal_moderate',
    'ComputableAnalysis.AlgebraicODE.Tests.besselConstant_growth',
]

EXPECTED += [
    'ComputableAnalysis.FormalPowerSeries.geometricRaw_hasBoxDerivative',
    'ComputableAnalysis.FormalPowerSeries.cauchy_prefix_error',
    'ComputableAnalysis.AlgebraicODE.Painleve.Laurent.leading_coefficient',
    'ComputableAnalysis.AlgebraicODE.Painleve.Laurent.resonance_obstruction',
    'ComputableAnalysis.AlgebraicODE.Painleve.Laurent.coeff_isSolution',
    'ComputableAnalysis.AlgebraicODE.Painleve.Laurent.solution_unique',
    'ComputableAnalysis.AlgebraicODE.Painleve.Laurent.coeff_growth',
    'ComputableAnalysis.AlgebraicODE.Painleve.Laurent.factorRaw_valid',
    'ComputableAnalysis.AlgebraicODE.Painleve.Pole.factor_valid',
    'ComputableAnalysis.AlgebraicODE.Painleve.Pole.firstDerivative_valid',
    'ComputableAnalysis.AlgebraicODE.Painleve.Pole.secondDerivative_valid',
    'ComputableAnalysis.AlgebraicODE.Painleve.Pole.factor_derivative',
    'ComputableAnalysis.AlgebraicODE.Painleve.Pole.factor_secondDerivative',
    'ComputableAnalysis.AlgebraicODE.Painleve.Pole.equation_error',
    'ComputableAnalysis.AlgebraicODE.Painleve.Pole.equation',
    'ComputableAnalysis.AlgebraicODE.Painleve.Pole.value_valid',
    'ComputableAnalysis.AlgebraicODE.Painleve.Pole.double_pole_bounds',
    'ComputableAnalysis.AlgebraicODE.Painleve.Pole.original_equation_identity',
    'ComputableAnalysis.AlgebraicODE.Tests.quadratic_forcing_obstruction',
    'ComputableAnalysis.AlgebraicODE.Tests.painleve_box_equation',
]

EXPECTED += [
    'ComputableAnalysis.Apery.number_integral',
    'ComputableAnalysis.Apery.term_telescopes',
    'ComputableAnalysis.Apery.number_recurrence',
    'ComputableAnalysis.Apery.number_growth',
    'ComputableAnalysis.Apery.number_equation',
    'ComputableAnalysis.Apery.coefficients_equation',
    'ComputableAnalysis.Apery.operator_ordinary',
    'ComputableAnalysis.Apery.value_valid',
    'ComputableAnalysis.Apery.value_derivative',
    'ComputableAnalysis.Apery.equation_error',
    'ComputableAnalysis.Apery.equation',
    'ComputableAnalysis.Apery.companion_recurrence',
    'ComputableAnalysis.Apery.companion_equation',
    'ComputableAnalysis.Apery.casoratian',
    'ComputableAnalysis.Apery.number_ge_one',
    'ComputableAnalysis.Apery.approximant_difference',
    'ComputableAnalysis.Apery.approximant_increasing',
]

def sha(data):
    return hashlib.sha256(data).hexdigest()

def install(site, revision, audit):
    assert re.fullmatch(r'[0-9a-f]{40}', revision)
    log = audit.read_text()
    assert 'error:' not in log and 'sorryAx' not in log
    for name in EXPECTED:
        assert "'" + name + "' depends on axioms:" in log, name
    before = {str(p.relative_to(site)): p.read_bytes() for p in site.rglob('*') if p.is_file()}
    assert PAGE not in before
    page = (ROOT / 'book/algebraic-ode/index.html').read_text().replace('__REVISION__', revision)
    assert '__REVISION__' not in page and 'general classification remains open' in page
    (site / PAGE).write_text(page)
    additions = {}
    for name in ['index.html', 'ch-differential-equations.html']:
        original = before[name].decode()
        assert MARKER not in original and '</article>' in original
        addition = MARKER + '<section class="fm-reader-link"><h2>Fuchs–Painlevé</h2><p>Algebraic differential equations on the computable-analysis foundation: forward Fuchs growth bounds, formal Frobenius recurrences, convergent factor computations, certified Laguerre polynomials, Painlevé I local pole charts with certified derivatives, Painlevé II algebraic seeds, and Apéry’s zeta(3) differential equation and arithmetic approximants.</p><p><a href="fuchs-painleve.html">Read the subproject and formalization comparisons →</a></p></section>' + MARKER
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
