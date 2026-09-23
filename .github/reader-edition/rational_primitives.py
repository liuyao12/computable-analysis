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
    'ComputableTrigonometricRationalization.Factorization.asRepresented',
    'ComputableTrigonometricRationalization.Expr.pullback_angle_correct',
    'ComputableTrigonometricRationalization.RepresentedFactorization.primitive_correct',

    'ComputableTrigonometricRationalization.Expr.shadow_compile',
    'ComputableTrigonometricRationalization.Expr.pullback_correct',
    'ComputableTrigonometricRationalization.Expr.pullback_defined_iff',
    'ComputableTrigonometricRationalization.Expr.antipodal_pullback_correct',
    'ComputableTrigonometricRationalization.jacobian_cancel',
    'ComputableTrigonometricRationalization.halfAngle_derivative',
    'ComputableTrigonometricRationalization.Factorization.primitive_sample_correct',
    'ComputableTrigonometricRationalization.Factorization.primitive_correct',
    'PrimitiveChangeOfVariables.rationalCompositionSecant_error_le',
    'PrimitiveChangeOfVariables.FiniteCompositionDerivativeOnInterval.toHasDerivativeOnInterval',
    'PrimitiveChangeOfVariables.FiniteSecantCompositionDerivativeOnInterval.toHasDerivativeOnInterval',
    'TrigonometricPrimitiveExamples.factors_checked',
    'TrigonometricPrimitiveExamples.derivative_computes',
    'TrigonometricPrimitiveExamples.value_computes',
    'TrigonometricPrimitiveExamples.irrational_primitive_correct',
    'TrigonometricPrimitiveExamples.derivative_is_expected',
    'TrigonometricPrimitiveExamples.zero_times_cosecant_stays_undefined',
    'TrigonometricPrimitiveExamples.antipodal_pole_retained',
    'TrigonometricPrimitiveExamples.zero_inner_increment',

    'ComputableCoefficient.widthStage_spec',
    'PrimitiveLogarithmEstimates.prefix_lipschitz',
    'PrimitiveLogarithmEstimates.kernel_lipschitz',
    'PrimitiveLogarithmEstimates.prefix_affine_secant',
    'ComputableLogarithmChart.Coefficient.value_valid',
    'ComputableLogarithmChart.Coefficient.derivative_valid',
    'ComputableLogarithmChart.Coefficient.hasDerivative',
    'ComputableLogarithmChart.simplePole_hasDerivative',
    'ComputableLogarithmChart.simplePole_derivative_equiv',
    'ComputableLogarithmChart.arctan_hasDerivative',
    'ComputableLogarithmChart.arctan_derivative_equiv',
    'ComputableLogarithmChart.arctan_valueSample',
    'ComputableLogarithmChart.Coefficient.weightedValue_valid',
    'ComputableLogarithmChart.Coefficient.weightedDerivative_valid',
    'ComputableLogarithmChart.Coefficient.weightedHasDerivative',
    'ComputableLogarithmChart.quadraticLog_hasDerivative',
    'ComputableLogarithmChart.quadraticLog_derivative_equiv',
    'ComputableLogarithmChart.quadraticArctan_hasDerivative',
    'ComputableLogarithmChart.quadraticArctan_derivative_equiv',
    'ComputablePrimitiveDerivativeExamples.irrationalPole_hasDerivative',
    'ComputablePrimitiveDerivativeExamples.irrationalPole_derivative_is_reciprocal',
    'ComputablePrimitiveDerivativeExamples.irrationalArctan_hasDerivative',
    'ComputablePrimitiveDerivativeExamples.irrationalArctan_derivative_is_kernel',
    'ComputablePrimitiveDerivativeExamples.irrationalArctan_series',
    'ComputablePrimitiveDerivativeExamples.irrationalQuadratic_hasDerivative',
    'ComputablePrimitiveDerivativeExamples.irrationalQuadratic_derivative_is_reciprocal',

    'ComputableCoefficient.Value.equiv_of_samples',
    'ComputableCoefficient.Expr.realize',
    'ComputableCoefficient.Expr.realize_equiv',
    'ComputableFactoredAlgebra.shadow_normalForm',
    'ComputableFactoredAlgebra.Formula.sample_formalDerivative',
    'ComputableFactoredAlgebra.requirements_sufficient',
    'ComputableFactoredAlgebra.certifyFactors',
    'ComputableFactoredAlgebra.primitive_correct',
    'ComputableFactoredAlgebra.FactoredRational.primitive_correct',
    'ComputablePrimitiveExamples.factors_checked',
    'ComputablePrimitiveExamples.derivative_computes',
    'ComputablePrimitiveExamples.integrand_computes',
    'ComputablePrimitiveExamples.irrational_primitive_correct',
    'ComputablePrimitiveExamples.zero_inverse_rejected',
    'ComputablePrimitiveExamples.duplicate_irrational_pole_rejected',

    'RationalFactoredPrimitives.generalQuadratic_value',
    'RationalQuadraticDivision.divide_identity',
    'RationalQuadraticDivision.norm_pos',
    'RationalQuadraticDivision.nextNumerator_identity',
    'RationalQuadraticDivision.remove_identity',
    'RationalFactoredPrimitives.normalForm_identity',
    'RationalFactoredPrimitives.decomposition',
    'RationalFactoredPrimitives.Factorization.decomposition',
    'RationalFactoredPrimitives.Factorization.primitive_correct',
    'RationalPrimitiveExamples.mixedQuadratic_coefficients',
    'RationalPrimitiveExamples.duplicateQuadratic_rejected',
    'RationalPrimitiveExamples.factoredQuadraticExample_primitive',

    'HasDerivativeOnInterval.scale',
    'HasDerivativeOnInterval.linearCombination',
    'RationalPrimitivePowers.hasDerivative',
    'RationalPrimitivePowers.weighted_hasDerivative',
    'RationalPartialFractions.decomposition',
    'RationalPartialFractions.ofFactorization',
    'RationalPrimitiveAssembly.radius_pos',
    'RationalPrimitiveAssembly.denominator_near',
    'RationalPrimitiveAssembly.splitPrimitive',
    'RationalPrimitiveAssembly.ofFactorization',
    'RationalPrimitiveExamples.automaticMixed_coefficients',
    'RationalPrimitiveExamples.negativeTriplePole_hasDerivative',
    'RationalPrimitiveExamples.automaticMixed_hasDerivative',
    'RationalPrimitiveExamples.automaticMixed_elementary',
    'RationalPrimitiveExamples.automaticMixed_radius',

    'HasDerivativeOnInterval.add',
    'RationalPrimitiveExamples.polynomialPlusLog_hasDerivative',
    'RationalPrimitivePolynomial.hasDerivative',
    'RationalPrimitiveLogarithm.hasDerivative',
    'RationalPrimitiveLogarithm.affineHasDerivative',
    'RationalPrimitiveLogarithm.simplePole_hasDerivative',
    'RationalPrimitiveLogarithm.poleRadius_pos',
    'RationalPrimitiveExamples.negativePole_hasDerivative',
    'RationalPrimitiveExamples.polynomial_hasDerivative',
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
    assert 'factorization existence, analytic assembly for computable coefficients, and represented trigonometric transport remain open' in log
    for name in EXPECTED:
        assert 'CHECKED ComputableAnalysis.' + name + '\n' in log, name
    before = {str(p.relative_to(site)): p.read_bytes() for p in site.rglob('*') if p.is_file()}
    assert PAGE not in before
    page = (ROOT / 'book/rational-primitives/index.html').read_text().replace('__REVISION__', revision)
    assert '__REVISION__' not in page
    assert 'The full rational-function primitive theorem remains open.' in page
    assert 'MathJax' in page and '<sup>' not in page and '<sub>' not in page
    (site / PAGE).write_text(page)
    additions = {}
    for name in ['index.html', 'ch-integrals.html']:
        original = before[name].decode()
        assert MARKER not in original and '</article>' in original
        addition = (MARKER + '<section class="fm-reader-link"><h2>Elementary primitives</h2>'
                    '<p>Checked elementary primitives for rationally split denominators and circle substitution; '
                    'the full rational-function primitive theorem remains open.</p>'
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
              'domainPreservingRationalizationProved': True,
              'analyticPolynomialPrimitivesProved': True,
              'analyticSimplePoleLocalPrimitivesProved': True,
              'automaticRationalLinearPartialFractionsProved': True,
              'automaticRationalQuadraticPartialFractionsProved': True,
              'factorizationToFormalPrimitiveProved': True,
              'computableRealCoefficientFormalPrimitivesProved': True,
              'irrationalCoefficientRegressionProved': True,
              'computableLogarithmArctangentDerivativesProved': True,
              'computableQuadraticBasePrimitivesProved': True,
              'trigonometricElementaryFormulaTheoremProved': True,
              'finitePrimitiveChangeOfVariablesProved': True,
              'trigonometricIntervalPrimitiveTheoremProved': False,
              'analyticRepeatedLinearPolePrimitivesProved': True,
              'analyticRationallySplitLocalPrimitivesProved': True, 'mathlibDependency': False,
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
