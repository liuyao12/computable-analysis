"""Attach the checked sine comparison routes and declaration metadata to the proof map.
Run after `lake env lean scripts/export_sine_dependencies.lean` and the two sine audits.
"""
from pathlib import Path
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'book/modular-dependencies'
P = 'ComputableAnalysis.'
S = P + 'ElementarySineODE.'
F = P + 'ElementarySineComparison.'
R = P + 'RiemannHilbert.'
M = P + 'ModularForms.'


def node(id, title, formula, body, roots, row, col, parents, theorems=(), lane='shared'):
    return dict(id='sine-' + id, title=title, formula=formula, body=body,
                roots=roots, row=row, col=col, parents=['sine-' + p for p in parents],
                theorems=list(theorems), lane=lane, status='checked')


nodes = [
    node('foundation', 'Shared computable foundation', r'\(\mathbb Q(i)\to\text{nested rational boxes},\qquad\simeq\;=\;\mathrm{Equiv}\)',
         'Both routes use valid rational interval and complex-box computations, exact rational algebra and equality of represented values. The primary sine functions retain their rational domains. No Mathlib real or complex numbers or completed scalar field supplies the functions.',
         [P+'Basic', P+'ComplexMultiplication', P+'ComplexRawQuotient'], 0, 1, []),
    node('primary', 'Primary rational sine functions', r'\[F(r)=\sin(\pi r),\ r\in\mathbb Q;\qquad S(q)=\sum_{n\ge0}\frac{(-1)^nq^{2n+1}}{(2n+1)!},\ q\in\mathbb Q(i).\]',
         'Normalized sine computes the imaginary coordinate of the bounded exponential at the represented physical angle. Power-series sine computes stabilized odd paired exponential prefixes; checked coefficient identities identify the usual sine series. These are two actual computations in different coordinates. Irrational evaluations are add-ons.',
         [P+'ElementaryRational', P+'ElementaryPowerSeries', P+'ElementarySeriesCoefficients'], 1, 0, ['foundation'], lane='finite'),
    node('exp', 'Shared entire exponential', r'\[E(z)=\sum_{n\ge0}\frac{z^n}{n!}.\]',
         'Rational power-series calculations and quantitatively justified entire exponential evaluations are common foundations. The normalized sine implementation is already based on an exponential; the ODE test does not compare it with a newly defined geometric sine.',
         [M+'EntireExponential', M+'ExponentialDerivative', P+'ExponentialComputations.RationalAgreement'], 1, 1, ['foundation'], [M+'entireExponential_derivative_value']),
    node('pi', 'Computed geometric pi', r'\[\pi\text{ is a valid rational interval computation.}\]',
         'The normalized coordinate uses the existing geometric pi algorithm, embedded as a valid represented complex coefficient. No rationality assumption on pi appears in the global theorem. Keep the physical coordinate change explicit.',
         [P+'GeometricPiRotation', P+'ElementaryRational'], 1, 2, ['foundation']),
    node('prefix', 'Finite odd-prefix identities', r'\[S_N(q)=\frac{E_N(iq)-E_N(-iq)}{2i}.\]',
         'Finite rational identities pair the odd exponential terms; on the rational real axis conjugate prefixes recover the rotation coordinate. This supplies a shared finite point in the relevant output enclosures. Agreement is algebraic, not a numerical test at chosen points.',
         [P+'ElementarySeriesCoefficients', P+'ElementarySeriesComparisons', M+'ExponentialConjugatePrefixes'], 2, 0, ['primary', 'exp'], [P+'ElementaryPowerSeries.imaginaryPrefix_pair', P+'ElementaryPowerSeries.sineValue_realAxis_agrees', P+'ElementaryPowerSeries.sineValue_agrees'], 'finite'),
    node('scalar', 'Paired scalar exponential solution', r'\[s_a(z)=\frac{E(iaz)-E(-iaz)}{2i},\qquad c_a(z)=\frac{E(iaz)+E(-iaz)}2.\]',
         'Composition with affine maps, sums, negation and products constructs actual entire holomorphic witnesses for this pair. The derivative of the entire exponential and the chain rule give the two solution equations.',
         [P+'ElementarySineODESolutions', M+'ExponentialDerivative', R+'DomainHolomorphicComposition', R+'DomainHolomorphicSums'], 2, 1, ['exp'], [S+'sine_derivative', S+'cosine_derivative'], 'ode'),
    node('matrix', 'Rotation-matrix Taylor solution', r'\[A_a=\begin{pmatrix}0&a\\-a&0\end{pmatrix},\quad u_a(z)=\exp(zA_a)\binom{0}{1}.\]',
         'A separate executable matrix Taylor computation uses coefficients determined recursively by the rotation generator. The existing matrix-series holomorphicity and termwise derivative proof supply its actual differential equation. Its value at zero is checked from the initial Taylor coefficient.',
         [P+'ElementarySineODESolutions', R+'EntireMatrixExponential', R+'EntireExponentialODE', R+'ExponentialCoefficients'], 2, 2, ['foundation'], [S+'seriesVector_ode', S+'seriesVector_initial'], 'ode'),
    node('tails', 'Shrinking tails and output enclosures', r'\[\|v-v_N\|\le\varepsilon_N,\qquad\varepsilon_N\longrightarrow0.\]',
         'Explicit power-series tails, nested-box validity and stabilization justify the passage from shared finite prefixes to exact value agreement. This route does not require the oscillator ODE or its uniqueness theorem.',
         [P+'ElementarySeriesComparisons', P+'ElementaryPowerSeries', M+'ExponentialLegacyTail'], 3, 0, ['prefix'], [P+'ElementaryPowerSeries.sineValue_realAxis_agrees'], 'finite'),
    node('laws', 'Solution laws and initial values', r"\[s_a'=ac_a,\qquad c_a'=-as_a,\qquad(s_a(0),c_a(0))=(0,1).\]",
         'Both supplied calculations have proved holomorphicity, both differential equations and the same initial pair, for every valid represented complex frequency. Initial equality alone is insufficient; these are actual solution proofs rather than equality fields in a certificate.',
         [P+'ElementarySineODESolutions', R+'EntireExponentialODE'], 3, 1, ['scalar', 'matrix'], [S+'exponentialVector_ode', S+'seriesVector_ode', S+'exponentialVector_initial', S+'seriesVector_initial'], 'ode'),
    node('local', 'Checked local ODE uniqueness', r"\[u'=A_au,\ v'=A_av,\ u(p)\simeq v(p)\;\Longrightarrow\;u\simeq v\text{ near }p.\]",
         'Actual holomorphic derivative and solution evidence gives agreement on a constructed positive neighborhood. This is the checked local comparison used beneath zero-derivative constancy, not the older conditional scalar uniqueness provider.',
         [R+'ContourSystemUniqueness', R+'HolomorphicPathConstancy'], 3, 2, ['foundation'], [R+'ConstructedSystemODE.solution_unique_local'], 'ode'),
    node('lift', 'Quantitative exponential extension bridge', r'\[E(z)\simeq\lim_N E_N(q_N),\qquad q_N\in\mathbb Q(i),\quad q_N\to z.\]',
         'Rational box centers, input-motion bounds, truncation tails and output widths identify the older bounded exponential computation with the latest entire evaluator on every valid represented input. This shared construction bridge permits the finite route to evaluate the irrational angle pi times a rational parameter.',
         [M+'ExponentialLiftAgreement', M+'ExponentialCenterApproximation', P+'ExponentialComputations.RationalAgreement'], 4, 0, ['tails', 'exp'], [M+'entireExponential_legacy_lift'], 'finite'),
    node('inverse', 'Inverse exponential removes the ODE', r"\[v(z)=\exp(-zA_a)u(z),\qquad v'(z)\simeq0.\]",
         'The actual invertible exponential frame acts on each supplied solution. Product and inverse-frame derivative laws prove zero derivative; reflecting through the invertible frame recovers equality of the original solutions. No sine-agreement theorem is used in this reduction.',
         [R+'ExponentialFrameHolomorphic', R+'EntireConstantODEUniqueness'], 4, 1, ['laws', 'exp'], [R+'MatrixExponential.constant_ode_path_unique'], 'ode'),
    node('coverage', 'Finite coverage of the affine path', r'\[\gamma(t)=(1-t)p+tz,\qquad0\le t\le1.\]',
         'Local uniqueness gives constancy neighborhoods for a zero-derivative field. Relative-open neighborhoods and a constructed finite rational bisection cover propagate equality across the entire parameter interval. Entire-domain membership covers every affine-path point, with no small-endpoint restriction or caller-supplied cover.',
         [R+'HolomorphicPathConstancy', R+'UnitIntervalLocalEquality', R+'ScalarPaths', R+'UnitIntervalOpenCover'], 4, 2, ['local'], [R+'DomainVectorFunctions.zero_derivative_path_constant'], 'ode'),
    node('finite-result', 'Finite-prefix comparison result', r'\[F(r)\simeq\operatorname{sineAtAngle}(\pi r),\quad r\in\mathbb Q;\qquad S(x)\simeq\operatorname{sineAtAngle}(x),\ x\in\mathbb Q.\]',
         'The checked finite route connects the primary normalized function and rational real radian function to the existing derived angle evaluation. It compares the two primary functions wherever their physical coordinates agree. This endpoint has that explicit overlap premise; it is not the separately proved entire complex extension theorem. Finite algebra and shrinking errors are the shorter route for these existing exponential-based implementations.',
         [P+'ElementarySineComparison'], 5, 0, ['lift', 'pi'], [F+'powerSeries_rational_agrees_derived', F+'sinPi_agrees_derived_powerSeries', F+'sinPi_powerSeries_agrees_at_coordinates'], 'finite'),
    node('uniqueness', 'Global constant-ODE uniqueness', r"\[u'=A_au,\ v'=A_av,\ u(0)\simeq v(0)\;\Longrightarrow\;u(z)\simeq v(z).\]",
         'Inverse-frame reduction and checked path constancy produce a reusable whole-plane uniqueness law. The theorem internally constructs an affine path to every valid represented complex endpoint. Domain coverage and solution evidence are genuine hypotheses; the desired agreement is a conclusion.',
         [R+'EntireConstantODEUniqueness'], 5, 1, ['inverse', 'coverage'], [R+'MatrixExponential.constant_ode_entire_unique', R+'MatrixExponential.constant_ode_path_unique'], 'ode'),
    node('ode-core', 'Global ODE comparison core', r'\[\binom{s_a(z)}{c_a(z)}\simeq u_a(z),\qquad a,z\text{ arbitrary valid represented complex values}.\]',
         'This theorem applies global uniqueness to the two constructed solutions and their proved initial values. Its extracted transitive proof closure contains both solution laws, initial values and checked path constancy, and contains no earlier elementary sine-agreement theorem. It shares the exponential foundation, but the comparison step uses ODE uniqueness.',
         [P+'ElementarySineODESolutions'], 6, 1, ['laws', 'uniqueness'], [S+'computations_agree_global'], 'ode'),
    node('coordinates', 'Frequency scaling and pi coordinate', r'\[u_a(z)\simeq u_1(az),\qquad a=\pi.\]',
         'Finite operator powers and shrinking matrix-series errors prove the actual parameter scaling. Substituting computed pi aligns the normalized and radian coordinates. This coordinate step uses coefficient algebra; an ODE comparison still needs its justified coordinate pullback.',
         [P+'ElementarySineODESolutions', R+'ExponentialScalarParameters', R+'ExponentialParameterScaling'], 6, 2, ['matrix', 'pi'], [S+'seriesVector_reparametrization'], 'ode'),
    node('bridges', 'Primary-function adapters', r'\[S(q)\simeq\widehat S(q),\ q\in\mathbb Q(i);\qquad F(r)\simeq\widehat F(r),\ r\in\mathbb Q.\]',
         'Separate adapters identify the actual primary computations with the derived entire values. The power-series adapter uses the finite odd-prefix identity to identify its scalar exponential formula, then the global ODE theorem to identify the matrix Taylor calculation. The normalized adapter uses the finite route’s checked normalized-angle bridge and conjugation. Thus the applied ODE route honestly reuses finite algebra at this primary-construction boundary.',
         [P+'ElementarySineODEComparison', P+'ElementarySineComparison', M+'ExponentialConjugation'], 7, 0, ['prefix', 'lift', 'finite-result', 'ode-core'], [S+'powerSeries_primary_agrees', S+'sinPi_primary_agrees']),
    node('entire-result', 'Entire normalized–radian identity', r'\[\widehat F(z)\simeq\widehat S(\pi z).\]',
         'For every valid represented complex input, global ODE agreement and the justified frequency scaling yield the exact entire complex comparison. The derived power-series value is the rotation-matrix Taylor computation; the derived normalized value is the paired scalar exponential at frequency pi. Primary adapters and convergence explain their connection with the rational-input objects, separately from this core identity.',
         [P+'ElementarySineODEComparison', P+'ElementarySineODESolutions'], 7, 1, ['ode-core', 'coordinates'], [S+'sinPi_powerSeries_global'], 'ode'),
    node('convergence', 'Irrational evaluation from rational inputs', r'\[S(q_n)\to\widehat S(z),\quad q_n=\operatorname{center}(z_n);\qquad F(r_n)\to\widehat F(x),\quad r_n=\operatorname{midpoint}(x_n).\]',
         'For every positive rational error the actual holomorphic continuity modulus and shrinking input-box widths give eventual closeness of primary rational values to the derived evaluation. All represented complex inputs are covered for power-series sine and all represented real inputs for normalized primary sine. Representation invariance is proved for the derived maps.',
         [P+'ElementarySineODEComparison', M+'RationalCenterApproximation', R+'DomainHolomorphicComposition'], 8, 2, ['bridges', 'scalar', 'matrix'], [S+'powerSeries_primary_converges', S+'sinPi_primary_converges']),
    node('applied', 'Primary comparison through the ODE route', r'\[F(r)\simeq\widehat S(\pi r),\qquad r\in\mathbb Q.\]',
         'The normalized primary-function adapter and the entire identity give the requested comparison at its physical angle, even when that angle is irrational. The extracted proof closure really includes the global ODE comparison. This applied theorem and the finite-prefix endpoint express compatible comparisons; their exact formal statements and domains are shown separately.',
         [P+'ElementarySineODEComparison'], 8, 0, ['bridges', 'entire-result'], [S+'sinPi_primary_ode_comparison']),
]


G = P + 'GeometricCircleODEComparison.'
C = P + 'GeometricCircleRational.'
nodes.extend([
    node('circle-primary', 'Primary geometric circle on rational slopes', r'\[P(t)=\left(\frac{1-t^2}{1+t^2},\frac{2t}{1+t^2}\right),\quad t\in\mathbb Q.\]',
         'The circle sine and cosine are literal rational coordinates of the stereographic point. Their executable definitions and geometric angle algorithm have no exponential or power-series dependency. This is the independent geometric construction used in the new test.',
         [P+'GeometricCircleRational', P+'RationalCircle'], 9, 0, ['foundation'], [C+'sine_valid', C+'cosine_valid'], 'geometric'),
    node('circle-clock', 'Sector-area coordinate add-on', r'\[\theta(t)=2\operatorname{atan}_{\mathrm{geom}}(t),\quad0\le t\le1.\]',
         'Polygonal sector-area enclosures compute the angle. Finite rectangle sums for the geometric angular speed converge to this same angle. An irrational angle is a derived coordinate of the rational circle object, not a new primary domain.',
         [P+'GeometricCircleRational', P+'ArctanGeometry', P+'ElementaryCircleAngle'], 10, 0, ['circle-primary'], [P+'ElementaryCircleAngle.angle_target_error', C+'angle_valid'], 'geometric'),
    node('circle-ode-law', 'Actual variable-speed rotation law', r"\[P'(t)=\frac{2i}{1+t^2}P(t),\qquad P(0)=1.\]",
         'Exact rational differentiation proves the geometric circle ODE. Quantitative rational difference-quotient residuals and Euler stability supply its solution evidence. This equation is in stereographic slope; treating slope as a radian angle would compare different functions.',
         [P+'GeometricRotationODE', M+'GeometricRotationEulerStability'], 10, 1, ['circle-primary'], [P+'GeometricRotationODE.point_hasComplexDerivativeOnUnit', P+'GeometricRotationODE.pointComplexDerivative_eq_angularVelocity_mul_point'], 'geometric'),
    node('circle-euler', 'Same finite Euler mesh, two error proofs', r'\[p_{k+1}=p_k+h\frac{2i}{1+(kh)^2}p_k,\quad p_0=1.\]',
         'The geometry proof bounds rational circle coordinates against this actual finite mesh. The analytic proof uses exponential local remainders, finite products and converging angular sums to bound its pulled-back rotation against the same mesh. Neither error record assumes agreement of the final values.',
         [P+'GeometricCircleODEComparison', P+'ElementaryCircleAngle', M+'GeometricRotationEulerMesh', M+'GeometricRotationEulerConvergence'], 11, 1, ['circle-ode-law', 'circle-clock', 'exp'], [G+'geometricSolutionEvidence', G+'analyticSolutionEvidence'], 'geometric'),
    node('circle-unique', 'Common-Euler limit uniqueness', r'\[\|u-p_N\|\le C_u\varepsilon_N,\quad\|v-p_N\|\le C_v\varepsilon_N,\quad\varepsilon_N\to0\;\Longrightarrow\;u\simeq v.\]',
         'Triangle inequalities and shrinking rational error bounds prove exact equality. The ODE application constructs both bounds from the actual residual and stability laws. This is a quantitative uniqueness test for these supplied computations, not an unproved general variable-coefficient ODE existence or uniqueness provider.',
         [R+'CommonEulerLimit', P+'GeometricCircleODEComparison'], 12, 1, ['circle-euler'], [R+'CommonEulerLimit.unique', G+'geometric_rotation_ode_unique'], 'geometric'),
    node('circle-coverage', 'Sign and reciprocal charts cover all slopes', r'\[\theta(t)=\pi-\theta(1/t)\ (t>1),\qquad\theta(-t)=-\theta(t).\]',
         'Here pi is four times the geometrically computed angle at slope one. Exact rational point reflection and reciprocal identities, with finite exponential addition and conjugation laws, extend the comparison to every rational slope. The angle algorithm remains geometric.',
         [P+'GeometricCircleRational', P+'GeometricCircleODEComparison'], 13, 1, ['circle-unique', 'circle-clock'], [C+'point_neg', C+'point_reciprocal', G+'geometric_rotation_all_rational'], 'geometric'),
    node('circle-result', 'Independent geometric–series sine identity', r'\[\frac{2t}{1+t^2}\simeq\widehat S(\theta(t)),\qquad t\in\mathbb Q.\]',
         'Common-Euler uniqueness identifies the geometric rotation with an analytic intermediate solution. Whole-plane oscillator uniqueness then identifies its sine coordinate with the matrix Taylor solution, already linked to the primary rational-complex sine series. The audit excludes the previous geometric/exponential endpoint identity. Exponential participates in the proof; it does not define the geometric primary object.',
         [P+'GeometricCircleODEComparison', P+'ElementarySineODESolutions', P+'ElementarySineODEComparison'], 14, 1, ['circle-coverage', 'ode-core'], [G+'geometric_sine_powerSeries'], 'geometric'),
    node('circle-series-bridge', 'Primary series adapter for the geometric test', r'\[S(q)\simeq\widehat S(q),\quad q\in\mathbb Q(i).\]',
         'Finite odd coefficient identities connect the actual primary sine series to the matrix Taylor extension. Its proved holomorphic modulus and shrinking input centers justify irrational angle evaluation. This adapter is needed for the primary convergence and overlap conclusions, separately from the geometric-to-matrix exact identity.',
         [P+'ElementarySineODEComparison', P+'ElementaryPowerSeries', P+'GeometricCircleODEComparison'], 15, 0, ['prefix', 'ode-core', 'matrix'], [S+'powerSeries_primary_agrees', S+'powerSeries_primary_converges', G+'primary_agreement_on_overlap'], 'geometric'),
    node('circle-convergence', 'Primary power-series values approach circle sine', r'\[S(q_n)\to\frac{2t}{1+t^2},\quad q_n=\operatorname{center}(\theta(t)_n)\in\mathbb Q(i).\]',
         'For every positive rational tolerance the existing holomorphic modulus supplies eventual closeness of the actual primary series values at rational box centers. Thus the derived irrational-angle evaluation is justified by primary computations. Exact primary-to-primary comparison retains a coordinate-overlap premise.',
         [P+'GeometricCircleODEComparison', P+'ElementarySineODEComparison'], 16, 1, ['circle-result', 'circle-series-bridge'], [G+'geometric_sine_primary_converges'], 'geometric'),
])


def update():
    graph = json.loads((OUT / 'modular-dependencies.json').read_text())
    deps = json.loads((OUT / 'sine-proof-dependencies.json').read_text())
    modules = {'.'.join(p.relative_to(ROOT).with_suffix('').parts): p for p in (ROOT / 'ComputableAnalysis').rglob('*.lean')}
    for name, entry in deps['declarations'].items():
        assert entry['module'] in modules, (name,entry['module'])
    highlighted = set(r for n in nodes for r in n['roots'])
    report=(ROOT/'skills/function-computation-identity/references/sine-comparison.md').read_text()
    highlighted.update(P + name[:-5].replace('/', '.') for name in re.findall(r'\]\(\.\./\.\./\.\./ComputableAnalysis/([^)]*\.lean)\)', report))
    for name in highlighted:
        path = modules[name]
        text = path.read_text()
        graph['sources'][name] = dict(text=text, sha256=hashlib.sha256(text.encode()).hexdigest())
    todo = list(highlighted)
    seen = set()
    while todo:
        name = todo.pop()
        if name in seen:
            continue
        seen.add(name)
        text = modules[name].read_text()
        imports = re.findall(r'^import\s+(ComputableAnalysis(?:\.[A-Za-z0-9_]+)+)', text, flags=re.M)
        graph['imports'][name] = imports
        todo.extend(imports)
    for entry in deps['declarations'].values():
        name = entry['module']
        if name not in graph['imports']:
            graph['imports'][name] = re.findall(r'^import\s+(ComputableAnalysis(?:\.[A-Za-z0-9_]+)+)', modules[name].read_text(), flags=re.M)
    deps['checkedAt'] = '2026-10-12'
    deps_path = OUT / 'sine-proof-dependencies.json'
    deps_path.write_text(json.dumps(deps, ensure_ascii=False, separators=(',', ':')) + '\n')
    for n in nodes:
        for theorem in n['theorems']:
            assert theorem in deps['declarations'], theorem
    audit = (OUT / 'sine-ode-audit.txt').read_bytes()
    finite_audit = (OUT / 'sine-finite-prefix-audit.txt').read_bytes()
    if 'Sine theorem buttons' not in graph['scope']:
        graph['scope'] += ' Sine theorem buttons expose extracted proof-body and declaration-type dependencies separately.'
    graph['sineFlow'] = dict(status='checked', nodes=nodes,
        scope='The algebra and ODE routes are checked, with different endpoint scopes. Bundle arrows describe mathematical obligations. Theorem inspection shows constants extracted from checked Lean proof bodies and declaration types; expanded module arrows show literal source imports. The applied ODE route reuses finite-prefix algebra in its primary-function adapter, while its central ODE comparison has no earlier sine-identity dependency. The independent geometric circle test uses constructed common-Euler solution bounds, all-rational sign/reciprocal coverage and the whole-plane oscillator comparison. Its geometric primary definitions contain no exponential, and its proof does not reuse the previous geometric endpoint agreement.',
        proofDependencies=dict(path='sine-proof-dependencies.json', sha256=hashlib.sha256(deps_path.read_bytes()).hexdigest(), declarations=len(deps['declarations'])),
        auditSha256=hashlib.sha256(audit).hexdigest(), finiteAuditSha256=hashlib.sha256(finite_audit).hexdigest(),
        primaryDomains=dict(normalized='Rat', powerSeries='QComplex', geometricCircle='Rat (stereographic slope)'),
        geometricSourceBundle=json.loads((OUT/'geometric-circle-proof.json').read_text()),
        geometricAuditSha256=hashlib.sha256((OUT/'geometric-circle-ode-audit.txt').read_bytes()).hexdigest(),
        geometricPrimaryIndependentOfExponential=True, geometricAllRationalSlopesCovered=True,
        coreIndependentOfEarlierSineAgreement=True,
        primaryAdapterUsesFinitePrefix=True)
    (OUT / 'modular-dependencies.json').write_text(json.dumps(graph, ensure_ascii=False, separators=(',', ':')) + '\n')
    print(f'Sine graph: {len(nodes)} bundles, {len(deps["declarations"])} checked declaration records, {len(highlighted)} source snapshots.')


if __name__ == '__main__':
    update()
