#!/usr/bin/env python3
"""Install the modular arithmetic graph without modifying existing proof maps."""
from pathlib import Path
import argparse, json, hashlib, shutil, re
ROOT=Path(__file__).resolve().parents[2]
BASE=Path(__file__).with_name('modular-graph')

def model():
    def node(i,title,formula,body,files,row,col,parents):
        return dict(id=i,title=title,formula=formula,body=body,roots=['ComputableAnalysis.'+f for f in files],row=row,col=col,parents=parents)
    nodes=[
      node('raw','Rational interval foundation',r'\(x:\mathrm{RealRaw},\quad z:\mathrm{ComplexRaw}\)','A name computes rational enclosing intervals or rectangles at finite stages. Validity supplies enclosure consistency and shrinking widths; Equiv identifies names of the same value. A function field alone is not a computability certificate. The constructors below are executable and their validity is proved.',['Basic'],0,1,[]),
      node('pi','Geometric constant',r'\(\pi=4\arctan_{\rm geom}(1)\)','The exact constant used by the modular nome is geometricPiScalar, twice the real-axis embedding of GeometricPiRotation.halfPi. halfPi is a rescheduled RealRaw name of twice the geometric arctangent at one, with a cofinal rational schedule and halfPi_valid. It is not Mathlib Real.pi.',['GeometricPiRotation','ModularForms.NomeRiccatiConstant'],1,0,['raw']),
      node('exp','Entire exponential and Euler constant',r'\(\exp(z)=\sum_{n\ge0}z^n/n!,\qquad e=\exp(1)\)','The current ExponentialComputations API registers power series, the literal compound-interest limit, and the scalar linear ODE by proved exact agreement at arbitrary represented complex inputs. Complex.exp is the same entireExponentialValue used by the nome. The reference evaluator chooses a positive rational chart radius from the initial input rectangle. exponentialChart uses rational factorial coefficients, quantitative tail bounds and a BoundedSeries evaluator. Charts agree on overlap, so representation and internal radius choices are hidden. Euler’s constant is the real-axis value at one; it is not an abstract completed real.',['ExponentialComputations.API','ExponentialComputations.ComplexFunctions','ExponentialComputations.CompoundLimit','ModularForms.EntireExponential','ModularForms.ExponentialCharts','ModularForms.ExponentialMajorant'],1,2,['raw']),
      node('nome','Nome and the CM point',r'\(q(z)=\exp(2\pi iz),\quad z_{163}=(1+i\sqrt{163})/2\)','Nome is constructed from the represented exponential and geometric constant. sqrt163 is the executable rational square-root name, with square, validity and positivity proofs. CMPoint163 builds the point from these names. The growth exponent is the represented real-axis argument pi times sqrt163.',['ModularForms.Nome','ModularForms.CMPoint163','ModularForms.CMNome163'],2,1,['pi','exp']),
      node('forms','Concrete modular forms',r'\(f((az+b)/(cz+d))=(cz+d)^k f(z)\)','There is no general ModularForm record in this proof route. Concrete DomainFunctions.Map values are defined on valid upper-half-plane names. Holomorphicity, the modular weight law for SL2Z, and the Fourier/cusp conditions are proved separately. Upper weight-four and weight-six lattice sums give the actual Eisenstein maps; the discriminant has weight twelve. This is the specific evidence used by the Hecke and CM arguments.',['ModularForms.UpperLatticeHolomorphic','ModularForms.UpperLatticeModularLaw','ModularForms.LatticeDiscriminant','ModularForms.NomeNormalizedDiscriminantHolomorphic'],3,1,['nome']),
      node('j','Definition of the modular function',r'\(g_2=60G_4,\ g_3=140G_6,\ D=g_2^3-27g_3^2,\quad j=1728g_2^3/D\)','latticeJMap is a product of the actual numerator map and the reciprocal discriminant map. Its domain requires proved nonvanishing of the denominator. Holomorphicity and modular invariance are derived from the lattice maps. At the CM point, cmJValue163 is precisely latticeJMap.eval, with the nonvanishing proof supplied internally. The normalization agrees with the standard Fourier normalization.',['ModularForms.LatticeJInvariant','ModularForms.CMJDomain163','ModularForms.LatticeJModularLaw'],4,2,['forms']),
      node('tau','Discriminant coefficients',r'\(\Delta(q)=q\prod_{m\ge1}(1-q^m)^{24}=\sum_{n\ge1}\tau(n)q^n\)','tau is a literal integer coefficient algorithm from finite Euler products; stabilization proves independence of the truncation. Analytic agreement identifies that series with the actual nome-normalized discriminant. Hecke discrepancy vanishing and coefficient uniqueness prove the prime eigenvector identity, rather than assuming it.',['ModularForms.Tau','ModularForms.TauBoundedSeriesAgreement','ModularForms.TauPrimeHeckeEigenvector'],4,0,['forms']),
      node('cm','CM modular relation and integer arithmetic',r'\(P(X)=\Phi_{41}(X,X),\quad P(j(z))=0\)','The actual index-forty-one modular relation is combined with a CM lattice endomorphism. The general hecke41_repeated_j_diagonal_root law proves a diagonal root whenever an actual Hecke value repeats the base j-value; the concrete minus-163 and minus-43 points supply that evidence separately. Weighted-j coefficient agreement, sparse power traces and Newton recurrence checks recover its integer polynomial. Its diagonal has the checked squared factor at the target integer; interval transformation and sign evidence prove the remaining factor nonzero at the actual CM value. Python generates candidates; kernel proofs check the arithmetic.',['ModularForms.CMHeckeDiagonal43','ModularForms.IntegerHeckeDiagonalPolynomial41','ModularForms.Hecke41CompressedNewtonCellwiseAgreement','ModularForms.CMJQuotientNonvanishing163','ModularForms.CMJExactClassFromNewton163'],5,2,['j']),
      node('elliptic','Modular fixed-point laws',r'\(g z=z,\ (cz+d)^k\ne1\quad\Longrightarrow\quad G_k(z)=0\)',r'For the actual lattice sums, the proved modular weight law and a fixed point force a zero whenever the multiplier is not one. The weight-four case gives \(j(z)=0\); the weight-six case gives \(j(z)=1728\). The discriminant domain is constructed using global nonvanishing. These are exact laws at arbitrary valid represented inputs. This is a reusable modular-symmetry theorem, not the general CM class-polynomial theorem.',['ModularForms.EllipticFixedValues','ModularForms.GlobalDiscriminantNonvanishing'],5,1,['j','forms']),
      node('square','Elliptic CM value',r'\[j(i)=1728,\qquad j(g i)=1728\quad(g\in\mathrm{SL}_2(\mathbb Z))\]',r'The discriminant-minus-four point is the literal rational complex name squareCMPoint. The transformation \(S(z)=-1/z\) fixes \(i\) and has weight-six multiplier \(-1\). Thus the actual \(G_6(i)\) value vanishes, giving cmJValue4_exact_value. Equivalent represented names and the entire modular orbit are covered. CMJModularOrbits also extends the exact minus-163 integer value to every valid name of every modular transform of its CM point. The full class-polynomial construction, integer-coefficient theorem, conjugacy, and degree theorem remain further targets.',['ModularForms.CMJExactValue4','ModularForms.CMJModularOrbits'],6,1,['elliptic']),
      node('ramanujan','Ramanujan identities',r'\(\tau(mn)=\tau(m)\tau(n)\ (\gcd(m,n)=1)\)\n\[\tau(p^{r+2})=\tau(p)\tau(p^{r+1})-p^{11}\tau(p^r)\]','Both statements are unconditional for the literal tau coefficients; the prime-power statement assumes only primality. The proof passes through the actual modular Hecke action. Deligne’s bound is outside this development.',['ModularForms.RamanujanTauIdentities'],6,0,['tau']),
      node('integer','Exact CM integer value',r'\[j((1+i\sqrt{163})/2)=-640320^3\]','cmJValue163_exact_value has no arithmetic certificate premise. latticeJMap_cm_equivalent_value proves the same result for every equivalent valid name of the CM point and constructs domain evidence internally. This exact identity supplies the arithmetic input to the exponential showpiece.',['ModularForms.CMJExactValue163'],6,2,['cm']),
      node('error','Near-integer exponential: 163',r'\[10^{-14}\le262537412640768744-\exp(\pi\sqrt{163})\le9\cdot10^{-13}\]','The independently proved Laurent remainder bounds are combined with the exact CM integer value. EC163.exp_bounds states this bound directly using the current real exp API at the computable geometric growth argument. EC163.complex_exp_agreement proves that the modular series value agrees with Complex.exp there. EC163.deficit_bounds transports the complete CM/Laurent proof to every registered exponential computation and every equivalent valid name of the argument. Explicit compound-interest and ODE corollaries are checked.',['ModularForms.CMExponentialFoundation163','ModularForms.CMExponentialAgreement163','ModularForms.CMIntegerGrowthDeficit163','ModularForms.CMJNearIntegerError163'],7,1,['integer','nome']),
      node('error43','Near-integer exponential: 43',r'\[10^{-4}\le884736744-\exp(\pi\sqrt{43})\le3\cdot10^{-4}\]',r'This unconditional statement uses the current exponential API at geometric pi times the positive computable square root of 43. The modular integer identity appears only beneath its proof. The linear Laurent term is \(196884q\); a rationally bounded remainder is at most \(10^{-6}\). The negative nome is bounded away from zero, proving that the exponential lies below the integer. The error bound holds for every registered implementation and every equivalent valid input name. The two public showpiece statements are in NearIntegerExponentials.',['ModularForms.NearIntegerExponentials','ModularForms.CMExponentialFoundation43','ModularForms.CMJLinearLaurentEstimate43','ModularForms.CMJNearIntegerError43'],8,2,['cm43','nome']),
      node('cm43','Nontrivial CM value',r'\[j((1+i\sqrt{43})/2)=-960^3\]',r'This point is not an elliptic fixed point. Put \(z=(1+i\sqrt{43})/2\). The checked equation \(z^2-z+11=0\) gives an endomorphism \(5+z\) of norm \(41\). The fifth Hecke point \(w=(z+5)/41\) satisfies \(6-1/w=z\), so modular invariance repeats the actual j-value among the roots of the already recovered correspondence. A new kernel-checked factorization gives \(P(X)=(X+960^3)^2Q_{43}(X)\). The actual Fourier expansion puts the real j-value in \([-1500000000,-750000000]\); the homogeneous interval transform of the quotient has strictly negative coefficients, excluding every other root. All domain, validity and isolation evidence is constructed internally. The exact endpoint covers arbitrary equivalent represented names and their modular transforms. EC43 verifies agreement with the current real and complex exponential API. The general class-polynomial theorem remains open.',['ModularForms.CMPoint43','ModularForms.CMHeckeDiagonal43','ModularForms.CMExponentialBounds43','ModularForms.CMJAnalyticBounds43','ModularForms.CMJFactor43','ModularForms.CMJIsolation43','ModularForms.CMJExactValue43','ModularForms.CMExponentialAgreement43'],7,2,['cm']),
    ]
    lessons=[
      dict(node='integer',question='What must an exact proof establish?',answer=r'Put \(J=j((1+i\sqrt{163})/2)\) and \(A=-640320^3\). Computing many digits of \(J\) does not prove \(J=A\). This proof first gives an exact polynomial equation for the actual analytic value, then rules out every other factor.',formula=r'\[P(J)=0,\quad P(X)=(X-A)^2Q(X),\quad Q(J)\ne0\quad\Longrightarrow\quad J=A.\]',files=['CMJExactClassFromNewton163','CMJExactValue163']),
      dict(node='j',question='What is the function being evaluated?',answer=r'The lattice \(\mathbb Z+z\mathbb Z\) supplies weight-four and weight-six sums. Their scaled versions define \(g_2\) and \(g_3\); the discriminant supplies the denominator. The proof must establish convergence, holomorphicity, transformation laws, normalization, and a nonzero denominator at the chosen point. The integer is not built into this definition.',formula=r'\[j(z)=\frac{1728g_2(z)^3}{g_2(z)^3-27g_3(z)^2}.\]',files=['LatticeJInvariant','CMJDomain163']),
      dict(node='nome',question='Why does 41 appear when the input involves 163?',answer=r'The quadratic equation means multiplication by the CM point preserves its lattice. In the basis \((1,z)\), multiplication sends \(1\) to \(z\) and \(z\) to \(z-41\). The resulting integer matrix has determinant \(41\), giving a lattice endomorphism of index \(41\). This is the source of the modular relation used here.',formula=r'\[z^2-z+41=0,\qquad \begin{pmatrix}0&-41\\1&1\end{pmatrix},\qquad \det=41.\]',files=['CMEquation163','RecoveredHeckePolynomial41']),
      dict(node='cm',question='How does a lattice relation become a polynomial equation?',answer=r'A modular polynomial relates the j-values of lattices connected by an index-41 map. The special endomorphism connects this lattice to itself, so the same value occupies both arguments. Fourier coefficients and modular-function arguments recover an integer polynomial. Newton identities reconstruct coefficients from power sums; finite kernel checks certify the generated candidate and its agreement with the actual relation.',formula=r'\[\Phi_{41}(J,J)=0,\qquad P(X)=\Phi_{41}(X,X).\]',files=['RecoveredHeckePolynomial41','IntegerHeckeDiagonalPolynomial41','Hecke41PrincipalDiagonalAgreement','Hecke41CompressedNewtonCellwiseAgreement']),
      dict(node='cm',question='Why is this particular root forced?',answer=r'The checked polynomial factors with the square of the desired linear factor. Analytic bounds on the actual value give a real substitution in which the remaining polynomial has a proved nonzero value. No-zero-divisor algebra then forces the linear factor to vanish. This is where approximation helps prove an exact identity, rather than replacing it.',formula=r'\[0=(J+640320^3)^2Q(J),\qquad Q(J)\ne0.\]',files=['Hecke41DiagonalFactorEvaluation','CMJIsolationSubstitution163','CMJQuotientNonvanishing163','CMJExactClassFromNewton163']),
      dict(node='error',question='Where does the near-integer exponential come from?',answer=r'At this point the nome is negative and very small. The Laurent expansion has leading terms inverse nome and 744. Substitute the exact j-value, then bound the remaining Laurent tail. The large integer is the positive cube plus 744; the tiny correction accounts for the observed near-integer. The checked EC163 bridge states this result with the current exponential API and transports it to the power-series, compound-interest, and ODE implementations.',formula=r'\[q=-\exp(-\pi\sqrt{163}),\quad j=q^{-1}+744+R(q),\quad \exp(\pi\sqrt{163})=640320^3+744+R(q).\]',files=['CMExponentialFoundation163','CMExponentialAgreement163','CMIntegerGrowthDeficit163','CMJNearIntegerError163']),
    ]
    lessons.append(dict(node='square',question='What generalizes, and what is the second CM value?',answer=r'The general CM class-polynomial theorem would identify every singular modulus as an algebraic integer of degree the quadratic-order class number. That is substantially larger than our specialized proof and remains a target. The checked reusable addition here is the modular fixed-point law: covariance forces a value to vanish when its weight multiplier is not one. At the computable point \(i\), inversion fixes the point and has weight-six multiplier \(-1\), so \(G_6(i)=0\) and \(j(i)=1728\). The general represented modular-orbit law covers every equivalent name of every transform, and specializes to both known exact CM integers.',formula=r'\[S(i)=i,\quad G_6(i)=i^6G_6(i)=-G_6(i),\quad j(i)=1728.\]',files=['EllipticFixedValues','CMJExactValue4','CMJModularOrbits']))
    lessons.append(dict(node='cm43',question='How can a different CM point reuse the same modular polynomial?',answer=r'The new point satisfies a different quadratic equation. Multiplication by \(5+z\) still has norm \(41\), so it supplies an index-\(41\) self-correspondence. Its fifth Hecke representative is a modular transform of the original point. Thus the same already proved polynomial contains the new actual value as a diagonal root. Reusing the polynomial avoids a second large Fourier-coefficient reconstruction.',formula=r'\[\begin{gathered}z^2-z+11=0,\quad N(5+z)=41,\\ w=(z+5)/41,\quad 6-1/w=z,\\ P(j(z))=0.\end{gathered}\]',files=['CMPoint43','CMHeckeDiagonal43']))
    lessons.append(dict(node='cm43',question='Why does the new root equal the integer cube exactly?',answer=r'The polynomial root relation alone has many possible solutions. The separate analytic proof uses the computable geometric constant, square root and exponential, the real negative nome, and the actual Fourier quotient. It puts the value in an interval where every root of the remaining quotient is excluded by a checked sign calculation. No-zero-divisor algebra forces the squared linear factor to vanish. This is the substantive CM argument beyond the inversion symmetry used at \(i\).',formula=r'\[\begin{gathered}P(X)=(X+960^3)^2Q_{43}(X),\\ -15\cdot10^8\le j(z)\le-75\cdot10^7,\\ Q_{43}(j(z))\ne0\ \Longrightarrow\ j(z)=-960^3.\end{gathered}\]',files=['CMJAnalyticBounds43','CMJFactor43','CMJIsolation43','CMJExactValue43','CMExponentialAgreement43']))
    lessons.append(dict(node='error43',question='What does the exponential theorem say without the modular function?',answer=r'Write \(N=884736744\). The final statement bounds \(N-\exp(\pi\sqrt{43})\) between two positive rationals. The exact CM integer theorem supplies \(N\), while the Laurent series supplies the sign and error. At the actual negative nome, the linear term dominates the remainder, whose absolute value is at most \(10^{-6}\). All those hypotheses have been proved internally. The exponential is the current API value, and the theorem also holds for every registered computation and every equivalent valid represented name.',formula=r'\[10^{-4}\le884736744-\exp(\pi\sqrt{43})\le3\cdot10^{-4}.\]',files=['NearIntegerExponentials','CMExponentialFoundation43','CMJLinearLaurentEstimate43','CMJNearIntegerError43']))
    for lesson in lessons:
        lesson['roots']=['ComputableAnalysis.ModularForms.'+f for f in lesson.pop('files')]
    # Learning links add snapshots, but do not pretend to be kernel dependency edges.
    # Resolve actual source imports, not inferred mathematical theorem edges.
    modules={};todo=[r for n in nodes+lessons for r in n['roots']]
    while todo:
        m=todo.pop()
        if m in modules:continue
        p=ROOT.joinpath(*m.split('.')).with_suffix('.lean')
        if not p.exists():raise RuntimeError('Missing graph source '+str(p))
        deps=[]
        for line in p.read_text().splitlines():
            if line.startswith('import '):deps+=line.split('--')[0].split()[1:]
        modules[m]=deps;todo += [d for d in deps if d.startswith('ComputableAnalysis.')]
    snapshots={}
    for n in nodes+lessons:
        for m in n['roots']:
            p=ROOT.joinpath(*m.split('.')).with_suffix('.lean');s=p.read_text()
            snapshots[m]=dict(text=s,sha256=hashlib.sha256(s.encode()).hexdigest())
    return dict(nodes=nodes,lessons=lessons,imports=modules,sources=snapshots,constantsAudit=(ROOT/'scripts/check_modular_constants.lean').read_text(),scope='Bundle arrows are a curated mathematical outline. Expanded module arrows/lists are literal source imports, not extracted declaration-level proof dependencies.')

def install(site, foundation_audit, constants_audit, import_audit, build, cm_values_audit, cm_values_build):
    site=Path(site);site.mkdir(parents=True,exist_ok=True)
    data=model()
    audit=Path(foundation_audit).read_text()
    endpoints=['complex_exp_agreement','real_exp_agreement','implementation_agreement',
               'deficit_agreement','deficit_bounds','exp_bounds','compoundInterest_bounds','linearODE_bounds']
    endpoints=['ComputableAnalysis.ModularForms.EC163.'+n for n in endpoints]
    assert 'error:' not in audit and 'sorryAx' not in audit
    for name in endpoints:
        match=re.search("'"+re.escape(name)+r"' depends on axioms: \[([^]]*)\]",audit)
        assert match,name
        assert set(re.findall(r'[\w.]+',match[1])) <= {'propext','Classical.choice','Quot.sound'},name
    assert 'Build completed successfully' in Path(build).read_text() and 'error:' not in Path(build).read_text()
    assert 'Forbidden source occurrences: []' in Path(import_audit).read_text()
    assert 'error:' not in Path(constants_audit).read_text()
    data['exponentialFoundation']=dict(checkedEndpoints=endpoints,mathlibDependency=False,
        api='ComputableAnalysis.ExponentialComputations.API',
        axiomAuditSha256=hashlib.sha256(audit.encode()).hexdigest())
    values_audit=Path(cm_values_audit).read_text()
    values_endpoints=['modular_weight_fixed_value_zero','upperWeightFour_zero_of_modular_fixed',
        'upperWeightSix_zero_of_modular_fixed','latticeJMap_value_of_weightFour_zero',
        'latticeJMap_value_of_weightSix_zero','latticeJMap_zero_of_modular_fixed',
        'latticeJMap_1728_of_modular_fixed','squareCMPoint_fixed',
        'squareCMPoint_weightSix_nonidentity','cmJValue4_exact_value',
        'latticeJMap_squareCM_equivalent_value','latticeJMap_squareCM_orbit_value',
        'latticeJMap_squareCM_orbit_equivalent_value','latticeJMap_modular_orbit_equivalent_value',
        'latticeJMap_cm163_orbit_equivalent_value','latticeJMap_cm4_orbit_equivalent_value',
        'cmPoint43Value_quadratic','cmHeckePointFive43_action_agreement','hecke41Point_cm43_five_j',
        'hecke41_repeated_j_diagonal_root','cmJValue43_candidate_diagonal_root',
        'cmJValue43_real_isolation_bounds','cmJValue43_quotient_nonzero','cmJValue43_exact_value',
        'latticeJMap_cm43_equivalent_value','latticeJMap_cm43_orbit_equivalent_value',
        'EC43.complex_exp_agreement','EC43.real_exp_agreement','EC43.implementation_agreement',
        'cmJValue43_linear_laurent_bound','cmJGrowthError43_small_sharp',
        'cmJGrowthError43_real_upper_negative','cmJGrowthDeficit43_lower','cmJGrowthDeficit43_upper',
        'EC43.deficit_agreement','EC43.deficit_bounds','EC43.exp_bounds',
        'EC43.compoundInterest_bounds','EC43.linearODE_bounds',
        'exp_pi_sqrt43_near_integer','exp_pi_sqrt163_near_integer',
        'exp_pi_sqrt43_near_integer_for','exp_pi_sqrt163_near_integer_for']
    values_endpoints=['ComputableAnalysis.ModularForms.'+n for n in values_endpoints]
    assert 'error:' not in values_audit and 'sorryAx' not in values_audit
    for name in values_endpoints:
        match=re.search("'"+re.escape(name)+r"' depends on axioms: \[([^]]*)\]",values_audit)
        assert match,name
        assert set(re.findall(r'[\w.]+',match[1])) <= {'propext','Classical.choice','Quot.sound'},name
    values_build=Path(cm_values_build).read_text()
    assert 'Build completed successfully' in values_build and 'error:' not in values_build
    data['cmGeneralization']=dict(checkedEndpoints=values_endpoints,classPolynomialTheoremProved=False,
        scope='Unconditional near-integer exponential showpieces at geometric pi times sqrt43 and sqrt163, current API and representation agreement, and their exact modular proofs.',
        axiomAuditSha256=hashlib.sha256(values_audit.encode()).hexdigest())
    bundle=ROOT/'book/modular-dependencies/cm-values-proof.tar.gz'
    bundle_meta=json.loads((ROOT/'book/modular-dependencies/cm-values-proof.json').read_text())
    assert hashlib.sha256(bundle.read_bytes()).hexdigest()==bundle_meta['sha256']
    assert bundle.stat().st_size==bundle_meta['bytes']
    data['cmGeneralization']['sourceBundle']=bundle_meta
    data['showpiece']=dict(module='ComputableAnalysis.ModularForms.NearIntegerExponentials',
        endpoints=['ComputableAnalysis.ModularForms.exp_pi_sqrt43_near_integer',
                   'ComputableAnalysis.ModularForms.exp_pi_sqrt163_near_integer'],
        statementUsesModularFunction=False,
        bounds={'43':{'integer':'884736744','lower':'1/10000','upper':'3/10000'},
                '163':{'integer':'262537412640768744','lower':'1/100000000000000','upper':'9/10000000000000'}})
    shutil.copy(bundle,site/'modular-cm-values-proof.tar.gz')
    shutil.copy(cm_values_audit,site/'modular-cm-values-audit.txt')
    shutil.copy(cm_values_build,site/'modular-cm-values-build.txt')
    shutil.copy(ROOT/'scripts/check_cm_elliptic_values.lean',site/'check_cm_elliptic_values.lean')
    (site/'modular-dependencies.json').write_text(json.dumps(data))
    shutil.copy(BASE/'page.html',site/'modular-proofs.html')
    shutil.copy(foundation_audit,site/'modular-exponential-foundation-audit.txt')
    shutil.copy(constants_audit,site/'modular-constants-audit.txt')
    shutil.copy(import_audit,site/'modular-import-audit.txt')
    shutil.copy(build,site/'modular-exponential-foundation-build.txt')
    shutil.copy(ROOT/'scripts/check_cm163_exponential_foundation.lean',site/'check_cm163_exponential_foundation.lean')
    print(json.dumps({'page':'modular-proofs.html','bundles':len(data['nodes']),'sourceModules':len(data['imports']),'sourceSnapshots':len(data['sources'])}))

if __name__=='__main__':
    p=argparse.ArgumentParser()
    for flag in ['site','foundation-audit','constants-audit','import-audit','build','cm-values-audit','cm-values-build']:
        p.add_argument('--'+flag,required=True)
    args=p.parse_args();install(args.site,args.foundation_audit,args.constants_audit,args.import_audit,args.build,args.cm_values_audit,args.cm_values_build)
