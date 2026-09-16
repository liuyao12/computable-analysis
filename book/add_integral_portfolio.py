#!/usr/bin/env python3
"""Two new paired integral families, real reference witnesses and cumulative costs.
Existing Cartwright, cosine and radical diagrams are retained byte-for-byte.
"""
from __future__ import annotations
from collections import defaultdict,deque
from copy import deepcopy
from pathlib import Path
import gzip,hashlib,json,shutil,sys,textwrap
from fractions import Fraction as Q
from bs4 import BeautifulSoup
import pygraphviz as pgv
from build import shell
ROOT=Path(__file__).resolve().parents[1];SITE=ROOT/'blueprint/web'
sys.path.insert(0,str(ROOT/'blueprint/checks'))
from build_proof_bench import closure,source_index,source_union,origin,ORIGINS
P='ComputableAnalysis.';W=P+'Wallis.';B=P+'BetaIntegral.'
M='MathlibComparison.';MW=M+'Wallis.';MB=M+'BetaIntegral.'
F=P+'FiniteSampleCalculus.';R=P+'RationalLipschitzIntegral.'
ROUTES=['ftc','mathlib'];COLORS={1:'#326493',2:'#7755a0'}
TARGETS={'thm:wallis-integrals':'wallis-factorials','thm:wallis-product':'wallis-product',
         'thm:beta-integral':'beta-factorials','thm:beta-normalization':'beta-normalization'}
OPTIONS=[['wallis-laws','Wallis: recurrence laws'],['wallis-evaluation','Wallis: uniform evaluation'],
 ['wallis-factorials','Wallis: factorial evaluations'],['wallis-product','Wallis: rational pi bounds'],
 ['beta-laws','Beta: recurrence laws'],['beta-evaluation','Beta: uniform evaluation'],
 ['beta-factorials','Beta: factorial evaluation'],['beta-normalization','Beta: density normalization']]
BUNDLES={
 'ip:numbers':('Computable numbers','Shared computational objects',[P+'QInterval',P+'RealRaw',P+'RealRaw.Valid'],r'<p>Numbers are programs returning ordered nested rational boxes with shrinking widths. The integral construction includes a supplied schedule and a proof of these properties; no integrability predicate is introduced.</p>'),
 'ip:geometry':('Geometric pi and trigonometry','Existing foundation reused',[P+'CosinePrimitive.pi',P+'CartwrightMoments.frequency',P+'ClockTrigonometry.cosine',P+'ClockTrigonometry.c'],r'<p>The original sector-area construction gives \(\pi=4A(1)\). In quarter-turn coordinates put \(\lambda=\pi/2\), \(c(t)=C(t/2)\), \(s(t)=S(t/2)\). None is defined using the new integrals.</p>'),
 'ip:wallis-construction':('Chosen cosine-power quadratures','Joint schedule and independent validity',[
 W+'sample',W+'sample_unit',W+'sample_decreases',W+'sample_error',W+'data',W+'integral',W+'integral_valid',W+'integral_width',W+'mesh_error',P+'MonotoneAverage.left',P+'MonotoneSampleIntegral.raw'],r'<p>For \(W_n=\int_0^1c(t)^n\,dt\), use dyadic subdivision depth k and cosine-evaluation stage k. The uniform power-error estimate certifies this particular diagonal.</p><div class="displaymath">\[\operatorname{width}((W_n)_k)\le2(1+112n)2^{-k}.\]</div><p>The radius is deliberately conservative. Validity uses decreasing samples and evaluation-error control, not the proposed recurrence or value.</p>'),
 'ip:power-calculus':('Finite power and product estimates','Local calculus reused',[P+'UnitPowerCalculus.modelPower',F+'Model',F+'Model.local_error',F+'Model.mul'],r'<p>Finite difference estimates give a quantitative power rule and product rule. The specified model retains a quadratic cell error and finite sample bounds. No general derivative existence is obtained by choice.</p>'),
 'ip:ftc':('Quantitative FTC','Reusable native calculus',[F+'chosen_samples_FTC'],r'<p>The FTC consumes a proved local model and a bound comparing a chosen quadrature with every fixed finite mesh. It concludes agreement with the primitive endpoint difference. The quadrature has already been independently defined and validated.</p>'),
 'ip:wallis-primitive':('Cosine-power primitive','Native calculus middle',[W+'primitive',W+'derivative',W+'primitiveModel',W+'recurrence_viaFTC',P+'CartwrightMoments.sineModel',P+'CartwrightMoments.cosineModel'],r'<p>Use \(F_n(t)=s(t)c(t)^{n+1}\).</p><div class="displaymath">\[F_n^{\prime}=\lambda((n+2)c^{n+2}-(n+1)c^n).\]</div><p>Both endpoints vanish. The finite power/product model and FTC give the reduction recurrence. This does not assume the entire primitive is concave.</p>'),
 'ip:wallis-laws':('Cosine-power recurrence','Same closed analytic contract',[W+'Laws',W+'lawsViaFTC',MW+'lawsViaMathlib'],r'<p>The two closed proofs inhabit the same proposition:</p><div class="displaymath">\[\begin{gathered}W_0=1,\quad\lambda W_1=1,\\(n+2)W_{n+2}=(n+1)W_n.\end{gathered}\]</div><p>The Lean interface uses vanishing errors between rational samples. Each route supplies these laws without a caller-provided analytic certificate.</p>'),
 'ip:wallis-endpoints':('Rational coefficients and factorials','Shared finite arithmetic',[W+'coefficient',W+'coefficient_pos',W+'coefficient_even',W+'coefficient_odd',W+'product',W+'product_zero',W+'product_step',W+'upper_ratio'],r'<p>Calculate \(a_0=a_1=1\), \(a_{n+2}=(n+1)a_n/(n+2)\) by rational recursion. Pure arithmetic gives</p><div class="displaymath">\[\begin{aligned}4^n(n!)^2a_{2n}&=(2n)!,\\(2n+1)!a_{2n+1}&=4^n(n!)^2.\end{aligned}\]</div><p>The ratio \(R_n=a_{2n+1}/a_{2n}\) is the finite Wallis product. Its computation and factorial interpretation have no analytic dependency.</p>'),
 'ip:wallis-evaluation':('Uniform cosine-power evaluation','Shared recurrence algebra',[W+'Statement',W+'evaluation_samples',W+'evaluation_of_laws',W+'evaluation_viaFTC',W+'evaluation_viaMathlib'],r'<p>Finite induction in the common laws proves \(W_{2n}=a_{2n}\) and \(\lambda W_{2n+1}=a_{2n+1}\). The exact same native proposition is established by either route; its algorithm is not defined by these coefficients.</p>'),
 'ip:wallis-squeeze':('Squeeze between consecutive powers','Order after the calculus',[W+'integralSample_power_decreases',W+'product_bounds_of_laws'],r'<p>The sampled cosine lies in [0,1], so its powers decrease. Transport the exact sample inequalities through the evaluations:</p><div class="displaymath">\[W_{2n+2}\le W_{2n+1}\le W_{2n}.\]</div><p>This shared consumer turns whichever analytic proof was supplied into rational bounds on geometric pi.</p>'),
 'thm:wallis-integrals':('Wallis integral evaluations','One proposition with alternative proofs',[W+'FactorialStatement',W+'factorials_of_laws',W+'factorials_viaFTC',W+'factorials_viaMathlib'],r'<div class="displaymath">\[\begin{aligned}4^n(n!)^2W_{2n}&\simeq(2n)!,\\(2n+1)!\lambda W_{2n+1}&\simeq4^n(n!)^2.\end{aligned}\]</div><p>All n are quantified in one checked theorem type, not a collection of finite numerical checks.</p>'),
 'thm:wallis-product':('Rational Wallis-product bounds','Arithmetic application',[W+'ProductBoundsStatement',W+'productBounds_viaFTC',W+'productBounds_viaMathlib'],r'<div class="displaymath">\[2R_n\le\pi\le2a_{2n+1}/a_{2n+2}.\]</div><p>The equivalent upper expression is \(2R_n(2n+2)/(2n+1)\). Both rational endpoints are computed without pi, cosine or integration. The proof relates them to the original geometric pi program.</p>'),
 'ip:beta-construction':('Chosen beta-polynomial quadratures','Explicit bound and successful schedule',[B+'integrand',B+'integrand_lipschitz',B+'data',B+'integral',B+'integral_valid',B+'integral_width',B+'mesh_error',R+'raw',R+'refinement',R+'valid'],r'<p>The rational-input samples \(x^m(1-x)^n\) are exact rationals. This integrand is generally not monotone: the supplied Lipschitz bound m+n controls every cell, including its turn.</p><div class="displaymath">\[\operatorname{width}((B_{m,n})_k)\le2(m+n)2^{-k}.\]</div><p>A finite dyadic schedule and prefix intersection give a valid computation. The beta value and the FTC are not used for this validity proof.</p>'),
 'ip:beta-primitive':('Polynomial beta primitive','Native calculus middle',[B+'primitive',B+'derivative',B+'primitiveModel',B+'step_viaFTC'],r'<p>Differentiate \(x^{m+1}(1-x)^{n+1}\), apply FTC to its zero endpoint difference, and use the finite identity \(x+(1-x)=1\). The base integral is obtained from \(x^{m+1}\).</p><p>Zero exponents are handled by the base theorem; no unproved endpoint vanishing is assumed.</p>'),
 'ip:beta-laws':('Beta recurrence','Same closed analytic contract',[B+'Laws',B+'lawsViaFTC',MB+'lawsViaMathlib'],r'<div class="displaymath">\[\begin{gathered}(m+1)B_{m,0}=1,\\(m+n+2)B_{m,n+1}=(n+1)B_{m,n}.\end{gathered}\]</div><p>Both proofs supply these exact laws for the same native quadrature. Neither assumes a beta/gamma formula in the native validity argument.</p>'),
 'ip:beta-endpoints':('Factorial coefficients','Shared finite arithmetic',[B+'value',B+'factorial_value',B+'normalizer',B+'normalizer_pos',B+'normalizer_factorial'],r'<p>The endpoint is a rational recursion \(v_{m,0}=1/(m+1)\), \(v_{m,n+1}=(n+1)v_{m,n}/(m+n+2)\). Finite arithmetic proves</p><div class="displaymath">\[(m+n+1)!v_{m,n}=m!n!.\]</div><p>The positive coefficient \(1/v_{m,n}\) is computed without evaluating an integral.</p>'),
 'ip:beta-evaluation':('Uniform beta evaluation','Shared finite induction',[B+'Statement',B+'evaluation_samples',B+'evaluation_of_laws',B+'evaluation_viaFTC',B+'evaluation_viaMathlib'],r'<p>The common recurrence laws identify the native integral program with the independently specified rational value \(v_{m,n}\), uniformly in both natural parameters. No fixed-degree examples substitute for the general theorem.</p>'),
 'thm:beta-integral':('Beta integral evaluation','One proposition with alternative proofs',[B+'FactorialStatement',B+'factorial_of_laws',B+'factorial_viaFTC',B+'factorial_viaMathlib'],r'<div class="displaymath">\[\boxed{(m+n+1)!B_{m,n}\simeq m!n!.}\]</div><p>The factorial scaling is exact rational arithmetic; the integral is the independently computed dyadic program. The two full theorem types are identical.</p>'),
 'thm:beta-normalization':('Beta polynomial normalization','Application of the same evaluation',[B+'NormalizationStatement',B+'normalization_of_laws',B+'normalization_viaFTC',B+'normalization_viaMathlib'],r'<div class="displaymath">\[\boxed{\frac{(m+n+1)!}{m!n!}B_{m,n}\simeq1.}\]</div><p>The normalizer is a rational arithmetic expression, not a reciprocal of the integral. Scaling the chosen integral defines the corresponding polynomial-density quadrature.</p>'),
 'ip:mathlib-integral':('Mathlib general and interval integrals','Comparison foundation',['MeasureTheory.lintegral','MeasureTheory.integral','intervalIntegral','intervalIntegral.integral_mono_on','intervalIntegral.integral_add_adjacent_intervals'],r'<p>The real interval integral rests on general Bochner integration and its nonnegative measure-theoretic construction. The quadrature bridge uses integral order and finite additivity. These declarations do not supply numerical data to the native programs.</p>'),
 'ip:mathlib-ftc':('Mathlib FTC and integration by parts','Comparison calculus',['intervalIntegral.integral_eq_sub_of_hasDerivAt','intervalIntegral.integral_mul_deriv_eq_deriv_mul','integral_pow'],r'<p>These are the actual FTC and integration-by-parts declarations used by the comparison. All differentiability and interval-integrability hypotheses are visible in their checked types. The integral-power and cosine-power theorems are not numerical definitions.</p>'),
 'ip:mathlib-trig':('Complex exponential and trigonometry','Mathlib comparison objects',['Complex.exp','Real.cos','Real.sin','Real.pi','Real.hasDerivAt_cos','Real.hasDerivAt_sin'],r'<p>Mathlib’s exponential construction supplies sine and cosine. The existing value bridge identifies them with our arctangent-based programs. Only the Wallis branch uses trigonometry; it is not inserted into the beta proof map merely because a source import contains it.</p>'),
 'ip:wallis-bridge':('Cosine-power quadrature correspondence','Independent of evaluation',[MW+'samples_tendsto',MW+'integral_samples_tendsto',MW+'integral_represents',M+'RealDyadicAverages.diagonal_tendsto'],r'<p>The rational cosine samples converge to Mathlib’s cosine. Finite monotone rectangles and the supplied joint-stage estimates identify the very same W_n with the real integral.</p><p>This bridge does not call a cosine-power reduction or a native endpoint proof.</p>'),
 'ip:mathlib-wallis':('Mathlib cosine-power reduction','Comparison middle',[MW+'moment',MW+'change_variable',MW+'moment_recurrence','integral_cos_pow_aux'],r'<p>A change of variable converts the unit quarter-turn integral to Mathlib’s integral over [0,pi/2]. Its integration-by-parts cosine-power theorem gives the recurrence, independently of our native FTC derivation.</p>'),
 'ip:beta-bridge':('Beta quadrature correspondence','Independent of evaluation',[MB+'samples_tendsto',MB+'integral_represents',M+'RealLipschitzAverages.rectangle_error',M+'RealLipschitzAverages.samples_tendsto'],r'<p>Exact rational polynomial samples agree with the real polynomial. Cellwise integral inequalities give the Lipschitz rectangle error and establish all-stage representation of the native beta integral.</p><p>Neither the beta value nor its recurrence is used to prove this correspondence.</p>'),
 'ip:mathlib-beta':('Mathlib polynomial FTC','Comparison middle',[MB+'integrand',MB+'moment',MB+'derivative',MB+'moment_base',MB+'moment_parts',MB+'moment_step'],r'<p>Mathlib independently differentiates \(x^{m+1}(1-x)^{n+1}\) and applies its FTC. The zero endpoint difference and polynomial decomposition produce the beta recurrence. No native analytic law is reused.</p>')}

def witness(nodes,start,goal,mode='proof'):
    q=deque([start]);previous={start:None}
    while q:
        n=q.popleft()
        if n==goal:
            out=[]
            while n is not None:out.append(n);n=previous[n]
            return out
        d=nodes[n]
        if mode=='statement' and d['kind'] not in ('def','definition','opaque'):continue
        fields=['bodyRefs'] if mode=='statement' or (mode=='proof' and n==start) else ['bodyRefs','typeRefs']
        for dep in sorted({x for k in fields for x in d[k]}):
            if dep not in previous:previous[dep]=n;q.append(dep)
    return None

def comparison(raw,nodes,sha):
    records,cache,hashes=source_index(nodes)
    def cost(names):
        src=source_union(names,records,cache)
        return dict(declarations=len(names),codeLines=src['nonblankCodeLines'],mappedDeclarations=src['mappedDeclarations'],
          unmappedDeclarations=src['unmappedDeclarations'],bodyDag=sum(nodes[n]['bodyDag'] for n in names),bodyTree=sum(nodes[n]['bodyTree'] for n in names))
    prior={r:closure(nodes,[name]) for r,name in zip(ROUTES,raw['priorBaselines'])}
    cases={};closures={}
    for key,title in OPTIONS:
        roots={x['route']:x for x in raw['roots'] if x['case']==key};sets={r:closure(nodes,[roots[r]['root']]) for r in ROUTES}
        closures[key]=sets;shared=set.intersection(*sets.values());statement=set().union(*(closure(nodes,nodes[roots[r]['root']]['typeRefs']) for r in ROUTES))
        rows={}
        for r in ROUTES:
            costs={}
            for baseline,names in [('full',sets[r]),('statement-free',sets[r]-statement),('shared-free',sets[r]-shared),('after-cartwright',sets[r]-prior[r])]:
                result=cost(names);result['origins']={o:cost({n for n in names if origin(nodes[n]['module'])==o}) for o in ORIGINS}
                assert sum(v['declarations'] for v in result['origins'].values())==result['declarations']
                assert sum(v['codeLines'] for v in result['origins'].values())==result['codeLines']
                costs[baseline]=result
            rows[r]=dict(roots=[roots[r]['root']],costs=costs,finalApplication=cost({roots[r]['root']}),axioms=roots[r]['axioms'])
        cases[key]=dict(title=title,routes=rows,baselines=dict(statementDeclarations=len(statement),sharedDeclarations=len(shared)))
    order=['wallis-factorials','wallis-product','beta-factorials','beta-normalization'];portfolio={}
    for r in ROUTES:
        used=set(prior[r]);steps=[]
        for c in order:
            added=closures[c][r]-used;used|=closures[c][r]
            steps.append(dict(case=c,additional=cost(added),cumulative=cost(used)))
        portfolio[r]=dict(order=order,baseline=cost(prior[r]),steps=steps,total=cost(used),newLibrary=cost(used-prior[r]))
    return dict(schemaVersion=2,sourceCommit=sha,routeOrder=ROUTES,routeLabels=dict(ftc='Computable FTC',mathlib='Mathlib + bridges'),
      caseOptions=OPTIONS,baselineOptions=[['full','Full used library'],['statement-free','Beyond statement prerequisites'],['shared-free','Beyond shared prerequisites'],['after-cartwright','Additional after Cartwright']],
      baselineDescriptions={'full':'All transitive declaration types and bodies, with each declaration counted once.',
       'statement-free':'The union of both statement-prerequisite closures is treated as already available.',
       'shared-free':'The intersection of both proof closures is treated as already available; it is not mathematically free.',
       'after-cartwright':'The matching preceding Cartwright pi-squared proof is already available. These are explicit route-specific prior libraries, not identical baselines.'},
      cases=cases,portfolio=portfolio,priorRoots=raw['priorBaselines'],sourceAvailability=hashes,method='True type/body closures; union of available source ranges without comments/blank lines. No import counting or invented timings.',families=2)

def main():
    reading=SITE/'reading';maps=json.loads((reading/'maps.json').read_text());sha=maps['sourceCommit']
    raw=json.loads((ROOT/'comparison/reports/integral-portfolio.json').read_text());assert all(raw['checks'].values())
    nodes={n['id']:n for n in raw['nodes']};decls={d['name']:d for d in raw['declarations']}
    # Reuse the already checked rational/Cauchy foundation bundles. Their exact
    # declarations and pinned provenance are retained, not newly paraphrased.
    reused={}
    for key,oldkey,title in [('ip:rationals','def:c3-rationals','Rational arithmetic'),('ip:mathlib-real','def:c3-mreal','Mathlib real numbers')]:
        old=deepcopy(maps['bundles'][oldkey]);old['title']=title;reused[key]=old
        BUNDLES[key]=(title,'Shared foundation', [d['name'] for d in old['declarations']],old['mathHtml'])
        for d in old['declarations']:decls.setdefault(d['name'],d)
    original={str(p.relative_to(SITE)):hashlib.sha256(p.read_bytes()).hexdigest() for p in
      [SITE/'proof-bench/data.json',*reading.glob('cosine-*.svg'),*reading.glob('cartwright-*.svg'),reading/'dyadic-product.svg'] if p.exists()}
    stats=comparison(raw,nodes,sha)
    for key,(title,role,names,math) in BUNDLES.items():
        cards=[]
        for name in names:
            if key in reused:
                cards.append(deepcopy(decls[name]));continue
            d=deepcopy(decls[name]);d['realDependencyPath']=witness(nodes,name,'Real','references') or []
            module=d['ownerModule'];path=module.replace('.','/')+'.lean'
            if module.startswith('Mathlib.'):
                url='https://github.com/leanprover-community/mathlib4/blob/51e6992efd06126df61a496bebf8f49482a4e129/'+path
            else:url=f'https://github.com/liuyao12/computable-analysis/blob/{sha}/'+('comparison/' if module.startswith('MathlibComparison') else '')+path
            span=d.get('sourceRange');d['sourceUrl']=url+(f'#L{span["start"]}-L{span["end"]}' if span else '')
            cards.append(d)
        uses=[bool(d['realDependencyPath']) for d in cards];kind='mathlib' if all(uses) else 'mixed' if any(uses) else 'native'
        maps['bundles'][key]=dict(title=title,anchors=names,groups=[dict(title='Checked definitions and statements',names=names)],declarations=cards,
          declarationCount=len(cards),classification=kind,mathHtml=math,strategy=dict(role=role,summary='',groups={}))
    edges=[]
    def edge(s,t,start,goal,route=None,kind='proof'):
        w=witness(nodes,start,goal,kind);assert w,(s,t,start,goal,kind)
        assert start in BUNDLES[t][2] and goal in BUNDLES[s][2],(s,t,start,goal,'undeclared anchor')
        edges.append(dict(source=s,target=t,witness=w,route=route,kind=kind,globalEdge=route is None,
          label=BUNDLES[s][0]+' in the statement' if kind=='statement' else 'Definition dependency' if kind=='construction' else 'Shared finite argument' if route is None else 'Computable FTC' if route==1 else 'Mathlib proof'))
    # Construction and independent convergence.
    edge('ip:rationals','ip:numbers',P+'RealRaw.Valid','Rat',None,'construction')
    edge('ip:rationals','ip:mathlib-real','Real.ofCauchy','Rat',None,'construction')
    edge('ip:mathlib-real','ip:mathlib-integral','intervalIntegral','Real',2,'construction')
    edge('ip:numbers','ip:wallis-construction',W+'integral',P+'RealRaw',None,'construction')
    edge('ip:geometry','ip:wallis-construction',W+'sample',P+'ClockTrigonometry.c',None,'construction')
    edge('ip:numbers','ip:beta-construction',B+'integral',P+'RealRaw',None,'construction')
    edge('ip:geometry','ip:wallis-primitive',W+'primitiveModel',P+'ClockTrigonometry.c',1)
    edge('ip:power-calculus','ip:wallis-primitive',W+'primitiveModel',P+'UnitPowerCalculus.modelPower',1)
    edge('ip:ftc','ip:wallis-primitive',W+'recurrence_viaFTC',F+'chosen_samples_FTC',1)
    edge('ip:wallis-construction','ip:wallis-primitive',W+'recurrence_viaFTC',W+'mesh_error',1)
    edge('ip:power-calculus','ip:beta-primitive',B+'primitiveModel',P+'UnitPowerCalculus.modelPower',1)
    edge('ip:ftc','ip:beta-primitive',B+'step_viaFTC',F+'chosen_samples_FTC',1)
    edge('ip:beta-construction','ip:beta-primitive',B+'step_viaFTC',B+'mesh_error',1)
    edge('ip:wallis-primitive','ip:wallis-laws',W+'lawsViaFTC',W+'recurrence_viaFTC',1)
    edge('ip:beta-primitive','ip:beta-laws',B+'lawsViaFTC',B+'step_viaFTC',1)
    # Mathlib's distinct infrastructure and the bridges, not native laws.
    edge('ip:mathlib-integral','ip:mathlib-ftc','intervalIntegral.integral_eq_sub_of_hasDerivAt','intervalIntegral',2,'construction')
    edge('ip:mathlib-trig','ip:wallis-bridge',MW+'samples_tendsto','Real.cos',2)
    edge('ip:geometry','ip:wallis-bridge',MW+'samples_tendsto',P+'ClockTrigonometry.c',2)
    edge('ip:wallis-construction','ip:wallis-bridge',MW+'integral_represents',W+'integral_valid',2)
    edge('ip:mathlib-integral','ip:wallis-bridge',M+'RealDyadicAverages.diagonal_tendsto','intervalIntegral.integral_mono_on',2)
    edge('ip:mathlib-ftc','ip:mathlib-wallis',MW+'moment_recurrence','intervalIntegral.integral_mul_deriv_eq_deriv_mul',2)
    edge('ip:mathlib-trig','ip:mathlib-wallis',MW+'moment_recurrence','Real.hasDerivAt_cos',2)
    edge('ip:wallis-bridge','ip:wallis-laws',MW+'lawsViaMathlib',MW+'integral_samples_tendsto',2)
    edge('ip:mathlib-wallis','ip:wallis-laws',MW+'lawsViaMathlib',MW+'moment_recurrence',2)
    edge('ip:beta-construction','ip:beta-bridge',MB+'integral_represents',B+'integral_valid',2)
    edge('ip:mathlib-integral','ip:beta-bridge',M+'RealLipschitzAverages.rectangle_error','intervalIntegral.integral_mono_on',2)
    edge('ip:mathlib-ftc','ip:mathlib-beta',MB+'moment_parts','intervalIntegral.integral_eq_sub_of_hasDerivAt',2)
    edge('ip:beta-bridge','ip:beta-laws',MB+'lawsViaMathlib',MB+'samples_tendsto',2)
    edge('ip:mathlib-beta','ip:beta-laws',MB+'lawsViaMathlib',MB+'moment_step',2)
    for route,suffix in [(1,'FTC'),(2,'Mathlib')]:
        edge('ip:wallis-laws','ip:wallis-evaluation',W+'evaluation_via'+suffix,W+'lawsViaFTC' if route==1 else MW+'lawsViaMathlib',route)
        edge('ip:beta-laws','ip:beta-evaluation',B+'evaluation_via'+suffix,B+'lawsViaFTC' if route==1 else MB+'lawsViaMathlib',route)
        edge('ip:wallis-laws','thm:wallis-integrals',W+'factorials_via'+suffix,W+'lawsViaFTC' if route==1 else MW+'lawsViaMathlib',route)
        edge('ip:wallis-laws','thm:wallis-product',W+'productBounds_via'+suffix,W+'lawsViaFTC' if route==1 else MW+'lawsViaMathlib',route)
        edge('ip:beta-laws','thm:beta-integral',B+'factorial_via'+suffix,B+'lawsViaFTC' if route==1 else MB+'lawsViaMathlib',route)
        edge('ip:beta-laws','thm:beta-normalization',B+'normalization_via'+suffix,B+'lawsViaFTC' if route==1 else MB+'lawsViaMathlib',route)
    edge('ip:wallis-evaluation','thm:wallis-integrals',W+'factorials_of_laws',W+'evaluation_samples')
    edge('ip:wallis-endpoints','thm:wallis-integrals',W+'factorials_of_laws',W+'coefficient_even')
    edge('ip:wallis-evaluation','ip:wallis-squeeze',W+'product_bounds_of_laws',W+'evaluation_samples')
    edge('ip:wallis-construction','ip:wallis-squeeze',W+'integralSample_power_decreases',W+'sample_unit')

    for route,suffix in [(1,'FTC'),(2,'Mathlib')]:
        edge('ip:wallis-squeeze','thm:wallis-product',W+'productBounds_via'+suffix,W+'product_bounds_of_laws',route)
    edge('ip:beta-evaluation','thm:beta-integral',B+'factorial_of_laws',B+'evaluation_samples')
    edge('ip:beta-evaluation','thm:beta-normalization',B+'normalization_of_laws',B+'evaluation_samples')
    # factorial/normalization helpers use the shared sample evaluation lemma,
    # not the final equiv wrapper, so expose that exact lemma in the bundle.
    # Its type is exported below as an explicit checked declaration.
    edge('ip:beta-endpoints','thm:beta-integral',B+'factorial_of_laws',B+'factorial_value')
    edge('ip:beta-endpoints','thm:beta-normalization',B+'normalization_of_laws',B+'normalizer_pos')
    for target in ['thm:wallis-integrals','thm:wallis-product']:
        statement=W+('FactorialStatement' if target.endswith('integrals') else 'ProductBoundsStatement')
        edge('ip:geometry',target,statement,P+'CartwrightMoments.frequency' if target.endswith('integrals') else P+'CosinePrimitive.pi',None,'statement')
    edge('ip:wallis-construction','thm:wallis-integrals',W+'FactorialStatement',W+'integral',None,'statement')
    edge('ip:wallis-endpoints','thm:wallis-product',W+'ProductBoundsStatement',W+'product',None,'statement')
    edge('ip:beta-construction','thm:beta-integral',B+'FactorialStatement',B+'integral',None,'statement')
    edge('ip:beta-construction','thm:beta-normalization',B+'NormalizationStatement',B+'integral',None,'statement')
    edge('ip:beta-endpoints','thm:beta-normalization',B+'NormalizationStatement',B+'normalizer',None,'statement')
    familysets={
      'wallis':{'ip:rationals','ip:mathlib-real','ip:numbers','ip:geometry','ip:wallis-construction','ip:power-calculus','ip:ftc','ip:wallis-primitive','ip:wallis-laws','ip:wallis-endpoints','ip:wallis-evaluation','ip:mathlib-integral','ip:mathlib-ftc','ip:mathlib-trig','ip:wallis-bridge','ip:mathlib-wallis'},
      'beta':{'ip:rationals','ip:mathlib-real','ip:numbers','ip:beta-construction','ip:power-calculus','ip:ftc','ip:beta-primitive','ip:beta-laws','ip:beta-endpoints','ip:beta-evaluation','ip:mathlib-integral','ip:mathlib-ftc','ip:beta-bridge','ip:mathlib-beta'}}
    reports={}
    for target,case in TARGETS.items():
        family='wallis' if 'wallis' in target else 'beta';ids=familysets[family]|{target}
        if target=='thm:wallis-product':ids.add('ip:wallis-squeeze')
        views={}
        for view in ['all','1','2']:
            visible=set(ids)
            if view=='1':visible-={k for k in ids if k.startswith('ip:mathlib') or k.endswith('-bridge')}
            if view=='2':visible-={'ip:power-calculus','ip:ftc','ip:wallis-primitive','ip:beta-primitive'}
            active=[e for e in edges if e['source'] in visible and e['target'] in visible and (view=='all' or e['route'] is None or str(e['route'])==view)]
            g=pgv.AGraph(strict=True,directed=True,rankdir='TB',bgcolor='transparent',splines='spline',ranksep='.58',nodesep='.35')
            g.node_attr.update(shape='box',style='rounded,filled',fontname='Helvetica',fontsize='12',margin='.15,.12',color='#879a8c')
            g.edge_attr.update(arrowhead='vee',arrowsize='.65')
            for k in sorted(visible):
                kind=maps['bundles'][k]['classification'];fill='#eef3ed' if kind=='native' else '#f0eafa'
                if kind=='mixed':fill='#eef3ed:#f0eafa' if view=='all' else '#eef3ed' if view=='1' else '#f0eafa'
                g.add_node(k,label='\n'.join(textwrap.wrap(BUNDLES[k][0],27)),fillcolor=fill,penwidth='2.2' if k==target else '1.1')
            grouped=defaultdict(list)
            for e in active:grouped[e['source'],e['target']].append(e)
            for (s,t),es in grouped.items():
                kind='statement' if any(e['kind']=='statement' for e in es) else 'proof' if any(e['kind']=='proof' for e in es) else 'construction'
                rs={e['route'] for e in es if e['route'] is not None}
                color='#202020' if kind!='proof' else ':'.join(COLORS[r] for r in sorted(rs)) if rs else '#54725b' if view=='all' else COLORS[int(view)]
                g.add_edge(s,t,color=color,penwidth='1.6' if kind=='proof' else '1.1')
            g.add_subgraph(['ip:rationals'],rank='min')
            g.add_subgraph([target],rank='max')
            degree={str(n):g.in_degree(n) for n in g.nodes()};todo=[n for n,d in degree.items() if not d];count=0
            while todo:
                n=todo.pop();count+=1
                for child in g.successors(n):
                    child=str(child);degree[child]-=1
                    if not degree[child]:todo.append(child)
            assert count==len(visible) and not list(g.successors(target))
            g.layout('dot');svg=BeautifulSoup(g.draw(format='svg').decode(),'html.parser').svg
            for attr in ['width','height']:svg.attrs.pop(attr,None)
            for e in svg.select('g.node'):
                key=e.title.get_text();e['data-node']=key;e['tabindex']='0';e['role']='button';e['aria-label']=BUNDLES[key][0]
            for e in svg.select('g.edge'):
                s,t=e.title.get_text().split('->');es=grouped[s,t]
                kind='statement' if any(x['kind']=='statement' for x in es) else 'proof' if any(x['kind']=='proof' for x in es) else 'construction'
                e['data-edge']=s+'->'+t;e['data-edge-kind']=kind;e['tabindex']='0';e['role']='button'
            filename=f'reading/portfolio-{target.split(":")[1]}-{view}.svg';(SITE/filename).write_text(str(svg));views[view]=filename
            reports[target+'/'+view]=dict(nodes=len(visible),edges=len(grouped))
        maps['theorems'][target]=dict(id=target,title=BUNDLES[target][0],sink=target,checkedComparison=True,verifiedGraph=True,
          status='Same computational statement · independent FTC and Mathlib proofs',page='integral-families.html',views=views,
          routeNames=['','Computable FTC','Mathlib comparison'],routeButtons={'1':'Computable FTC','2':'Mathlib'},
          comparison=dict(url='reading/integral-portfolio-comparison.json',defaultCase=case))
        maps['witnesses']=[e for e in maps['witnesses'] if e.get('map')!=target]+[dict(e,map=target) for e in edges if e['source'] in ids and e['target'] in ids]
    data=dict(sourceCommit=sha,families=2,closedProofs=raw['roots'],checks=raw['checks'],views=reports,unchangedArtifacts=original,
      priorBaseline='Matching Cartwright pi-squared route; reuse charged by dependency union, not sums of standalone counts.')
    maps['integralPortfolio']=data
    (reading/'maps.json').write_text(json.dumps(maps,separators=(',',':')))
    (reading/'integral-portfolio-audit.json').write_text(json.dumps(data,indent=2)+'\n')
    (reading/'integral-portfolio-comparison.json').write_text(json.dumps(stats,indent=2)+'\n')
    with gzip.open(reading/'integral-portfolio.json.gz','wt') as f:json.dump(raw,f,separators=(',',':'))
    rows=''.join('<tr><th>'+dict(OPTIONS)[key]+'</th>'+''.join('<td>'+format(stats['cases'][key]['routes'][r]['costs']['full']['declarations'],',')+' / '+format(stats['cases'][key]['routes'][r]['costs']['full']['codeLines'],',')+'</td>' for r in ROUTES)+'</tr>' for key in TARGETS.values())
    table='<div class="numeric-scroll"><table><thead><tr><th>Conclusion</th><th>Computable FTC: declarations / mapped LOC</th><th>Mathlib: declarations / mapped LOC</th></tr></thead><tbody>'+rows+'</tbody></table></div>'
    examples=json.loads((ROOT/'comparison/reports/integral-native-examples.json').read_text())
    def decimal(q,upper=False):
        q=Q(q.replace(' ',''));scale=10**8
        k=-((-q.numerator*scale)//q.denominator) if upper else q.numerator*scale//q.denominator
        return str(k//scale)+'.'+str(k%scale).zfill(8)
    numerics=''.join('<tr><td>'+str(r['n'])+'</td><td>'+decimal(r['lower'])+'</td><td>'+decimal(r['upper'],True)+'</td></tr>' for r in examples['wallisBounds'])
    numbertable='<div class="numeric-scroll"><table><caption>Actual Lean executions of the rational Wallis bounds; decimals rounded outwards.</caption><thead><tr><th>Product index n</th><th>Lower bound on geometric pi</th><th>Upper bound</th></tr></thead><tbody>'+numerics+'</tbody></table></div>'
    (reading/'integral-native-examples.json').write_text(json.dumps(examples,indent=2)+'\n')
    doc=BeautifulSoup((ROOT/'book/chapters/integral-portfolio.html').read_text().replace('<!-- PORTFOLIO_TABLE -->',table).replace('<!-- WALLIS_BOUNDS -->',numbertable),'html.parser')
    for target in TARGETS:
        box=doc.find(id=target);aside=doc.new_tag('aside',attrs={'class':'theorem-margin'})
        a=doc.new_tag('a',href='proof-map.html?theorem='+target,attrs={'data-proof-map':target});a.string='Proof map ↗';aside.append(a)
        label=doc.new_tag('small');label.string='Checked alternative derivations';aside.append(label);box.append(aside)
    (SITE/'integral-families.html').write_text(shell('Two integral families, two foundations',str(doc),'integral-families.html','REUSABLE CALCULUS',
      'Uniformly quantified statements; two theorem families, not a parameter-count leaderboard.',sha,[(h['id'],h.get_text()) for h in doc.select('h2[id]')]))
    for file in ['index.html','cosine.html','cartwright.html','integral-families.html']:
        p=SITE/file
        if p.exists():
            text=p.read_text();needle='<a class="portfolio-navigation" href="integral-families.html">Wallis and beta integrals</a>'
            if 'class="portfolio-navigation"' not in text:text=text.replace('<span class="nav-label">The development</span>',needle+'<span class="nav-label">The development</span>',1)
            p.write_text(text)
    shutil.copyfile(ROOT/'book/assets/graph.js',reading/'graph.js')
    shutil.copyfile(ROOT/'book/assets/map-comparison.js',reading/'map-comparison.js')
    manifest=json.loads((reading/'manifest.json').read_text());manifest['theoremMaps']=len(maps['theorems']);manifest['checkedPairedMaps']=sum(t.get('checkedComparison',False) and not t.get('aliasOf') for t in maps['theorems'].values());manifest['integralPortfolio']=True
    (reading/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
    for file,h in original.items():assert hashlib.sha256((SITE/file).read_bytes()).hexdigest()==h
    print('PASS: two paired families, four theorem maps, witnessed edges, independent validity and bridges, cumulative library accounting')
    for key in TARGETS.values():print(key,{r:(v['costs']['full']['declarations'],v['costs']['full']['codeLines'],v['costs']['after-cartwright']['codeLines']) for r,v in stats['cases'][key]['routes'].items()})

if __name__=='__main__':main()
