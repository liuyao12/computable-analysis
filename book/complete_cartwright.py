#!/usr/bin/env python3
"""Replace the arithmetic-only plan with checked paired statements and real costs.
Every diagram arrow has a stored Lean-reference witness. Display selections
never become measurement roots. Existing cosine/dyadic artefacts are retained.
"""
from __future__ import annotations
from collections import defaultdict, deque
from copy import deepcopy
from pathlib import Path
import gzip, hashlib, json, shutil, sys, textwrap
import pygraphviz as pgv
from bs4 import BeautifulSoup
from build import shell
ROOT=Path(__file__).resolve().parents[1];SITE=ROOT/'blueprint/web'
sys.path.insert(0,str(ROOT/'blueprint/checks'))
from build_proof_bench import closure, source_index, source_union, origin, ORIGINS

N='ComputableAnalysis.CartwrightMoments.';A='ComputableAnalysis.CartwrightArithmetic.'
P='ComputableAnalysis.';M='MathlibComparison.Cartwright.'
EVAL='thm:cartwright-moments';FINAL='thm:cartwright-irrationality';OLD='thm:cartwright-plan'
COLORS=['#a45032','#326493','#7755a0'];ROUTES=['direct','ftc','mathlib']
MATHLIB='51e6992efd06126df61a496bebf8f49482a4e129'

BUNDLES={
 'cw:integers':('Integer recurrence and denominators','Shared finite arithmetic',[
  A+'polynomialPair',A+'polynomialValue',A+'integerPair',A+'integerValue',A+'denominator_cleared'],
  r'<p>The two finite recurrences give \(P_n\) and an integer \(K_n\). Denominator clearing proves \(K_n=b^nP_n(a/b)\), with a nonzero denominator.</p><p>This bundle has no integral, computable-number, or Mathlib-real dependency. It is literally reused in all routes.</p>'),
 'cw:geometry':('Geometric pi and circle coordinates','Fixed definitions',[
  P+'CosinePrimitive.pi',P+'CosinePrimitive.pi_compute',N+'frequency',N+'frequencySample',
  N+'frequencySample_bounds',P+'ClockTrigonometry.c',P+'ClockTrigonometry.s',P+'ClockTrigonometry.cosine',P+'ClockTrigonometry.sine'],
  r'<p>The original sector computation defines \(\pi=4A(1)\); set \(\lambda=\pi/2\). The quarter-turn coordinate functions are \(c(t)=C(t/2)\) and \(s(t)=S(t/2)\).</p><p>The rational frequency samples lie in [1,2]. No moment value or irrationality theorem is used to define these objects.</p>'),
 'cw:quadrature':('Chosen weighted-moment construction','Computations and a checked joint schedule',[
  N+'weight',N+'sample',P+'MonotoneAverage.left',P+'MonotoneAverage.gap',P+'MonotoneAverage.mesh_error',
  P+'MonotoneSampleIntegral.Data',P+'MonotoneSampleIntegral.centre',P+'MonotoneSampleIntegral.raw',
  P+'MonotoneSampleIntegral.valid',N+'data',N+'moment',N+'moment_valid',N+'moment_width',
  N+'sample_evaluation_error',N+'sample_decreases',N+'recurrence_mesh_error',N+'first_mesh_error'],
  r'<p>Compute \(J_n=\int_0^1(1-t^2)^n c(t)\,dt\) by finite dyadic samples. The chosen joint stage is mesh depth k and evaluation stage k. A uniform error proof, not pointwise convergence alone, justifies that diagonal.</p><div class="displaymath">\[\operatorname{width}((J_n)_k)\le226\,2^{-k}.\]</div><p>The program widens each sampled mean by \(113\,2^{-k}\), intersects earlier enclosures, and clips to [0,1]. Its convergence and monotonicity are proved without the moment recurrence or evaluation.</p>'),
 'cw:bounds':('Positive and bounded moments','Bounds before evaluation',[
  N+'lowerBound',N+'momentSample_lower',N+'moment_positive',N+'moment_upper'],
  r'<p>The weight and cosine samples are nonnegative and decreasing. A fixed subinterval supplies a strictly positive lower bound:</p><div class="displaymath">\[\frac1{16}(15/16)^n\le J_n\le1.\]</div><p>These bounds are independent of the recurrence and FTC. They are used only when turning the evaluated moment into inequalities on an integer.</p>'),
 'cw:local':('Finite derivative and polynomial estimates','Shared native local calculus',[
  P+'FiniteSampleCalculus.Model',P+'FiniteSampleCalculus.Model.local_error',
  N+'sineModel',N+'cosineModel',N+'weightDerivative',N+'weightModel'],
  r'<p>The supplied local certificate bounds the error in replacing a rational increment by its slope sample by \(Kh^2\), after sufficiently accurate evaluation of that fixed cell.</p><p>Finite polynomial multiplication and the geometric sine/cosine estimates supply the local data. Both native routes reuse these estimates. Sharing them does not mean that either route invokes the other’s global theorem.</p>'),
 'cw:discrete':('Discrete summation by parts','Finite route',[
  P+'FiniteSummationByParts.cellSum',P+'FiniteSummationByParts.product_identity',
  P+'FiniteSummationByParts.quadratic_accumulation',P+'FiniteSummationByParts.finite_product_estimate',
  P+'FiniteSummationByParts.two_products_close',N+'zero_viaFinite',N+'first_viaFinite',N+'recurrence_viaFinite'],
  r'<p>First sum the exact rational identity \(\Delta(fg)=f\Delta g+g\Delta f+\Delta f\Delta g\). Then bound the increment-replacement errors and the cross-increment term on a fixed finite mesh.</p><p>Two discrete product estimates yield the moment recurrence. This route does not call the general sample FTC, its telescoping theorem, or the composite-primitive certificate.</p>'),
 'cw:ftc':('Quantitative FTC and a primitive','Native FTC route',[
  P+'FiniteSampleCalculus.Model.mul',P+'FiniteSampleCalculus.finite_telescope',
  P+'FiniteSampleCalculus.chosen_samples_FTC',N+'recurrencePrimitive',N+'recurrenceDerivative',
  N+'recurrenceModel',N+'zero_viaFTC',N+'first_viaFTC',N+'recurrence_viaFTC'],
  r'<p>The reusable finite-sample FTC converts a certified local derivative estimate into agreement with an independently chosen quadrature. The product rules construct the certificate for</p><div class="displaymath">\[F_n(t)=\lambda(1-t^2)^{n+2}s(t)-2(n+2)t(1-t^2)^{n+1}c(t).\]</div><p>Its derivative is the recurrence’s linear combination of weighted cosine integrands. Endpoint estimates finish the calculation. This is a quantitative product/remainder theorem, not an unsupported assumption that the whole primitive is concave.</p>'),
 'cw:mathlib-trig':('Mathlib exponential and trigonometry','Comparison foundation',[
  'Complex.exp','Real.sin','Real.cos','Real.pi','Real.hasDerivAt_sin','Real.hasDerivAt_cos'],
  r'<p>Mathlib’s trigonometric functions and their derivative theorems are the targets of our value bridges. They do not replace the native geometric definitions or provide numerical values to the native moment program.</p>'),
 'cw:mathlib-integral':('Mathlib general and interval integrals','Comparison foundation',[
  'MeasureTheory.lintegral','MeasureTheory.integral','intervalIntegral',
  'intervalIntegral.integral_mono_on','intervalIntegral.integral_add_adjacent_intervals'],
  r'<p>The nonnegative Lebesgue construction underlies Mathlib’s general Bochner integral; the oriented interval integral restricts its measure to intervals. The quadrature bridge uses integral order and finite additivity.</p><p>These noncomputable real-analysis definitions belong only to the comparison package. No native integrability predicate is introduced.</p>'),
 'cw:mathlib-ftc':('Mathlib FTC and integration by parts','Comparison calculus',[
  'intervalIntegral.integral_eq_sub_of_hasDerivAt','intervalIntegral.integral_mul_deriv_eq_deriv_mul'],
  r'<p>Mathlib’s FTC and integration-by-parts theorem supply the analytic moment recurrence. The exact statements retain their derivative and interval-integrability hypotheses.</p>'),
 'cw:bridge':('The actual moments represent real integrals','Independent quadrature bridge',[
  'MathlibComparison.cosine_represents','MathlibComparison.piCircleArea_represents',
  M+'clock_cosine_represents', 'MathlibComparison.RealDyadicAverages.rectangle_bounds',
  'MathlibComparison.RealDyadicAverages.diagonal_tendsto',M+'moment_samples_tendsto',M+'moment_represents'],
  r'<p>Identify the native samples with the real integrand at rational inputs. Monotone upper/lower rectangles and finite additivity then identify the very same native moment program with Mathlib’s integral.</p><p>Separate mesh and sample convergence is essential. This bridge does not use the moment evaluation, its recurrence, or an irrationality theorem.</p>'),
 'cw:real-moments':('Mathlib moment recurrence','Comparison middle',[
  M+'lambda',M+'moment',M+'moment_zero',M+'moment_one',M+'moment_recurrence'],
  r'<p>Two integrations by parts and the endpoint sine/cosine values yield the recurrence for Mathlib’s moments. This is proved locally from calculus rather than obtained from the existing irrationality of π.</p>'),
 'cw:laws':('The same moment laws','One common analytic interface',[
  P+'RationalSampleLimits.Small',P+'RationalSampleLimits.Close',N+'MomentLaws',N+'MomentLaws.zero',N+'MomentLaws.first',N+'MomentLaws.recurrence',
  N+'lawsViaFinite',N+'lawsViaFTC',M+'lawsViaMathlib'],
  r'<p>The three closed proofs establish one proposition consisting of the bases and recurrence:</p><div class="displaymath">\[\lambda J_0=1,\quad\lambda^2J_1=2J_0,\quad\lambda^2J_{n+2}=2(n+2)(2n+3)J_{n+1}-4(n+2)(n+1)J_n.\]</div><p>The Lean interface expresses these laws through errors of rational samples tending to zero. Each final route supplies its proof; no unproved provider is left for the caller.</p>'),
 'cw:polynomial-values':('Polynomial evaluation on computed numbers','Statement objects',[
  N+'polynomialRawPair',N+'polynomialRawPair_mem',N+'polynomialEndpoint'],
  r'<p>Evaluate the same finite polynomial recurrence by interval arithmetic at \(\lambda^2\). Its sample-membership theorem connects this interval program to the rational polynomial recurrence.</p><p>This is the right-hand-side computation, not a definition of the moment integral.</p>'),
 EVAL:('Weighted cosine evaluation','One evaluated identity',[
  N+'scaledMoment',N+'EvaluationStatement',N+'evaluation_close',N+'evaluation_of_laws',
  N+'evaluation_viaFinite',N+'evaluation_viaFTC',N+'evaluation_viaMathlib'],
  r'<p>Scale the common moment laws and apply a finite recurrence induction:</p><div class="displaymath">\[\boxed{\lambda^{2n+1}J_n\simeq2^nn!P_n(\lambda^2).}\]</div><p>The three named derivations have definitionally identical complete types, uniformly in n. A single shared algebraic proof consumes the analytic laws.</p>'),
 'cw:transfer':('Bounds on the integer recurrence','From analysis back to arithmetic',[
  N+'integer_close',N+'integer_bounds',N+'frequency_not_rational_close'],
  r'<p>Under the hypothetical \(\lambda^2=a/b\), clear denominators in the evaluation and use the independent moment bounds. The result passed to the arithmetic consumer is exactly</p><div class="displaymath">\[0&lt;K_n,\qquad K_n2^nn!\le2a^n.\]</div><p>This generic consumer is shared by all routes. Its complete applications still depend on whichever calculus proof supplied the moment laws.</p>'),
 'cw:factorial':('An explicit factorial bound','Pure finite arithmetic',[
  A+'factorial_tail_lower',A+'witnessIndex',A+'factorial_dominates'],
  r'<p>Choose \(N=2a^2\). Bounding the last block of factorial factors proves</p><div class="displaymath">\[2a^N&lt;2^NN!.\]</div><p>This is a finite inequality with a supplied index, not a theorem about asymptotic growth.</p>'),
 'cw:obstruction':('No positive integer can be that small','Pure finite arithmetic',[
  A+'integer_obstruction',A+'no_positive_small_sequence'],
  r'<p>A positive integer is at least one. The factorial inequality therefore contradicts \(K_N2^NN!\le2a^N\).</p><p>The actual declaration closure of this lemma contains no integrals, computable numbers, geometric π or Mathlib. Only the integer inequalities are its input.</p>'),
 FINAL:('Geometric pi squared is irrational','Complete arithmetic application',[
  P+'RealRaw.Irrational',N+'PiSquaredStatement',N+'piSquared_of_laws',N+'piSquared_viaFinite',N+'piSquared_viaFTC',N+'piSquared_viaMathlib'],
  r'<p>No rational constant program is equivalent to the square of the original geometric π computation:</p><div class="displaymath">\[\boxed{\forall r\in\mathbb Q,\quad\pi^2\not\simeq r.}\]</div><p>Each named proof is closed, has the same exact type, and uses the shared integer contradiction. The Mathlib route uses its own calculus, not an existing irrationality theorem. The native routes are Mathlib-free.</p>')}

def witness(nodes,start,goal,mode='proof'):
    prev={start:None};q=deque([start])
    while q:
        x=q.popleft()
        if x==goal:
            path=[]
            while x is not None:path.append(x);x=prev[x]
            return path
        d=nodes[x]
        if mode=='definitions' and d['kind'] not in ('def','definition','opaque'):continue
        fields=['bodyRefs'] if mode=='definitions' or (mode=='proof' and x==start) else ['typeRefs','bodyRefs']
        for y in sorted({y for k in fields for y in d[k]}):
            if y not in prev:prev[y]=x;q.append(y)
    return None

def comparison(raw,nodes,sha):
    records,cache,sourceHashes=source_index(nodes)
    def cost(ss):
        t=source_union(ss,records,cache)
        return dict(declarations=len(ss),codeLines=t['nonblankCodeLines'],mappedDeclarations=t['mappedDeclarations'],
            unmappedDeclarations=t['unmappedDeclarations'],bodyDag=sum(nodes[n]['bodyDag'] for n in ss),
            bodyTree=sum(nodes[n]['bodyTree'] for n in ss))
    arithmetic=closure(nodes,raw['arithmetic']);prior={r:closure(nodes,[name])|arithmetic for r,name in zip(ROUTES,raw['cosineBaselines'])}
    cases={}
    for caseId in ['laws','moments','irrationality']:
        roots={r['route']:r for r in raw['roots'] if r['case']==caseId}
        ss={r:closure(nodes,[roots[r]['root']]) for r in ROUTES}
        shared=set.intersection(*ss.values());statement=set().union(*(closure(nodes,nodes[roots[r]['root']]['typeRefs']) for r in ROUTES))
        rows={}
        for r in ROUTES:
            costs={}
            for b,s in [('full',ss[r]),('statement-free',ss[r]-statement),('shared-free',ss[r]-shared),('after-cosine',ss[r]-prior[r])]:
                c=cost(s);c['origins']={o:cost({n for n in s if origin(nodes[n]['module'])==o}) for o in ORIGINS}
                assert sum(v['declarations'] for v in c['origins'].values())==c['declarations']
                assert sum(v['codeLines'] for v in c['origins'].values())==c['codeLines']
                costs[b]=c
            rows[r]=dict(roots=[roots[r]['root']],costs=costs,finalApplication=cost({roots[r]['root']}),axioms=roots[r]['axioms'])
        cases[caseId]=dict(title=caseId,routes=rows,baselines=dict(statementDeclarations=len(statement),sharedDeclarations=len(shared)))
    # Exact union across the two main obligations; do not charge shared terms twice.
    unions={r:cost(closure(nodes,[next(x['root'] for x in raw['roots'] if x['case']==c and x['route']==r) for c in ['moments','irrationality']])) for r in ROUTES}
    return dict(schemaVersion=2,sourceCommit=sha,routeOrder=ROUTES,cases=cases,
        routeLabels=dict(direct='Finite summation by parts',ftc='Quantitative FTC',mathlib='Mathlib + bridges'),
        caseOptions=[['laws','Analytic middle: moment laws'],['moments','Uniform moment evaluation'],['irrationality','Complete irrationality proof']],
        baselineOptions=[['full','Full used library'],['statement-free','Beyond statement prerequisites'],['shared-free','Beyond shared prerequisites'],['after-cosine','Additional after cosine + arithmetic']],
        baselineDescriptions=dict(full='All transitive type/body dependencies, including existing foundations.',
            **{'statement-free':'The union of statement prerequisite closures is available first.',
            'shared-free':'The intersection shared by the three alternatives is available first.',
            'after-cosine':'For each route, its matching preceding cosine proof and the common arithmetic are already available. These are route-specific prior-library baselines, not identical baselines.'}),
        arithmetic=cost(arithmetic),priorLibrary={r:cost(s) for r,s in prior.items()},combined=unions,
        codeLineLabel='Mapped source LOC',sourceAvailability=sourceHashes,
        method='Stored type/body closures; source-range unions exclude comments and blanks, with explicit coverage; display nodes do not become measurement roots.')

def main():
    reading=SITE/'reading';maps=json.loads((reading/'maps.json').read_text());sha=maps['sourceCommit']
    raw=json.loads((ROOT/'comparison/reports/cartwright-complete.json').read_text());assert all(raw['checks'].values())
    nodes={n['id']:n for n in raw['nodes']};decs={d['name']:d for d in raw['declarations']}
    old={str(p.relative_to(SITE)):hashlib.sha256(p.read_bytes()).hexdigest() for p in [SITE/'proof-bench/data.json',reading/'map-comparison.json',*reading.glob('cosine-*.svg'),reading/'dyadic-product.svg']}
    stats=comparison(raw,nodes,sha)
    for key,(title,role,names,math) in BUNDLES.items():
        cards=[]
        for name in names:
            d=deepcopy(decs[name]);d['realDependencyPath']=witness(nodes,name,'Real','all') or []
            mod=d['ownerModule'];prefix=f'https://github.com/liuyao12/computable-analysis/blob/{sha}/'
            if mod.startswith('MathlibComparison'):prefix+='comparison/'
            elif mod.startswith('Mathlib.'):prefix=f'https://github.com/leanprover-community/mathlib4/blob/{MATHLIB}/'
            span=d['sourceRange'];d['sourceUrl']=prefix+mod.replace('.','/')+'.lean'+(f"#L{span['start']}-L{span['end']}" if span else '')
            cards.append(d)
        kinds=[bool(d['realDependencyPath']) for d in cards]
        cls='mixed' if any(kinds) and not all(kinds) else 'mathlib' if any(kinds) else 'native'
        maps['bundles'][key]=dict(title=title,anchors=names,groups=[dict(title='Exact definitions and statements',names=names)],declarations=cards,
            classification=cls,proofStatus='checked',mathHtml=math,strategy=dict(role=role,summary='',groups={}))
    # Every proposed arrow is checked against actual declarations before drawing.
    edges=[]
    def edge(s,t,start,goal,route=None,kind='proof',label=None):
        mode='definitions' if kind=='statement' else 'proof' if kind=='proof' else 'all'
        p=witness(nodes,start,goal,mode);assert p,(s,t,start,goal,mode)
        assert start in BUNDLES[t][2] and goal in BUNDLES[s][2],(s,t,start,goal)
        edges.append(dict(source=s,target=t,kind=kind,route=route,globalEdge=route is None,witness=p,
          label=label or ('Definition used by the statement' if kind=='statement' else 'Shared proof step' if route is None else stats['routeLabels'][ROUTES[route]])))
    edge('cw:geometry','cw:quadrature',N+'moment',P+'ClockTrigonometry.c',None,'construction')
    edge('cw:quadrature','cw:bounds',N+'moment_positive',N+'moment_valid')
    edge('cw:geometry','cw:local',N+'sineModel',N+'frequencySample',None,'construction')
    edge('cw:local','cw:discrete',N+'recurrence_viaFinite',N+'sineModel',0)
    edge('cw:local','cw:ftc',N+'recurrenceModel',N+'sineModel',1)
    edge('cw:quadrature','cw:discrete',N+'recurrence_viaFinite',N+'recurrence_mesh_error',0)
    edge('cw:quadrature','cw:ftc',N+'recurrence_viaFTC',N+'recurrence_mesh_error',1)
    edge('cw:quadrature','cw:bridge',M+'moment_represents',N+'moment_valid',2)
    edge('cw:geometry','cw:bridge',M+'clock_cosine_represents',P+'ClockTrigonometry.cosine',2)
    edge('cw:mathlib-trig','cw:bridge',M+'clock_cosine_represents','Real.cos',2)
    edge('cw:mathlib-integral','cw:bridge','MathlibComparison.RealDyadicAverages.rectangle_bounds','intervalIntegral.integral_mono_on',2)
    edge('cw:mathlib-integral','cw:mathlib-ftc','intervalIntegral.integral_mul_deriv_eq_deriv_mul','intervalIntegral',2,'construction')
    edge('cw:mathlib-ftc','cw:real-moments',M+'moment_recurrence','intervalIntegral.integral_mul_deriv_eq_deriv_mul',2)
    edge('cw:mathlib-trig','cw:real-moments',M+'moment_recurrence','Real.hasDerivAt_sin',2)
    edge('cw:bridge','cw:laws',M+'lawsViaMathlib',M+'moment_samples_tendsto',2)
    edge('cw:real-moments','cw:laws',M+'lawsViaMathlib',M+'moment_recurrence',2)
    edge('cw:discrete','cw:laws',N+'lawsViaFinite',N+'recurrence_viaFinite',0)
    edge('cw:ftc','cw:laws',N+'lawsViaFTC',N+'recurrence_viaFTC',1)
    for i,suffix in enumerate(['Finite','FTC','Mathlib']):
        edge('cw:laws',EVAL,N+'evaluation_via'+suffix,(M+'lawsViaMathlib') if i==2 else N+'lawsVia'+suffix,i)
    edge('cw:integers',EVAL,N+'evaluation_close',A+'polynomialPair')
    edge('cw:polynomial-values',EVAL,N+'EvaluationStatement',N+'polynomialEndpoint',None,'statement')
    edge('cw:quadrature',EVAL,N+'EvaluationStatement',N+'moment',None,'statement')
    edge('cw:geometry',EVAL,N+'EvaluationStatement',N+'frequency',None,'statement')
    edge(EVAL,'cw:transfer',N+'integer_close',N+'evaluation_close')
    edge('cw:integers','cw:transfer',N+'integer_close',A+'denominator_cleared')
    edge('cw:bounds','cw:transfer',N+'integer_bounds',N+'momentSample_lower')
    edge('cw:factorial','cw:obstruction',A+'integer_obstruction',A+'factorial_dominates')
    for i,suffix in enumerate(['Finite','FTC','Mathlib']):
        edge('cw:transfer',FINAL,N+'piSquared_via'+suffix,N+'integer_bounds',i)
        edge('cw:obstruction',FINAL,N+'piSquared_via'+suffix,A+'no_positive_small_sequence',i)
    edge('cw:geometry',FINAL,N+'PiSquaredStatement',P+'CosinePrimitive.pi',None,'statement')
    # Main graph and the smaller moment graph use the same verified bundle edges.
    full=set(BUNDLES);moment=full-{'cw:bounds','cw:transfer','cw:factorial','cw:obstruction',FINAL}
    graphs={};graphReports={}
    for target,ids in [(EVAL,moment),(FINAL,full)]:
        views={}
        for view in ['all','0','1','2']:
            active=[e for e in edges if e['source'] in ids and e['target'] in ids and (view=='all' or e['route'] is None or str(e['route'])==view)]
            visible=set(ids)
            if view in ['0','1']:visible-={'cw:mathlib-trig','cw:mathlib-integral','cw:mathlib-ftc','cw:bridge','cw:real-moments'}
            if view=='0':visible.discard('cw:ftc')
            if view=='1':visible.discard('cw:discrete')
            if view=='2':visible-={'cw:local','cw:discrete','cw:ftc'}
            active=[e for e in active if e['source'] in visible and e['target'] in visible]
            g=pgv.AGraph(strict=True,directed=True,rankdir='TB',bgcolor='transparent',nodesep='.32',ranksep='.58',splines='spline')
            g.node_attr.update(shape='box',style='rounded,filled',fontname='Helvetica',fontsize='12',margin='.16,.12',color='#879a8c')
            g.edge_attr.update(arrowhead='vee',arrowsize='.65')
            for key in sorted(visible):
                cls=maps['bundles'][key]['classification'];fill='#eef3ed' if cls=='native' else '#f0eafa'
                if cls=='mixed':fill='#eef3ed:#f0eafa' if view=='all' else '#f0eafa' if view=='2' else '#eef3ed'
                g.add_node(key,label='\n'.join(textwrap.wrap(BUNDLES[key][0],26)),fillcolor=fill,penwidth='2.1' if key==target else '1.1')
            grouped=defaultdict(list)
            for e in active:grouped[e['source'],e['target']].append(e)
            for (s,t),es in grouped.items():
                kind='statement' if any(e['kind']=='statement' for e in es) else 'proof' if any(e['kind']=='proof' for e in es) else 'construction'
                rs=sorted({e['route'] for e in es if e['route'] is not None})
                # Shared proof steps are used by all alternatives; color follows
                # the active route, with muted green for a common all-route step.
                col=(':'.join(COLORS[i] for i in rs) if rs else '#54725b') if kind=='proof' else '#202020'
                if kind=='proof' and not rs and view!='all':col=COLORS[int(view)]
                g.add_edge(s,t,color=col,style='solid',penwidth='1.6' if kind=='proof' else '1.1')
            g.add_subgraph([k for k in ['cw:integers','cw:geometry','cw:mathlib-trig','cw:mathlib-integral'] if k in visible],rank='min')
            g.add_subgraph([target],rank='max')
            deg={str(n):g.in_degree(n) for n in g.nodes()};q=[n for n,v in deg.items() if not v];seen=0
            while q:
                n=q.pop();seen+=1
                for child in g.successors(n):
                    child=str(child);deg[child]-=1
                    if not deg[child]:q.append(child)
            assert seen==len(visible) and not list(g.successors(target))
            g.layout('dot');svg=BeautifulSoup(g.draw(format='svg').decode(),'html.parser').svg
            for k in ['width','height']:svg.attrs.pop(k,None)
            for n in svg.select('g.node'):
                k=n.title.get_text();n['data-node']=k;n['tabindex']='0';n['role']='button';n['aria-label']=BUNDLES[k][0]
            for e in svg.select('g.edge'):
                s,t=e.title.get_text().split('->');es=grouped[s,t]
                e['data-edge']=s+'->'+t;e['data-edge-kind']='statement' if any(x['kind']=='statement' for x in es) else 'proof' if any(x['kind']=='proof' for x in es) else 'construction'
                e['tabindex']='0';e['role']='button'
            filename=f'reading/cartwright-{target.split(":")[1]}-{view}.svg';(SITE/filename).write_text(str(svg));views[view]=filename
            graphReports[target+'/'+view]=dict(nodes=len(visible),edges=len(grouped))
        entry=dict(id=target,title=BUNDLES[target][0],sink=target,checkedComparison=True,verifiedGraph=True,
            status='Checked complete statements · finite / FTC / Mathlib · shared arithmetic',page='cartwright.html',views=views,
            routeNames=list(stats['routeLabels'].values()),comparison=dict(url='reading/cartwright-comparison.json',defaultCase='moments' if target==EVAL else 'irrationality'))
        maps['theorems'][target]=entry;graphs[target]=entry
        maps['witnesses']=[e for e in maps['witnesses'] if e.get('map')!=target]+[dict(e,map=target) for e in edges if e['source'] in ids and e['target'] in ids]
    # An earlier plan bookmark opens the now-completed application.
    maps['theorems'][OLD]=dict(graphs[FINAL],aliasOf=FINAL)
    maps['witnesses']=[e for e in maps['witnesses'] if e.get('map')!=OLD]
    maps.pop('cartwrightPlan',None)
    report=dict(sourceCommit=sha,status='complete',momentIdentityProved=True,finalIrrationalityProved=True,
        checkedProofs=raw['roots'],checks=raw['checks'],views=graphReports,unchangedArtifacts=old,
        comparison='reading/cartwright-comparison.json',nativeSchedule='mesh k, evaluation k; width <= 226/2^k')
    maps['cartwrightComplete']=report
    (reading/'maps.json').write_text(json.dumps(maps,separators=(',',':')))
    (reading/'cartwright-audit.json').write_text(json.dumps(report,indent=2)+'\n')
    (reading/'cartwright-comparison.json').write_text(json.dumps(stats,indent=2)+'\n')
    with gzip.open(reading/'cartwright-complete.json.gz','wt') as f:json.dump(raw,f,separators=(',',':'))
    # Replace the previous plan JSON with an honest completed status as well.
    (reading/'cartwright-plan.json').write_text(json.dumps(report,indent=2)+'\n')
    rows=''.join('<tr><th>'+stats['routeLabels'][r]+'</th><td>'+format(stats['cases']['moments']['routes'][r]['costs']['full']['declarations'],',')+'</td><td>'+format(stats['cases']['moments']['routes'][r]['costs']['full']['codeLines'],',')+'</td><td>'+format(stats['cases']['irrationality']['routes'][r]['costs']['full']['declarations'],',')+'</td><td>'+format(stats['cases']['irrationality']['routes'][r]['costs']['full']['codeLines'],',')+'</td></tr>' for r in ROUTES)
    table='<div class="numeric-scroll"><table><thead><tr><th>Route</th><th>Moment declarations</th><th>Moment mapped LOC</th><th>Full declarations</th><th>Full mapped LOC</th></tr></thead><tbody>'+rows+'</tbody></table></div>'
    page=BeautifulSoup((ROOT/'book/chapters/cartwright-complete.html').read_text().replace('<!-- CARTWRIGHT_COMPARISON -->',table),'html.parser')
    for target in [EVAL,FINAL]:
        box=page.find(id=target);aside=page.new_tag('aside',attrs={'class':'theorem-margin'});a=page.new_tag('a',href='proof-map.html?theorem='+target,attrs={'data-proof-map':target});a.string='Proof map ↗';aside.append(a);note=page.new_tag('small');note.string='Checked alternative derivations';aside.append(note);box.append(aside)
    (SITE/'cartwright.html').write_text(shell('Arithmetic with calculus in the middle',str(page),'cartwright.html','CHECKED ARITHMETIC APPLICATION','One moment family; shared arithmetic; alternative calculus routes.',sha,[(h['id'],h.get_text()) for h in page.select('h2[id]')]))
    # The generic comparison widget now accepts per-theorem datasets.
    shutil.copyfile(ROOT/'book/assets/map-comparison.js',reading/'map-comparison.js')
    shutil.copyfile(ROOT/'book/assets/graph.js',reading/'graph.js')
    manifest=json.loads((reading/'manifest.json').read_text());manifest['theoremMaps']=len(maps['theorems']);manifest['checkedPairedMaps']=sum(t.get('checkedComparison',False) and not t.get('aliasOf') for t in maps['theorems'].values());manifest['partlyFormalizedPlans']=0;manifest['cartwrightComplete']=True
    (reading/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
    for path,h in old.items():assert hashlib.sha256((SITE/path).read_bytes()).hexdigest()==h
    print('PASS: complete moment and irrationality statements, real reference paths, paired measurements and preserved earlier examples')
    for case in stats['cases']:
        print(case,{r:(v['costs']['full']['declarations'],v['costs']['full']['codeLines'],v['costs']['after-cosine']['declarations'],v['costs']['after-cosine']['codeLines']) for r,v in stats['cases'][case]['routes'].items()})
if __name__=='__main__':main()
