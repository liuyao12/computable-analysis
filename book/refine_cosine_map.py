#!/usr/bin/env python3
"""Refine the existing proof map using stored proof references, not a new theorem.

A generic supplied-schedule lemma is displayed inside the construction panel.
It is NOT added as a premise of the original proofs, which use their existing
retained-mesh program. Validity is a separate object with route-specific uses.
"""
from pathlib import Path
from copy import deepcopy
from collections import Counter, deque, defaultdict
import hashlib, json
from bs4 import BeautifulSoup
import pygraphviz as pgv

ROOT=Path(__file__).resolve().parents[1]
P='ComputableAnalysis.'; M='MathlibComparison.'
TARGET='thm:c3-primitive'; VALID='lem:c3-construction-valid'; END='lem:c3-endpoint-representation'
COLORS=['#a45032','#326493','#7755a0']
SCHEDULE=P+'Integral.ScheduledBounds.'
ROOTS=[P+'CosinePrimitive.viaInequalities',P+'CosinePrimitive.viaFTC',P+'CosinePrimitive.viaMathlib']
VALIDS=[P+'CosinePrimitive.integral_valid_viaInequalities',P+'CosinePrimitive.integral_valid_viaFTC',P+'CosinePrimitive.integral_valid_viaMathlib']


def path(nodes,start,goal,mode='references'):
    previous={start:None};todo=deque([start])
    while todo:
        n=todo.popleft()
        if n==goal:
            out=[]
            while n is not None:out.append(n);n=previous[n]
            return out
        d=nodes[n]
        if mode=='definitions' and d['kind'] not in ('def','definition','opaque'):continue
        keys=['bodyRefs'] if mode=='definitions' or (mode=='proof' and n==start) else ['bodyRefs','typeRefs']
        for dep in sorted({x for k in keys for x in d[k]}):
            if dep not in previous:previous[dep]=n;todo.append(dep)
    return None


def main():
    site=ROOT/'blueprint/web';reading=site/'reading'
    data=json.loads((reading/'maps.json').read_text());details=data['bundles'];sha=data['sourceCommit']
    raw=json.loads((ROOT/'comparison/reports/proof-bench-raw.json').read_text())
    extra=json.loads((ROOT/'comparison/reports/schedule-map.json').read_text())
    assert all(extra['checks'].values()) and all(raw['checks'].values())
    nodes={n['id']:n for n in raw['nodes']}
    for n in extra['nodes']:
        if n['id'] in nodes:
            old=nodes[n['id']]
            assert set(old['typeRefs'])==set(n['typeRefs']) and set(old['bodyRefs'])==set(n['bodyRefs'])
        else:nodes[n['id']]=n
    cards={d['name']:deepcopy(d) for b in details.values() for d in b['declarations']}
    before=Counter((d['name'],d['type'],str(d.get('value'))) for b in details.values() for d in b['declarations'])
    for d0 in extra['declarations']:
        d=deepcopy(d0);d['realDependencyPath']=path(nodes,d['name'],'Real') or []
        d['sourceUrl']=f'https://github.com/liuyao12/computable-analysis/blob/{sha}/'+('comparison/' if d['ownerModule'].startswith('MathlibComparison') else '')+d['ownerModule'].replace('.','/')+'.lean'
        if d['name'] not in cards:cards[d['name']]=d
    def add_group(bundle,title,names):
        bundle['groups'].append(dict(title=title,names=names))
        bundle['declarations'] += [deepcopy(cards[n]) for n in names]
        bundle['declarationCount']=len(bundle['declarations'])
    def new_bundle(label,title,groups,math,role,classification='native'):
        b=dict(title=title,anchors=[],paths={},groups=[],declarations=[],classification=classification,
               mathHtml=math,strategy=dict(role=role,summary='',groups={}))
        for heading,names in groups:
            add_group(b,heading,names);b['anchors']+=names
        b['paths']={n:cards[n].get('realDependencyPath',[]) for n in b['anchors']}
        details[label]=b;return b

    target=details[TARGET];target['title']='Cosine primitive'
    validity_cards=[d for d in target['declarations'] if d['name'] in VALIDS]
    assert len(validity_cards)==3
    target['groups']=[dict(title=('Alternative derivations' if 'proofs' in g['title'].lower() else g['title']),
                           names=[n for n in g['names'] if n not in VALIDS]) for g in target['groups']]
    target['groups']=[g for g in target['groups'] if g['names']]
    target['declarations']=[d for d in target['declarations'] if d['name'] not in VALIDS]
    target['declarationCount']=len(target['declarations'])
    target['strategy']=dict(role='Equality of independently defined computations',summary=
        'The statement is RealRaw.Equiv, with the same rational endpoint t and the same two programs in every route. '
        'Validity of the chosen integral construction has its own node. No integrability predicate is introduced.',groups={})
    target['mathHtml']=r'''<p>For a rational \(0\le t\le\tfrac12\), the chosen cosine integral computation and the independently evaluated sine endpoint agree:</p>
<div class="displaymath">\[\boxed{I_C(t)\simeq S(t)/\pi.}\]</div>
<p>Here \(\pi=4A(1)\). The left side is a particular supplied finite-sum program, not a definition by its proposed primitive. Its validity certificate is shown separately.</p>
<p>The direct and concave-FTC derivations explicitly use their corresponding validity proofs when transporting equivalences. The Mathlib derivation concludes overlap from two representations of the same real; it also supplies a separate validity proof, but that proof is not a premise of the final overlap term.</p>'''
    construction=details['def:c3-integrals'];construction['title']='Integral construction'
    construction['mathHtml']=r'''<p>A monotone function on rational inputs returns computable numbers, not exact rational samples. Write its stage-m enclosure as \(F(x,m)=[f_m^-(x),f_m^+(x)]\).</p>
<p>There are two independent finite choices: subdivision level n and evaluation stage m. For an increasing function, with \(N=2^n\), \(h=(b-a)/N\) and \(x_j=a+jh\), form</p>
<div class="displaymath">\[B_{n,m}=\left[h\sum_{j=0}^{N-1}f_m^-(x_j),\quad h\sum_{j=1}^{N}f_m^+(x_j)\right].\]</div>
<p>For a decreasing function, exchange left and right endpoints. Monotonicity controls subdivision error; the widths of the computed samples are a separate contribution.</p>
<p><strong>Supply a joint stage schedule</strong> \(\sigma(k)=(n(k),m(k))\) for this evaluator and interval. Prove that its selected bounds are compatible and shrink. Strictly increasing indices alone are not that proof. Nest the outputs, if needed, by</p>
<div class="displaymath">\[I_k^{\sigma}=\bigcap_{r\le k}B_{n(r),m(r)}.\]</div>
<p><strong>Schedule independence:</strong> any two successful constructions agree when their bounds are cross-compatible for the same integrand. The checked generic lemma below retains that compatibility hypothesis; validity of unrelated programs is not sufficient.</p>
<p>The object is a supplied computation with a certificate. We do not first define an integrability predicate, quantify over all functions, or extract a schedule through choice.</p>'''
    construction['formalizationBoundary']=(
        'The supplied-schedule definitions and their certificate-to-validity and cross-compatibility-to-equivalence lemmas are now checked. '
        'They do not automatically supply monotonicity, a successful schedule, or compatibility for a new integrand. '
        'The original cosine proofs still use the retained-mesh construction shown in the adjacent cosine node; '
        'the generic schedule lemmas are displayed as foundational context, not asserted to be dependencies of those original proof terms.')
    construction['strategy']=dict(role='A chosen plan, then a proof that it works',summary=
        'The choice is computational data. Convergence certifies that choice; equivalence identifies other certified choices. '
        'The GIF illustrates monotone endpoint bounds, whereas the displayed cosine theorem uses its explicitly widened sums.',groups={})
    old_groups=deepcopy(construction['groups']);old_cards=deepcopy(construction['declarations'])
    construction['groups']=[];construction['declarations']=[]
    for title,names in [
        ('Supplied subdivision and evaluation stages',['JointSchedule','JointSchedule.meshStage','JointSchedule.evaluationStage','selected','raw']),
        ('Certificate for this choice',['Certificate','Certificate.compatible','Certificate.shrinking','valid']),
        ('Independence of successful choices',['equivalent'])]:
        add_group(construction,title,[SCHEDULE+n for n in names])
    construction['groups']+=old_groups;construction['declarations']+=old_cards
    construction['declarationCount']=len(construction['declarations'])
    cosine=details['def:c3-integral'];cosine['title']='Chosen cosine construction'
    cosine['mathHtml']=r'''<p>This is the specific computation used by all the displayed endpoint proofs, on \([0,t]\). For fixed mesh index r, let \(R_{r,q}\) be its \(r+1\) left cosine rectangles evaluated at stage q. The prescribed output is</p>
<div class="displaymath">\[I_C(t)_k=\bigcap_{r=0}^{k}\operatorname{expand}\left(R_{r,k},\frac{4000t^2}{r+1}\right).\]</div>
<p><strong>This is a finite retained-mesh schedule</strong>: at output k, evaluate all meshes r≤k at precision k. It is not the bare diagonal \(B_{k,k}\), nor an unspecified tolerance search. The definition contains neither a primitive value nor a convergence oracle.</p>
<p>For each fixed mesh its finite sample widths shrink. The rational discretization allowance shrinks with the mesh. A fixed sufficiently fine mesh can therefore be reevaluated until its bounds are narrow, while all newer meshes remain additional constraints. The separate convergence node shows the compatibility evidence used by each route.</p>
<p>The simpler single-pair schedule interface is available in the integral-construction panel. This map does not silently replace the existing numerical program by a new diagonal evaluator.</p>'''
    cosine['strategy']['role']='Two finite indices, with an explicit joint plan'
    cosine['strategy']['summary']='Fixed-mesh sample validity and mesh-error shrinkage are separate checked inputs. All routes use this same retained-mesh algorithm.'
    new_bundle(VALID,'Convergence of the chosen construction',[
        ('Direct finite bounds',[VALIDS[0]]),('Concave FTC',[VALIDS[1]]),('Mathlib comparison',[VALIDS[2]])],r'''
<p>These declarations each prove that the SAME chosen integral program has ordered, nested rational boxes whose widths tend to zero. They certify an explicit construction, not an existential integrability predicate.</p>
<p><strong>Direct:</strong> finite geometric bounds supply all-stage compatibility with a valid endpoint computation. Fixed-mesh sample convergence and a shrinking mesh allowance then give validity.</p>
<p><strong>Concave FTC:</strong> supporting-secant data and the general finite FTC estimates supply the corresponding compatibility and validity.</p>
<p><strong>Mathlib:</strong> the independent quadrature bridge puts the real integral in every widened mesh enclosure; the endpoint bridge identifies a valid anchor. This provides a separate validity theorem.</p>
<p>The native endpoint proofs invoke their validity lemmas. The Mathlib endpoint proof only invokes the representation-to-overlap theorem, so there is deliberately NO Mathlib proof arrow from this node to the conclusion. Its validity result is nonetheless checked and available here.</p>''','The supplied construction actually converges','mixed')
    new_bundle(END,'Endpoint representation',[
        ('The endpoint represents the same integral',[M+'primitive_endpoint_represents']),
        ('Two representations give native overlap',[M+'equiv_of_represents'])],r'''
<p>Combine the sine and reciprocal-pi value bridges with Mathlib's primitive identity. The independently computed native endpoint \(S(t)/\pi\) then represents the same Mathlib real integral as the quadrature program.</p>
<p>The final transport is an inequality between rational endpoints: a real contained in both output boxes forces those boxes to overlap. This yields the original native proposition, not merely an equality between Mathlib reals.</p>
<p>This step is separate from identifying the quadrature with the integral. In particular the quadrature bridge does not use the primitive identity.</p>''','Mathlib proof: identify the other side','mathlib')
    details['lem:c3-quadrature']['mathHtml']+=r'''<p>The primitive formula is not a premise of this correspondence. Continuity and the cellwise error estimate \(4t^2/m\) are enough to put the integral in each widened mesh box.</p>'''
    add_group(details['lem:c3-quadrature'],'The closed chosen integral',[M+'primitive_integral_represents'])
    details['lem:c3-direct']['mathHtml']+=r'''<p>One finite overlap estimate serves two purposes: it certifies compatibility of the chosen integral construction and identifies its endpoint value. This does not use the final cosine-primitive theorem as an assumption.</p>'''
    add_group(details['lem:c3-direct'],'The zero endpoint, proved from the clock',[P+'CosinePrimitive.S_zero'])
    entry=data['theorems'][TARGET];entry['title']='Cosine primitive'
    entry['status']='Checked alternative derivations · chosen construction and its convergence shown separately'
    entry['routeNames']=['Direct inequalities','Concave FTC','Mathlib comparison']

    edges=[deepcopy(e) for e in data['witnesses'] if not e.get('map')]
    # The Mathlib primitive is used through an endpoint representation, not as
    # an unexplained direct conversion of native expressions to real ones.
    edges=[e for e in edges if not(e['source']=='lem:c3-mftc' and e['target']==TARGET)]
    additions=[]
    def edge(source,target,start,goal,route,kind='proof',note=None):
        witness=path(nodes,start,goal,'proof' if kind=='proof' else 'references')
        assert witness,(source,target,start,goal)
        rec=dict(source=source,target=target,witness=witness,kind=kind,route=route)
        if note:rec['note']=note
        additions.append(rec);edges.append(rec)
    for i in range(3):
        edge('def:c3-integral',VALID,VALIDS[i],P+'CosineFTC.error_shrinks',i)
        edge('def:c3-integrals',VALID,VALIDS[i],P+'Integral.Dovetail.raw_valid',i)
    edge('lem:c3-direct',VALID,VALIDS[0],P+'CosineFTC.fixedMesh_overlaps_endpoint',0)
    edge('lem:c3-concavity',VALID,VALIDS[1],P+'GeometricSineConcavity.primitiveDerivativeData',1)
    edge('thm:c3-ftc',VALID,VALIDS[1],P+'ConcaveFTC.integral_valid',1)
    edge('lem:c3-quadrature',VALID,VALIDS[2],M+'fixedMesh_contains_integral',2)
    edge(END,VALID,VALIDS[2],M+'primitive_endpoint_represents',2)
    for i in [0,1]:edge(VALID,TARGET,ROOTS[i],VALIDS[i],i)
    assert path(nodes,ROOTS[2],VALIDS[2]) is None
    edge('lem:c3-values',END,M+'primitive_endpoint_represents',M+'sine_represents',2)
    edge('lem:c3-mftc',END,M+'primitive_endpoint_represents',M+'mathlib_cosine_primitive',2)
    edge('def:c3-real',END,M+'equiv_of_represents',M+'Represents',2)
    edge(END,TARGET,ROOTS[2],M+'primitive_endpoint_represents',2)
    edge('def:c3-integral','lem:c3-quadrature',M+'cosine_integral_represents',P+'CosineFTC.fixedMesh',2)
    edge('def:c3-mexp','lem:c3-values',M+'sine_represents','Real.sin',2)
    # No use of the NEW generic schedule theorem is falsely attributed to old proofs.
    for root in ROOTS:
        assert path(nodes,root,SCHEDULE+'valid') is None
        assert path(nodes,root,SCHEDULE+'equivalent') is None
    data['witnesses']=edges+[e for e in data['witnesses'] if e.get('map')]
    views=entry['views'];report_views={}
    for view,file in views.items():
        old=BeautifulSoup((site/file).read_text(),'html.parser')
        ids={n['data-node'] for n in old.select('[data-node]')}|{VALID}
        if view in ('all','companions','2'):ids.add(END)
        graph=pgv.AGraph(strict=True,directed=True,rankdir='TB',bgcolor='transparent',
                        splines='spline',nodesep='.36',ranksep='.54',outputorder='edgesfirst')
        graph.node_attr.update(shape='box',style='rounded,filled',fontname='Helvetica',fontsize='12',margin='.15,.12',color='#879a8c',fontcolor='#27382f')
        graph.edge_attr.update(arrowhead='vee',arrowsize='.65')
        for key in sorted(ids):
            b=details[key];c=b['classification']
            fill='#eef3ed' if c=='native' else '#f0eafa'
            if c=='mixed':fill='#eef3ed' if view in ('0','1') else '#f0eafa' if view=='2' else '#eef3ed:#f0eafa'
            graph.add_node(key,label=b['title'],fillcolor=fill)
        graph.get_node(TARGET).attr.update(penwidth='2.2',color='#355d49')
        graph.add_subgraph(['def:c3-rationals'],rank='min')
        graph.add_subgraph([TARGET],rank='max')
        grouped=defaultdict(list)
        for e in edges:
            if e['source'] not in ids or e['target'] not in ids:continue
            if e['kind']!='statement' and not e.get('globalEdge') and view not in ('all','companions') and e['route']!=int(view):continue
            grouped[e['source'],e['target']].append(e)
        for (s,t),ee in grouped.items():
            proof=[e for e in ee if e['kind']=='proof'];kind='proof' if proof else 'statement' if any(e['kind']=='statement' for e in ee) else 'construction'
            color=':'.join(COLORS[i] for i in sorted({e['route'] for e in proof})) if proof else '#202020'
            graph.add_edge(s,t,color=color,penwidth='1.6' if proof else '1.15',style='solid',**{'class':kind+'-edge'})
        indegrees={str(n):graph.in_degree(n) for n in graph.nodes()};todo=[n for n,v in indegrees.items() if not v];count=0
        while todo:
            n=todo.pop();count+=1
            for child in graph.successors(n):
                child=str(child);indegrees[child]-=1
                if not indegrees[child]:todo.append(child)
        assert count==len(ids) and not list(graph.successors(TARGET))
        if view=='2':assert not graph.has_edge(VALID,TARGET)
        graph.layout('dot');svg=BeautifulSoup(graph.draw(format='svg').decode(),'html.parser').svg
        for k in ['width','height']:svg.attrs.pop(k,None)
        for n in svg.select('g.node'):
            key=n.title.get_text();n['data-node']=key;n['tabindex']='0';n['role']='button';n['aria-label']=details[key]['title']
        for e in svg.select('g.edge'):
            s,t=e.title.get_text().split('->');records=grouped[s,t]
            e['data-edge']=s+'->'+t;e['data-edge-kind']='proof' if any(r['kind']=='proof' for r in records) else 'statement' if any(r['kind']=='statement' for r in records) else 'construction'
            e['tabindex']='0';e['role']='button';e['aria-label']='Inspect dependency'
        (site/file).write_text(str(svg));report_views[view]=dict(nodes=len(ids),edges=len(grouped))
    after=Counter((d['name'],d['type'],str(d.get('value'))) for b in details.values() for d in b['declarations'])
    assert not(before-after),'Existing declaration cards were lost'
    # Verify all new edges in their precise sense, and that consumer/source are
    # included in their bundles (not merely named in an unrelated module).
    for e in additions:
        for dep,user in zip(e['witness'],e['witness'][1:]):assert dep in nodes[user]['typeRefs']+nodes[user]['bodyRefs']
        assert e['witness'][-2] in nodes[e['witness'][-1]]['bodyRefs']
        for side,index in [('source',0),('target',-1)]:
            b=details[e[side]];names=set(b['anchors'])|{d['name'] for d in b['declarations']}
            assert e['witness'][index] in names,(e[side],e['witness'][index])
    fingerprint=hashlib.sha256((site/'proof-bench/data.json').read_bytes()).hexdigest()
    info=dict(version=1,sourceCommit=sha,noIntegrabilityPredicateIntroduced=True,
              oldProofTermsUnchanged=True,chosenProgram='retained mesh r <= k, evaluation stage k',
              genericScheduledBoundsAreContextOnly=True,mathlibValidityIsSeparate=True,
              newEdgeWitnesses=additions,views=report_views,proofMetricsFileSha256=fingerprint,
              checks=extra['checks'],displayedConvergenceProofs=VALIDS)
    data['schedulePresentation']=info
    (reading/'maps.json').write_text(json.dumps(data,separators=(',',':')))
    (reading/'schedule-proof-map.json').write_text(json.dumps(info,indent=2)+'\n')
    (reading/'schedule-declarations.json').write_text(json.dumps(extra,separators=(',',':')))
    chapter=site/'cosine.html';text=chapter.read_text()
    note=r'''<section id="the-chosen-schedule"><h2>The chosen schedule and its convergence</h2>
<p>The integrand returns computable numbers at rational inputs. Subdivision and sample evaluation therefore have separate indices. An integral construction includes a prescribed joint plan and a certificate that its rational bounds are compatible and shrink; we do not introduce a separate notion of integrability.</p>
<p>The existing computation in this theorem retains all meshes through k, reevaluates them at stage k, and intersects their widened enclosures. That is one concrete successful plan, not a claim that every increasing pair of stage indices works. The proof map now separates its numerical definition from its convergence certificates.</p>
<p>The integral-construction panel also shows a checked generic interface for a supplied pair of schedules and an equivalence theorem for successful cross-compatible choices. These generic lemmas are contextual: they have not silently replaced the retained-mesh evaluator used by the existing proofs.</p></section>'''
    assert 'id="the-chosen-schedule"' not in text
    text=text.replace('<h2 id="three-arguments">',note+'<h2 id="three-arguments">',1)
    chapter.write_text(text)
    print('PASS: schedule data/certificate/equivalence distinguished; actual validity uses and Mathlib endpoint bridge witnessed; no original proof changed')
    print(report_views)

if __name__=='__main__':main()
