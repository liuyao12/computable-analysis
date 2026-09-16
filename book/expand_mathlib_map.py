#!/usr/bin/env python3
"""Expose checked Mathlib integration layers and compare the actual proof closures.

This is a documentation view. No production Lean statement, proof or algorithm
is changed. Every new arrow has a stored reference witness. Measurement roots
remain the previously audited paired statements, never the display bundles.
"""
from __future__ import annotations
from collections import defaultdict, deque
from copy import deepcopy
import hashlib, json, re, shutil, sys
from pathlib import Path
import pygraphviz as pgv
from bs4 import BeautifulSoup

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT/'blueprint/checks'))
from build_proof_bench import closure, source_index, source_union, origin, ORIGINS

TARGET='thm:c3-primitive'
MATHLIB_SHA='51e6992efd06126df61a496bebf8f49482a4e129'
NONNEG='def:c3-mathlib-nonnegative'
BOCHNER='def:c3-mathlib-bochner'
INTERVAL='def:c3-mathlib-interval'
FTC='thm:c3-mathlib-ftc'
COLORS=['#a45032','#326493','#7755a0']

GROUPS={
 NONNEG: ('Nonnegative Lebesgue integral',[
   ('Finite simple functions and their supremum',[
     'MeasureTheory.SimpleFunc.lintegral','MeasureTheory.lintegral','MeasureTheory.lintegral_def']),
   ('Finite norm integral and measurability',[
     'MeasureTheory.HasFiniteIntegral','MeasureTheory.Integrable'])]),
 BOCHNER: ('General Bochner integral',[
   ('Simple functions and the continuous extension to L1',[
     'MeasureTheory.SimpleFunc.integral','MeasureTheory.L1.integralCLM',
     'MeasureTheory.L1.integral','MeasureTheory.L1.integral_def']),
   ('The general function-level integral',[
     'MeasureTheory.integral','MeasureTheory.integral_def']),
   ('Underlying extension mechanism',[
     'MeasureTheory.L1.setToL1','MeasureTheory.setToFun','MeasureTheory.integral_eq_setToFun'])]),
 INTERVAL: ('Mathlib interval integral',[
   ('Oriented intervals and restricted measures',[
     'intervalIntegral','IntervalIntegrable','MeasureTheory.Measure.restrict',
     'intervalIntegral.integral_of_le']),
   ('Order and finite additivity used in the quadrature bridge',[
     'intervalIntegral.integral_mono_on','intervalIntegral.integral_add_adjacent_intervals'])]),
 FTC: ('Mathlib FTC',[
   ('Integral of a supplied derivative',[
     'intervalIntegral.integral_eq_sub_of_hasDerivAt']),
   ('Derivative formulations used by the cosine formula',[
     'intervalIntegral.integral_deriv_eq_sub','intervalIntegral.integral_deriv_eq_sub\''])])}

TEXT={
 NONNEG: r'''<p>Mathlib first integrates nonnegative, possibly infinite-valued functions on a measure space. A finite simple function is integrated by a finite weighted sum; the general nonnegative integral is the supremum of simple-function integrals from below.</p>
<div class="displaymath">\[\int^- f\,d\mu=\sup\left\{\int s\,d\mu : s\text{ simple},\ s\le f\right\}.\]</div>
<p>The codomain is the extended nonnegative reals. This construction also supplies the integrals of norms used to define L1 and integrability in Mathlib. Its use of a supremum belongs to the comparison foundation, not our numerical evaluator.</p>
<p>The <code>Integrable</code> and <code>HasFiniteIntegral</code> declarations below are Mathlib's assumptions. No such predicate is being introduced in the native project.</p>''',
 BOCHNER: r'''<p>This is the general vector-valued integral used by the Mathlib route: functions from a measure space to a real normed vector space, with the nontrivial case in a complete target.</p>
<p>Integrate simple functions, extend continuously to L1 equivalence classes, and apply that extension to an integrable function. In the pinned definition, the value is set to zero if the function is not integrable or the target is not complete. Correct applications therefore supply the required hypotheses; zero in a default case is not a proof of the intended integral.</p>
<p>For real-valued functions this gives the usual Lebesgue integral. The construction is not merely a limit of our rational rectangle computations, and its general codomain is not the same as the nonnegative extended-real integral above.</p>
<p>The exact <code>integral_def</code> equation exposes the definition behind Mathlib's opaque wrapper. The L1 extension and its underlying <code>setToL1</code> mechanism are available below.</p>''',
 INTERVAL: r'''<p>Mathlib's interval notation is an oriented version of its Bochner integral, normally with Lebesgue measure on the real line:</p>
<div class="displaymath">\[\int_a^b f=\int_{(a,b]} f\,d\mathrm{vol}-\int_{(b,a]} f\,d\mathrm{vol}.\]</div>
<p>The function is defined on Mathlib reals, not merely rational inputs. <code>IntervalIntegrable</code> records the integrability hypotheses on the relevant restricted measures.</p>
<p>The quadrature bridge uses continuity, integral order on each cell, and finite additivity to identify our actual sample program with this integral. The cosine primitive formula is not used in that bridge. These same interval objects also occur in the hypotheses and conclusion of Mathlib's FTC.</p>''',
 FTC: r'''<p>Mathlib's fundamental theorem identifies the interval integral of a derivative with the difference of the primitive's endpoint values. The displayed general theorem allows values in a complete real normed vector space.</p>
<div class="displaymath">\[\int_a^b f'(x)\,dx=f(b)-f(a).\]</div>
<p>Its hypotheses include differentiability on the stated closed interval and interval integrability of the derivative. The exact declarations below show those hypotheses, rather than assuming that any pointwise derivative can be integrated.</p>
<p>For cosine, Mathlib uses its theorem about the derivative of sine and <code>integral_deriv_eq_sub'</code> to prove <code>integral_cos</code>. Our comparison then rescales the argument by pi and combines the result with independent value and quadrature bridges. This is the genuine FTC dependency in the stored proof, not a decorative node.</p>'''}


def witness(nodes,start,goal,mode='refs'):
    previous={start:None};todo=deque([start])
    while todo:
        n=todo.popleft()
        if n==goal:
            out=[]
            while n is not None:out.append(n);n=previous[n]
            return out
        d=nodes[n]
        if mode=='definitions' and d['kind'] not in ('definition','def','opaque'):continue
        keys=['typeRefs'] if mode=='type' and n==start else ['bodyRefs'] if mode=='definitions' or (mode=='proof' and n==start) else ['typeRefs','bodyRefs']
        for dep in sorted({dep for k in keys for dep in d[k]}):
            if dep not in previous:previous[dep]=n;todo.append(dep)
    return None


def source_metrics(names,nodes,records,cache):
    src=source_union(names,records,cache)
    result={'declarations':len(names),'codeLines':src['nonblankCodeLines'],
            'mappedDeclarations':src['mappedDeclarations'],
            'unmappedDeclarations':src['unmappedDeclarations'],
            'sourceFiles':src['availableSourceFiles']}
    return result


def build_comparison(raw,bench,nodes):
    records,cache,manifest=source_index(nodes)
    cases={}
    for key,case_ids,title in [
      ('identity',['cosine-primitive'],'Endpoint identity'),
      ('validity',['cosine-validity'],'Convergence certificate'),
      ('combined',['cosine-primitive','cosine-validity'],'Identity and convergence, shared work counted once')]:
        roots={route:[bench['cases'][case]['routes'][route]['root'] for case in case_ids]
               for route in ['direct','ftc','mathlib']}
        sets={route:closure(nodes,rs) for route,rs in roots.items()}
        statement=set().union(*(closure(nodes,nodes[n]['typeRefs']) for rs in roots.values() for n in rs))
        shared=set.intersection(*sets.values())
        rows={}
        for route,names in sets.items():
            costs={}
            for base,group in [('full',names),('statement-free',names-statement),('shared-free',names-shared)]:
                data=source_metrics(group,nodes,records,cache)
                data['origins']={o:source_metrics({n for n in group if origin(nodes[n]['module'])==o},nodes,records,cache) for o in ORIGINS}
                assert sum(x['codeLines'] for x in data['origins'].values())==data['codeLines']
                assert sum(x['declarations'] for x in data['origins'].values())==data['declarations']
                if key!='combined':
                    old=bench['cases'][case_ids[0]]['routes'][route]['sizes'][base]
                    assert data['declarations']==old['declarations']
                    # Preserve the report's source availability: missing ranges do
                    # not quietly become zero cost, and new display roots add none.
                    assert data['codeLines']==old['source']['nonblankCodeLines'],(key,route,base,data['codeLines'],old['source'])
                costs[base]=data
            rows[route]={'roots':roots[route],'costs':costs,
                'finalApplication':source_metrics(set(roots[route]),nodes,records,cache)}
        cases[key]={'title':title,'routes':rows,
                    'baselines':{'statementDeclarations':len(statement),'sharedDeclarations':len(shared)}}
    return {'schemaVersion':1,'sourceCommit':bench['sourceCommit'],
      'cases':cases,'routeOrder':['direct','ftc','mathlib'],
      'method':'Count each transitive type/body reference once. LOC is the union of available declaration source ranges after removing comments and blank lines; it includes definitions and proof scripts. Unmapped declarations are reported, not assigned zero-cost proofs.',
      'codeLineLabel':'Mapped source LOC','sourceAvailability':manifest,
      'noNewMeasurementRoots':True}


def main():
    site=ROOT/'blueprint/web';reading=site/'reading'
    model=json.loads((reading/'maps.json').read_text());sha=model['sourceCommit']
    assert 'mathlibExpansion' not in model,'Run on the freshly built schedule-aware map'
    raw=json.loads((ROOT/'comparison/reports/proof-bench-raw.json').read_text())
    nodes={n['id']:n for n in raw['nodes']}
    extra=json.loads((ROOT/'comparison/reports/mathlib-map-statements.json').read_text())
    assert all(extra['checks'].values())
    exact={d['name']:d for d in extra['declarations']}
    for name,d in exact.items():
        assert name in nodes,('Display declaration is not in the measured proof graph',name)
        assert set(d['typeRefs'])==set(nodes[name]['typeRefs']) and set(d['bodyRefs'])==set(nodes[name]['bodyRefs'])
    bench_path=site/'proof-bench/data.json';bench_bytes=bench_path.read_bytes()
    bench=json.loads(bench_bytes)
    assert bench['sourceCommit']==sha
    comparison=build_comparison(raw,bench,nodes)
    mathlib_root=bench['cases']['cosine-primitive']['routes']['mathlib']['root']
    used=closure(nodes,[mathlib_root])
    assert set(exact)<=used,'Do not charge or imply unreferenced foundation statements'
    # Exact statements may be explanatory companions even when another variant
    # carries the particular displayed arrow. Per-card use is still available.
    def card(name):
        d=deepcopy(exact[name]);d['realDependencyPath']=list(reversed(witness(nodes,name,'Real') or []))
        assert d['realDependencyPath']
        span=d['sourceRange'];suffix=f"#L{span['start']}-L{span['end']}" if span else ''
        d['sourceUrl']=f"https://github.com/leanprover-community/mathlib4/blob/{MATHLIB_SHA}/"+d['ownerModule'].replace('.','/')+'.lean'+suffix
        return d
    details=model['bundles']
    for key,(title,groups) in GROUPS.items():
        names=[n for _,ns in groups for n in ns]
        details[key]={'title':title,'classification':'mathlib','anchors':names,
          'groups':[{'title':t,'names':ns} for t,ns in groups],
          'declarations':[card(n) for n in names],'declarationCount':len(names),
          'paths':{n:card(n)['realDependencyPath'] for n in names},'mathHtml':TEXT[key],
          'strategy':{'role':'Mathlib foundation used in the comparison','summary':'The native numerical definitions and their proofs do not import these declarations.','groups':{}}}
    details['def:c3-mexp']['title']='Complex exponential and trigonometry'
    b=details['def:c3-mexp']
    if not any(d['name']=='Real.deriv_sin' for d in b['declarations']):
        b['groups'].append({'title':'Sine derivative used in the integral formula','names':['Real.deriv_sin']})
        b['declarations'].append(card('Real.deriv_sin'));b['declarationCount']=len(b['declarations'])
    details['lem:c3-mftc']['mathHtml']+=r'''<p>The analytic calculation is explicitly downstream of Mathlib's FTC: <code>integral_cos</code> calls <code>intervalIntegral.integral_deriv_eq_sub'</code>. The rescaling theorem then gives the normalized formula. Its existence as a short application does not make the integral and FTC foundations cost-free.</p>'''
    additions=[]
    def edge(source,target,start,goal,kind='proof',mode=None,label=''):
        mode=mode or ('proof' if kind=='proof' else 'type')
        p=witness(nodes,start,goal,mode)
        assert p,(source,target,start,goal,mode)
        e={'source':source,'target':target,'kind':kind,'witness':p,'route':2,
           'referenceMode':mode,'label':label or ('Mathlib theorem use' if kind=='proof' else 'Mathlib integral definition')}
        if kind!='proof':e['globalEdge']=True
        if mode=='type':e['typeEntry']=True
        additions.append(e)
    edge('def:c3-mreal',NONNEG,'MeasureTheory.lintegral','Real','construction','type','Extended nonnegative real values')
    edge(NONNEG,BOCHNER,'MeasureTheory.integral','MeasureTheory.lintegral','construction','definitions','Norm integration in the L1 construction')
    edge('def:c3-mreal',BOCHNER,'MeasureTheory.integral','Real','construction','type','Real normed-vector-space target')
    edge(BOCHNER,INTERVAL,'intervalIntegral','MeasureTheory.integral','construction','definitions','Interval integral uses restricted Bochner integrals')
    edge(INTERVAL,FTC,'intervalIntegral.integral_deriv_eq_sub\'','intervalIntegral','construction','type','Interval integral in the FTC statement')
    edge(FTC,'lem:c3-mftc','integral_cos','intervalIntegral.integral_deriv_eq_sub\'',label='FTC applied to the sine derivative')
    edge('def:c3-mexp','lem:c3-mftc','integral_cos','Real.deriv_sin',label='The derivative of sine is cosine')
    edge(INTERVAL,'lem:c3-mftc','integral_cos','intervalIntegral','construction','type','Interval integral in the cosine formula')
    edge(INTERVAL,'lem:c3-quadrature','MathlibComparison.cosine_cell_error','intervalIntegral.integral_mono_on',label='Cellwise integral bounds, not an antiderivative')
    edge(INTERVAL,'lem:c3-quadrature','MathlibComparison.rectangle_error','intervalIntegral.integral_add_adjacent_intervals',label='Finite additivity across the mesh')
    edge(FTC,'lem:c3-values','MathlibComparison.arctan_rectangle_represents','intervalIntegral.integral_eq_sub_of_hasDerivAt',label='FTC for the independent rational-kernel arctangent bridge')
    # Endpoints of displayed witnesses must actually occur in the bundles.
    for e in additions:
        for side,i in [('source',0),('target',-1)]:
            bundle=details[e[side]];names=set(bundle['anchors'])|{d['name'] for d in bundle['declarations']}
            assert e['witness'][i] in names,(side,e['witness'][i],e[side])
    model['witnesses']+=additions
    views=model['theorems'][TARGET]['views'];counts={}
    for view in ['all','companions','2']:
        file=site/views[view];old=BeautifulSoup(file.read_text(),'html.parser')
        ids={n['data-node'] for n in old.select('[data-node]')}|set(GROUPS)
        graph=pgv.AGraph(strict=True,directed=True,rankdir='TB',bgcolor='transparent',splines='spline',
                        nodesep='.32',ranksep='.55',outputorder='edgesfirst')
        graph.node_attr.update(shape='box',style='rounded,filled',fontname='Helvetica',fontsize='12',margin='.15,.12',color='#879a8c',fontcolor='#27382f')
        graph.edge_attr.update(arrowhead='vee',arrowsize='.65')
        for key in sorted(ids):
            cls=details[key]['classification']
            fill='#eef3ed' if cls=='native' else '#f0eafa'
            if cls=='mixed':fill='#f0eafa' if view=='2' else '#eef3ed:#f0eafa'
            graph.add_node(key,label=details[key]['title'],fillcolor=fill)
        graph.get_node(TARGET).attr.update(penwidth='2.2',color='#355d49')
        graph.add_subgraph(['def:c3-rationals'],rank='min');graph.add_subgraph([TARGET],rank='max')
        graph.add_subgraph(['def:c3-intervals','def:c3-mreal'],rank='same')
        graph.add_subgraph(['def:c3-integrals','def:c3-arctan','def:c3-mexp',NONNEG],rank='same')
        graph.add_subgraph(['def:c3-pi','def:c3-trig',BOCHNER],rank='same')
        grouped=defaultdict(list)
        for e in model['witnesses']:
            if e.get('map') or e['source'] not in ids or e['target'] not in ids:continue
            if e['kind']!='statement' and not e.get('globalEdge') and view=='2' and e['route']!=2:continue
            grouped[e['source'],e['target']].append(e)
        for (s,t),es in grouped.items():
            proof=[e for e in es if e['kind']=='proof'];kind='proof' if proof else 'statement' if any(e['kind']=='statement' for e in es) else 'construction'
            col=':'.join(COLORS[i] for i in sorted({e['route'] for e in proof})) if proof else '#202020'
            graph.add_edge(s,t,color=col,style='solid',penwidth='1.6' if proof else '1.15',**{'class':kind+'-edge'})
        degrees={str(n):graph.in_degree(n) for n in graph.nodes()};queue=[n for n,v in degrees.items() if not v];nread=0
        while queue:
            n=queue.pop();nread+=1
            for ch in graph.successors(n):
                ch=str(ch);degrees[ch]-=1
                if not degrees[ch]:queue.append(ch)
        assert nread==len(ids) and not list(graph.successors(TARGET))
        graph.layout('dot');svg=BeautifulSoup(graph.draw(format='svg').decode(),'html.parser').svg
        for k in ['width','height']:svg.attrs.pop(k,None)
        for n in svg.select('g.node'):
            key=n.title.get_text();n['data-node']=key;n['tabindex']='0';n['role']='button';n['aria-label']=details[key]['title']
        for e in svg.select('g.edge'):
            s,t=e.title.get_text().split('->');es=grouped[s,t]
            e['data-edge']=s+'->'+t;e['data-edge-kind']='proof' if any(r['kind']=='proof' for r in es) else 'statement' if any(r['kind']=='statement' for r in es) else 'construction'
            e['tabindex']='0';e['role']='button';e['aria-label']='Inspect dependency'
        file.write_text(str(svg));counts[view]={'nodes':len(ids),'edges':len(grouped)}
    report={'sourceCommit':sha,'mathlibCommit':MATHLIB_SHA,'additionalBundles':list(GROUPS),
      'witnesses':additions,'views':counts,'benchmarkSha256':hashlib.sha256(bench_bytes).hexdigest(),
      'checks':{'exactMathlibStatements':True,'allNodesUsedInMeasuredProof':True,'actualFTCCall':True,
                'unchangedProofRootsAndMetrics':True,'allViewsAcyclic':True,'nativeViewsUnchanged':True}}
    model['mathlibExpansion']=report;model['mapComparison']={'url':'reading/map-comparison.json','case':TARGET}
    (reading/'maps.json').write_text(json.dumps(model,separators=(',',':')))
    (reading/'map-comparison.json').write_text(json.dumps(comparison,indent=2)+'\n')
    (reading/'mathlib-expansion.json').write_text(json.dumps(report,indent=2)+'\n')
    (reading/'mathlib-map-statements.json').write_text(json.dumps(extra,separators=(',',':')))
    for asset in ['map-comparison.css','map-comparison.js']:
        shutil.copyfile(ROOT/'book/assets'/asset,reading/asset)
    html=site/'proof-map.html';text=html.read_text()
    text=text.replace('</head>','<link rel="stylesheet" href="reading/map-comparison.css"></head>')
    text=text.replace('<script defer src="reading/graph.js">','<script defer src="reading/map-comparison.js"></script><script defer src="reading/graph.js">')
    html.write_text(text)
    assert bench_path.read_bytes()==bench_bytes
    print('PASS: Mathlib integration/FTC nodes with exact types and witnessed uses; inline paired declaration/LOC comparison')
    print(counts)
    for r,row in comparison['cases']['identity']['routes'].items():print(r,row['costs']['full']['declarations'],row['costs']['full']['codeLines'])

if __name__=='__main__':main()
