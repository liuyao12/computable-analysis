#!/usr/bin/env python3
"""A focused view of the rendered blueprint, not another statement database.

Preserve plasTeX theorem modals and normal shape conventions. Contract actual
stored references between selected mathematical landmarks. Keep route identity
through contraction/reduction; all three final proof declarations map to one
statement node. No type edge from that node back to a proof is inserted.
"""
from __future__ import annotations
import argparse, collections, gzip, hashlib, html, json, os, re, shutil, subprocess
from pathlib import Path
import pygraphviz as pgv
from proof_lanes import layout_graph

ROOT=Path(__file__).resolve().parents[2]
N='ComputableAnalysis.'
M='MathlibComparison.'
TARGET='thm:c3-primitive'
# LaTeX label, short visual title, actual Lean declaration anchors.
PICKS=[
 ('def:c3-rationals','Rational numbers (ℚ)',['Rat']),
 ('def:c3-mreal','Mathlib real numbers',['Real','Real.ofCauchy']),
 ('def:c3-intervals','Nested rational intervals',[N+'RealRaw',N+'QInterval',N+'RealRaw.Valid',N+'RealRaw.Equiv']),
 ('def:c3-arctan','Geometric arctangent',[N+'CosinePrimitive.A',N+'ArctanGeometry.arctanGeom',N+'ArctanGeometry.arctanIntegralRectangleRaw']),
 ('def:c3-pi','Arctangent definition of pi',[N+'CosinePrimitive.pi']),
 ('lem:c3-inverse','Closed arctangent inverse',[N+'ClosedArctanInverse.provider']),
 ('def:c3-trig','Native sine and cosine',[N+'CosinePrimitive.S',N+'CosinePrimitive.C',N+'CosineFTC.sine',N+'CosineFTC.cosine',N+'SinPiIntegral.sinPiRawOfArctan',N+'SinPiIntegral.cosPiRawOfArctan']),
 ('def:c3-integral','Cosine integral computation',[N+'CosinePrimitive.integral']),
 ('lem:c3-direct','Finite geometric inequalities',[N+'CosineFTC.fixedMesh_overlaps_endpoint']),
 ('lem:c3-concavity','Concavity and secant data',[N+'GeometricSineConcavity.primitiveDerivativeData']),
 ('thm:c3-ftc','Native concave FTC',[N+'ConcaveFTC.integral_equiv_endpoint']),
 ('def:c3-real','Mathlib real interpretation',[M+'Represents']),
 ('def:c3-mexp','Mathlib exponential\nand trigonometry',['Complex.exp','Real.sin','Real.cos']),
 ('def:c3-mpi','Mathlib definition of pi',['Real.pi']),
 ('lem:c3-values','Special-function value bridges',[M+'sine_represents',M+'cosine_represents',M+'piCircleArea_represents']),
 ('lem:c3-quadrature','Quadrature-to-integral bridge',[M+'cosine_integral_represents']),
 ('lem:c3-mftc','Mathlib cosine primitive',[M+'mathlib_cosine_primitive']),
 (TARGET,'Cosine primitive\nOne statement, three proofs',[
     N+'CosinePrimitive.viaInequalities',N+'CosinePrimitive.viaFTC',N+'CosinePrimitive.viaMathlib']),
 ('lem:c3-native-exp','Native complex exponential\nCompanion computation',[N+'RotationSeries.rotationExpRaw_valid'])]
COLORS=['#a45032','#326493','#7755a0']


def closure(nodes,roots):
    seen=set(); todo=list(roots)
    while todo:
        x=todo.pop()
        if x in seen: continue
        seen.add(x);todo.extend(nodes[x]['refs'])
    return seen


def find_edges(nodes,picks,route):
    selected={a:k for k,_,aa in picks for a in aa}
    edges={}
    for target,_,anchors in picks:
        for root in anchors:
            if route is not None and route not in nodes[root]['routes']: continue
            previous={root:None}; todo=collections.deque([root])
            while todo:
                x=todo.popleft()
                for dep in sorted(set(nodes[x]['refs'])):
                    if dep in previous: continue
                    previous[dep]=x
                    if dep in selected and selected[dep]!=target:
                        source=selected[dep]; path=[dep];y=x
                        while y is not None:path.append(y);y=previous[y]
                        pair=(source,target)
                        if pair not in edges or len(path)<len(edges[pair]['witness']):
                            edges[pair]={'source':source,'target':target,'witness':path,'route':route}
                    else:todo.append(dep)
    # Reduction is performed for each alternative route, never on their union.
    g=pgv.AGraph(directed=True,strict=True)
    g.add_nodes_from(k for k,_,_ in picks)
    for s,t in edges:g.add_edge(s,t)
    if not g.is_directed(): raise ValueError('Expected directed graph')
    subprocess.run(['dot','-Tcanon'],input=g.string(),text=True,capture_output=True,check=True)
    reduced=g.tred()
    return [edges[(str(e[0]),str(e[1]))] for e in reduced.edges()]


def dot_for(nodes,picks,edges,route=None):
    return layout_graph(nodes,picks,edges,route)


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--site',type=Path,default=ROOT/'blueprint/web')
    ap.add_argument('--report',type=Path,default=ROOT/'comparison/reports/three-proofs.json')
    ap.add_argument('--commit',default=os.getenv('GITHUB_SHA'));args=ap.parse_args()
    sha=args.commit or subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip()
    if not re.fullmatch('[a-f0-9]{40}',sha):raise ValueError('An exact source SHA is required')
    report=json.loads(args.report.read_text()); nodes={n['id']:n for n in report['nodes']}
    assert all(report['checks'].values())
    source=args.site/'dep_graph_document.html'; text=source.read_text()
    for k,_,aa in PICKS:
        assert f'id="{k}_modal"' in text, f'Missing real blueprint modal {k}'
        for a in aa:assert a in nodes, f'Missing measured declaration {a}'
    tex=(ROOT/'blueprint/src/06-three-cosine-proofs.tex').read_text()
    for group in re.findall(r'\\lean\{([^}]+)\}',tex):
        for name in group.split(','):
            assert name.strip() in nodes, f'Unaudited blueprint declaration {name}'
    selections=PICKS[:-1];edges=[]
    for route in range(3):edges+=find_edges(nodes,selections,route)
    auxiliary=find_edges(nodes,PICKS,None)
    auxiliary=[e for e in auxiliary if e['target']=='lem:c3-native-exp']
    views={'all':dot_for(nodes,selections,edges),'companions':dot_for(nodes,PICKS,edges+auxiliary)}
    for i in range(3):views[str(i)]=dot_for(nodes,selections,edges,i)
    for e in edges+auxiliary:
        for dep,consumer in zip(e['witness'],e['witness'][1:]):assert dep in nodes[consumer]['refs']
    for key,dot in views.items():
        g=pgv.AGraph(string=dot)
        assert sum(str(n)==TARGET for n in g.nodes())==1
        assert not list(g.successors(TARGET)), 'The theorem is a sink, not an assumption of its proofs'
        assert not list(g.predecessors('def:c3-rationals'))
        assert g.has_edge('def:c3-rationals','def:c3-intervals')
        if g.has_node('def:c3-mreal'):
            assert g.has_edge('def:c3-rationals','def:c3-mreal')
        indegree={str(n):g.in_degree(n) for n in g.nodes()};todo=[n for n,d in indegree.items() if d==0];count=0
        while todo:
            n=todo.pop();count+=1
            for m in g.successors(n):
                m=str(m);indegree[m]-=1
                if indegree[m]==0:todo.append(m)
        assert count==len(indegree),f'Cycle in {key}'
    assets=args.site/'three-proofs';assets.mkdir(exist_ok=True)
    manifest={}
    for n in nodes.values():
        m=n['module'];p=(m.replace('.','/')+'.lean')
        if m.startswith('ComputableAnalysis'): f=ROOT/p
        elif m.startswith('MathlibComparison'):f=ROOT/'comparison'/p
        else:continue
        if f.is_file():manifest[str(f.relative_to(ROOT))]=hashlib.sha256(f.read_bytes()).hexdigest()
    info={'sourceCommit':sha,'leanVersion':report['leanVersion'],'mathlibCommit':'51e6992efd06126df61a496bebf8f49482a4e129',
          'checks':report['checks'],'metrics':report['metrics'],'sourceManifest':manifest,
          'referenceNodeCount':len(nodes),'blueprintNodeCount':len(selections)}
    (assets/'summary.json').write_text(json.dumps(info,indent=2)+'\n')
    with gzip.open(assets/'references.json.gz','wt') as out:json.dump(report,out,separators=(',',':'))
    (assets/'witnesses.json').write_text(json.dumps(edges+auxiliary,indent=2)+'\n')
    for k,_,aa in PICKS:
        links=[]
        for a in aa:
            n=nodes[a];m=n['module'];p=m.replace('.','/')+'.lean'
            if m.startswith('MathlibComparison'):base=f'https://github.com/liuyao12/computable-analysis/blob/{sha}/comparison/'
            elif m.startswith('ComputableAnalysis'):base=f'https://github.com/liuyao12/computable-analysis/blob/{sha}/'
            elif m.startswith(('Init.', 'Lean.', 'Std.')):base='https://github.com/leanprover/lean4/blob/v'+report['leanVersion']+'/src/'
            else:base='https://github.com/leanprover-community/mathlib4/blob/'+info['mathlibCommit']+'/'
            r=n['sourceRange'];url=base+p+(f"#L{r['start']}-L{r['end']}" if r else '')
            links.append(f'<a target="_blank" rel="noopener" href="{html.escape(url)}">{html.escape(a)}</a>')
        pattern=r'(<div class="dep-modal-container" id="'+re.escape(k)+r'_modal">\s*<div class="dep-modal-content">)'
        text,n=re.subn(pattern,lambda m:m.group(1)+'<div class="proof-source-links">'+''.join(links)+'</div>',text,count=1)
        assert n==1,k
    payload=json.dumps({'views':views,'info':info,'witnesses':edges+auxiliary},separators=(',',':')).replace('</','<\\/')
    controller=(ROOT/'blueprint/three-proofs/graph.js').read_text()
    match=re.search(r'<script type="text/javascript">\s*const graphContainer.*?</script>',text,re.S)
    assert match,'Unknown blueprint graph template'
    text=text[:match.start()]+'<script>const proofGraphData='+payload+';\n'+controller+'</script>'+text[match.end():]
    text=text.replace('<title>Dependency graph</title>','<title>One cosine primitive · Three proofs</title>')
    text=text.replace('<h1 id="doc_title">Dependencies</h1>','<h1 id="doc_title">One cosine primitive · Three proofs</h1>')
    banner=(ROOT/'blueprint/three-proofs/toolbar.html').read_text().replace('SOURCE_SHA',sha[:12])
    text=text.replace('</header>','</header>'+banner,1)
    text=text.replace('</head>','<link rel="stylesheet" href="three-proofs/graph.css" /></head>',1)
    (args.site/'cosine-primitive-graph.html').write_text(text)
    shutil.copyfile(ROOT/'blueprint/three-proofs/graph.css',assets/'graph.css')
    original=source.read_text()
    link='<div style="padding:10px 20px"><a href="cosine-primitive-graph.html">Three proofs of one cosine primitive — focused blueprint graph</a></div>'
    source.write_text(original.replace('</header>','</header>'+link,1))
    assert 'cosine-primitive-graph.html' in (args.site/'index.html').read_text()
    print('PASS: one shared sink; three acyclic routes; all displayed paths witnessed; all chapter Lean names audited')
    print(json.dumps({k:v for k,v in info.items() if k not in ['sourceManifest','metrics']},indent=2))

if __name__=='__main__':main()
