#!/usr/bin/env python3
"""Render the measured Lean declaration graph, without inventing dependencies.

The overview contracts paths between selected declarations. Every displayed
edge carries a shortest witness path in the uncontracted type/body graph.
The declaration explorer exposes the uncontracted graph. Source-size metrics
use unions of Lean-reported source ranges, so overlapping helper ranges are
never double counted. Graphviz is a layout tool only, not a proof checker.
"""
from __future__ import annotations
import argparse, collections, hashlib, json, os, pathlib, platform, shutil
import statistics, subprocess, sys, re
ROOT = pathlib.Path(__file__).resolve().parents[2]
PREFIX = 'ComputableAnalysis.'
PICKS = [
 ('ArctanGeometry.arctanIntegralRectangleRaw_equiv_arctanGeom', 'Arctan: rectangles = geometry'),
 ('GeometricSineDerivative.slope_clock_close', 'Inverse arctan clock'),
 ('GeometricSineFiniteBounds.finite_normalized_residual', 'Finite quadratic inequality'),
 ('GeometricSineDirectBounds.positive_increment_error', 'Geometric increment bound'),
 ('CosineFTC.fixedMesh_overlaps_endpoint', 'Cosine sums overlap endpoints'),
 ('GeometricSineConcavity.chord_tangent_bounds', 'Circle chord / tangent bounds'),
 ('GeometricSineConcavity.selected_support', 'Supporting-line inequalities'),
 ('GeometricSineConcavity.primitive_concave', 'Concavity of sine / pi'),
 ('GeometricSineConcavity.primitiveDerivativeData', 'Concave derivative certificate'),
 ('ConcaveFTC.local_residual_bound', 'General local FTC estimate'),
 ('ConcaveFTC.integral_equiv_endpoint', 'General concave FTC'),
 ('CosineFTC.integral_cosPi_viaInequalities', 'PROOF 1 · Direct inequalities'),
 ('CosineFTC.integral_cosPi_viaFTC', 'PROOF 2 · Via FTC'),
]
SUPPLEMENT_PICKS = [
 ('GeometricSineConcavity.sine_concave', 'Concavity of geometric sine'),
 ('GeometricSineConcavity.sineDerivative_valid', 'Secant derivative is valid'),
 ('GeometricSineConcavity.sineDerivative_equiv_pi_cosine', 'Secant derivative = pi cosine'),
]
COLORS = {'shared':'#54796d','direct':'#a25336','ftc':'#385fa3','auxiliary':'#8c729e'}

def strip_comments(text: str) -> str:
    """Remove nested Lean comments, retaining lines and string contents."""
    out=[]; i=0; block=0; string=False
    while i<len(text):
        c=text[i]; nxt=text[i:i+2]
        if block:
            if nxt=='/-': block+=1; out.extend('  '); i+=2; continue
            if nxt=='-/': block-=1; out.extend('  '); i+=2; continue
            out.append('\n' if c=='\n' else ' '); i+=1; continue
        if string:
            out.append(c); i+=1
            if c=='\\' and i<len(text): out.append(text[i]);i+=1
            elif c=='"': string=False
            continue
        if nxt=='/-': block=1;out.extend('  ');i+=2;continue
        if nxt=='--':
            while i<len(text) and text[i]!='\n': out.append(' ');i+=1
            continue
        out.append(c);string=c=='"';i+=1
    return ''.join(out)

def source_info(nodes):
    cache={}; manifest={}
    for n in nodes:
        path=n['module'].replace('.','/')+'.lean'
        n['sourcePath']=path if n['project'] else None
        n['sourceLines']=0
        if not n['project']: continue
        p=ROOT/path
        if not p.exists(): raise ValueError(f'Missing measured source {p}')
        if path not in cache:
            raw=p.read_bytes();manifest[path]=hashlib.sha256(raw).hexdigest()
            cache[path]=strip_comments(raw.decode()).splitlines()
        r=n['sourceRange']
        if r:
            n['sourceLines']=sum(bool(t.strip()) for t in cache[path][r['start']-1:r['end']])
    return cache, manifest

def source_union(ns,cache):
    lines=collections.defaultdict(set)
    for n in ns:
        r=n['sourceRange']; path=n['sourcePath']
        if path and r: lines[path].update(range(r['start'],r['end']+1))
    return sum(bool(cache[p][i-1].strip()) for p,ids in lines.items() for i in ids if i<=len(cache[p]))

def summarize(raw, nodes, cache):
    out={}
    shared=[n for n in nodes if n['direct'] and n['ftc'] and n['project']]
    for side,root,bench in zip(('direct','ftc'),raw['roots'],raw['kernelRecheck']):
        alln=[n for n in nodes if n[side]]; ns=[n for n in alln if n['project']]
        exc=[n for n in ns if not n['ftc' if side=='direct' else 'direct']]
        r=next(n for n in ns if n['id']==root)
        times=[x/1e6 for x in bench['nanoseconds']]
        out[side]={
            'root':root,'rootSourceLines':r['sourceLines'],
            'rootTreeNodes':r['bodyTreeNodes'],'rootDagNodes':r['bodyDagNodes'],
            'allDeclarations':len(alln),'projectDeclarations':len(ns),
            'sharedProjectDeclarations':len(shared),'exclusiveProjectDeclarations':len(exc),
            'projectBodyTreeNodes':sum(n['bodyTreeNodes'] for n in ns),
            'projectBodyDagNodes':sum(n['bodyDagNodes'] for n in ns),
            'exclusiveBodyTreeNodes':sum(n['bodyTreeNodes'] for n in exc),
            'exclusiveBodyDagNodes':sum(n['bodyDagNodes'] for n in exc),
            'reachableSourceLines':source_union(ns,cache),
            'exclusiveSourceLines':source_union(exc,cache),
            'kernelMedianMs':statistics.median(times),'kernelMinMs':min(times),
            'kernelMaxMs':max(times),'kernelSamplesMs':times,
            'axioms':bench['axioms'],'axiomCount':len(bench['axioms']),
        }
    union=sum(n['project'] and (n['direct'] or n['ftc']) for n in nodes)
    out['shared']={'projectDeclarations':len(shared),'unionProjectDeclarations':union,
        'jaccard':len(shared)/union,'sourceLines':source_union(shared,cache)}
    return out

def get_path(adj,start,end):
    prev={start:None}; todo=collections.deque([start])
    while todo:
        n=todo.popleft()
        if n==end:
            p=[]
            while n is not None: p.append(n);n=prev[n]
            return list(reversed(p))
        for d in adj[n]:
            if d not in prev:prev[d]=n;todo.append(d)
    return None

def overview(nodes, include_supplements=False):
    byid={n['id']:n for n in nodes}
    picks=[(PREFIX+k,v) for k,v in PICKS+(SUPPLEMENT_PICKS if include_supplements else [])]
    selected={k for k,_ in picks}
    for k in selected:
        if k not in byid:raise ValueError(f'Missing overview declaration: {k}')
    adj={n['id']:sorted(set(n['bodyRefs']+n['typeRefs'])) for n in nodes}
    edges=[]
    for consumer,_ in picks:
        prev={consumer:None};todo=collections.deque([consumer])
        while todo:
            curr=todo.popleft()
            for dep in adj[curr]:
                if dep in prev:continue
                prev[dep]=curr
                if dep in selected:
                    path=[dep]; x=curr
                    while x is not None:path.append(x);x=prev[x]
                    edges.append({'source':dep,'target':consumer,'witness':path})
                else:todo.append(dep)
    reduced=[]
    for edge in edges:
        aa={n:set() for n in selected}
        for other in edges:
            if other is not edge: aa[other['source']].add(other['target'])
        if get_path(aa,edge['source'],edge['target']) is None: reduced.append(edge)
    dot=['digraph G {','graph [rankdir=BT, nodesep=0.32, ranksep=0.52, pad=0.15];',
         'node [shape=box, width=2.85, height=0.65, fixedsize=true, fontname="Arial", fontsize=12];']
    ids={k:f'n{i}' for i,(k,_) in enumerate(picks)}
    for k,label in picks:dot.append(f'{ids[k]} [label={json.dumps(label)}];')
    for e in reduced:dot.append(f'{ids[e["source"]]} -> {ids[e["target"]]};')
    dot.append('}')
    layout=json.loads(subprocess.run(['dot','-Tjson'],input='\n'.join(dot),text=True,capture_output=True,check=True).stdout)
    bb=[float(x) for x in layout['bb'].split(',')]; H=bb[3]
    obj={o['name']:o for o in layout['objects']}
    resultnodes=[]
    for k,label in picks:
        o=obj[ids[k]];x,y=map(float,o['pos'].split(','))
        resultnodes.append({'id':k,'label':label,'x':x,'y':H-y,'w':float(o['width'])*72,'h':float(o['height'])*72})
    return {'width':bb[2],'height':H,'nodes':resultnodes,'edges':reduced}

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--raw',type=pathlib.Path,default=ROOT/'blueprint/proof-comparison/raw.json')
    ap.add_argument('--out',type=pathlib.Path,default=ROOT/'blueprint/web/proof-comparison')
    ap.add_argument('--commit',default=os.environ.get('PROOF_SOURCE_COMMIT'))
    args=ap.parse_args(); raw=json.loads(args.raw.read_text());nodes=raw['nodes']
    commit=args.commit or subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip()
    if len(commit)!=40 or any(c not in '0123456789abcdef' for c in commit):raise ValueError('Expected exact source SHA')
    if not all(raw[k] for k in ('sameType','independentRoots','noSorryAx')):raise ValueError('Proof audit failed')
    cache,manifest=source_info(nodes)
    summary=summarize(raw,nodes,cache)
    data={'schemaVersion':1,'sourceCommit':commit,'leanVersion':raw['leanVersion'],
      'repository':'liuyao12/computable-analysis','roots':raw['roots'], 'supplements':raw['supplements'],
      'summary':summary,'nodes':nodes,'overview':overview(nodes), 'overviewSupplement':overview(nodes,True),
      'verification':{k:raw[k] for k in ('sameType','independentRoots','noSorryAx')},
      'sourceManifest':manifest,'timingEnvironment':{'machine':platform.machine(),'platform':platform.system(),
        'method':'Synchronous Kernel.check plus Kernel.isDefEq; dependencies loaded; 11 trials after one warmup; excludes imports, elaboration, and recursive dependency verification.'}}
    args.out.mkdir(parents=True,exist_ok=True)
    for name in ('index.html','style.css','app.js'):
        shutil.copyfile(ROOT/'blueprint/proof-comparison'/name,args.out/name)
    (args.out/'data.json').write_text(json.dumps(data,separators=(',',':'))+'\n')
    (args.out/'summary.json').write_text(json.dumps({k:data[k] for k in ('sourceCommit','leanVersion','summary','verification','timingEnvironment')},indent=2)+'\n')
    shutil.copyfile(args.raw,args.out/'raw.json')
    shutil.copyfile(ROOT/'blueprint/checks/ExportProofComparison.lean',args.out/'ExportProofComparison.lean')
    (args.out/'source-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
    for graph in ('overview','overviewSupplement'):
        for e in data[graph]['edges']:
            for dep,consumer in zip(e['witness'],e['witness'][1:]):
                cn=next(n for n in nodes if n['id']==consumer)
                assert dep in cn['bodyRefs']+cn['typeRefs'], (dep,consumer)
    native = args.out.parent/'dep_graph_document.html'
    if native.exists():
        text = native.read_text()
        if 'id="measured-proof-link"' not in text:
            banner = ('<div id="measured-proof-link" style="padding:12px 20px;background:#eef3ef;'
                'border-bottom:1px solid #b5c9bf;font:15px system-ui">'
                '<a href="proof-comparison/index.html">Two cosine proofs: measured dependencies and quantitative comparison</a>'
                ' · Source ' + commit[:12] + '</div>')
            text = re.sub(r'(<body[^>]*>)', lambda m: m.group(1)+banner, text, count=1)
            native.write_text(text)
    print(json.dumps(summary,indent=2))
    print(f'Published graph assets in {args.out}; every overview edge has a checked reference-path witness.')
if __name__=='__main__':main()
