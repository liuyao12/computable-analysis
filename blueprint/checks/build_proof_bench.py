#!/usr/bin/env python3
"""Build reproducible multi-case proof accounting and a browser report.
No imported module count is substituted for an actual reference closure.
"""
from __future__ import annotations
import argparse, collections, gzip, hashlib, json, os, shutil, subprocess
from pathlib import Path
from build_proof_comparison import strip_comments

ROOT = Path(__file__).resolve().parents[2]
ORIGINS = ('native', 'bridge', 'mathlib', 'lean', 'other')
WEIGHTS = ('bodyTree', 'bodyDag', 'typeTree', 'typeDag')


def origin(module):
    if module.startswith('ComputableAnalysis'): return 'native'
    if module.startswith('MathlibComparison'): return 'bridge'
    if module.startswith('Mathlib.'): return 'mathlib'
    if module.startswith(('Init', 'Lean', 'Std', 'Lake')): return 'lean'
    return 'other'


def closure(nodes, seeds):
    seen, todo = set(), list(seeds)
    while todo:
        name = todo.pop()
        if name in seen: continue
        if name not in nodes: raise ValueError(f'Missing referenced declaration: {name}')
        seen.add(name)
        todo.extend(nodes[name]['typeRefs']); todo.extend(nodes[name]['bodyRefs'])
    return seen


def source_index(nodes):
    """Source counts are optional diagnostics with explicit coverage."""
    directories = [ROOT, ROOT/'comparison', ROOT/'comparison/.lake/packages/mathlib']
    directories += list((ROOT/'comparison/.lake/packages').glob('*'))
    directories += list((ROOT/'comparison/.lake/packages/mathlib/.lake/packages').glob('*'))
    if prefix := os.environ.get('LEAN_SYSROOT'):
        directories.append(Path(prefix)/'src/lean')
    records, cache, manifest = {}, {}, {}
    for name, node in nodes.items():
        span = node['sourceRange']
        if not span: continue
        rel = Path(node['module'].replace('.', '/')+'.lean')
        path = next((d/rel for d in directories if (d/rel).is_file()), None)
        if path is None: continue
        key = str(path.relative_to(ROOT)) if path.is_relative_to(ROOT) else 'lean-source/'+str(rel)
        if key not in cache:
            raw = path.read_bytes()
            cache[key] = strip_comments(raw.decode()).splitlines()
            manifest[key] = hashlib.sha256(raw).hexdigest()
        records[name] = (key, span['start'], span['end'])
    return records, cache, manifest


def source_union(names, records, cache):
    lines = collections.defaultdict(set); mapped = 0
    for name in names:
        if name not in records: continue
        mapped += 1; path, start, end = records[name]
        lines[path].update(range(start, end+1))
    count = sum(bool(cache[p][i-1].strip()) for p, ids in lines.items()
                for i in ids if 0 < i <= len(cache[p]))
    return {'nonblankCodeLines':count, 'mappedDeclarations':mapped,
            'unmappedDeclarations':len(names)-mapped, 'availableSourceFiles':len(lines)}


def totals(names, nodes, records=None, cache=None):
    bins = {k:{'declarations':0, **{w:0 for w in WEIGHTS}} for k in ORIGINS}
    for name in names:
        n = nodes[name]; b = bins[origin(n['module'])]; b['declarations'] += 1
        for key in WEIGHTS: b[key] += n[key]
    out = {'declarations':len(names), **{w:sum(b[w] for b in bins.values()) for w in WEIGHTS}, 'origins':bins}
    if records is not None: out['source'] = source_union(names, records, cache)
    return out


def audit_axioms(names):
    standard = {'propext','Classical.choice','Quot.sound'}
    native = [n for n in names if '_native.' in n or 'native_decide' in n or n == 'Lean.ofReduceBool']
    return {'standard':[n for n in names if n in standard], 'nativeComputation':native,
            'other':[n for n in names if n not in standard and n not in native]}


def build(raw, suite, nodes, records, cache):
    groups = collections.defaultdict(list)
    for row in raw['roots']: groups[row['case']].append(row)
    if set(groups) != set(suite['cases']): raise ValueError('Suite contracts and measured case registry differ')
    cases, closures = {}, {}
    for case, rows in groups.items():
        ds = {r['route']:closure(nodes,[r['root']]) for r in rows}
        for r in rows: closures[case,r['route']] = ds[r['route']]
        type_closures = [closure(nodes,nodes[r['root']]['typeRefs']) for r in rows]
        # Syntactic representations of definitionally equal types can differ;
        # use their union to state one symmetric, explicit common baseline.
        statement = set().union(*type_closures)
        shared = set.intersection(*ds.values())
        cr = {'contract':suite['cases'][case], 'routes':{},
              'statementBaseline':totals(statement,nodes,records,cache),
              'sharedBaseline':totals(shared,nodes,records,cache)}
        for r in rows:
            names = ds[r['route']]; node = nodes[r['root']]
            # A baseline is intersected with the actual root closure; it cannot
            # increase a route's cost or charge declarations it does not use.
            sets = {'full':names, 'statement-free':names-statement, 'shared-free':names-shared}
            cr['routes'][r['route']] = {
                **r, 'finalBody':{w:node[w] for w in WEIGHTS},
                'sizes':{k:totals(v,nodes,records,cache) for k,v in sets.items()},
                'axiomClasses':audit_axioms(r['axioms']),
                'largestBodies':[{'name':nodes[n]['name'],'module':nodes[n]['module'],
                    'bodyDag':nodes[n]['bodyDag'],'bodyTree':nodes[n]['bodyTree']}
                    for n in sorted(names-statement,key=lambda x:nodes[x]['bodyDag'],reverse=True)[:12]]}
        cases[case] = cr
    order = [k for k,v in suite['cases'].items() if v['countInPortfolio']]
    common_routes = set.intersection(*(set(cases[c]['routes']) for c in order))
    portfolios = {}
    for route in sorted(common_routes):
        cumulative=set(); steps=[]
        for case in order:
            ds=closures[case,route]; marginal=ds-cumulative; cumulative |= ds
            steps.append({'case':case,'added':totals(marginal,nodes,records,cache),
                          'union':totals(cumulative,nodes,records,cache)})
        portfolios[route]={'order':order,'steps':steps,'total':totals(cumulative,nodes,records,cache)}
    return cases, portfolios


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--raw',type=Path,default=ROOT/'comparison/reports/proof-bench-raw.json')
    ap.add_argument('--site',type=Path,default=ROOT/'blueprint/web')
    ap.add_argument('--commit',default=os.getenv('GITHUB_SHA'))
    args=ap.parse_args()
    raw=json.loads(args.raw.read_text());suite=json.loads((ROOT/'comparison/proof-bench/suite.json').read_text())
    if not all(raw['checks'].values()): raise ValueError('Failed proof audit')
    nodes={n['id']:n for n in raw['nodes']}
    for n in nodes.values():
        if n['bodyDag']>n['bodyTree'] or n['typeDag']>n['typeTree']:raise ValueError('Invalid expression metric')
    records,cache,manifest=source_index(nodes)
    cases,portfolios=build(raw,suite,nodes,records,cache)
    sha=args.commit or subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip()
    result={'schemaVersion':1,'sourceCommit':sha,'leanVersion':raw['leanVersion'],
            'checks':raw['checks'],'cases':cases,'portfolio':portfolios,'roadmap':suite['roadmap'],
            'method':'Stored type/body reference closures; per-body structural Expr DAG/tree sizes; no constant unfolding.',
            'sourceManifest':manifest,'uniqueMeasuredDeclarations':len(nodes)}
    out=args.site/'proof-bench';out.mkdir(parents=True,exist_ok=True)
    (out/'data.json').write_text(json.dumps(result,indent=2)+'\n')
    with gzip.open(out/'raw.json.gz','wt') as f:json.dump(raw,f,separators=(',',':'))
    for name in ('index.html','app.js','style.css'):shutil.copyfile(ROOT/'blueprint/proof-bench'/name,out/name)
    shutil.copyfile(ROOT/'comparison/proof-bench/README.md',out/'methodology.md')
    shutil.copyfile(ROOT/'comparison/proof-bench/cases.tsv',out/'cases.tsv')
    shutil.copyfile(ROOT/'comparison/proof-bench/suite.json',out/'suite.json')
    # These are links, not duplicated summaries that could become stale.
    for file in ['index.html','cosine-primitive-graph.html','dep_graph_document.html']:
        p=args.site/file
        if p.exists():
            text=p.read_text()
            banner='<div class="proof-bench-link" style="padding:8px 20px"><a href="proof-bench/">Proof-size laboratory: matched statements, foundation costs, and reuse across theorems</a></div>'
            if 'class="proof-bench-link"' not in text:text=text.replace('</header>','</header>'+banner,1)
            if 'class="proof-bench-link"' not in text:text=text.replace('<body>','<body>'+banner,1)
            p.write_text(text)
    print('PASS: measured matched cases, explicit baselines, source coverage, and union-based portfolio')
    for c,record in cases.items():
        print(c, {r:{'finalDag':v['finalBody']['bodyDag'],'fullDeclarations':v['sizes']['full']['declarations'],
          'fullDag':v['sizes']['full']['bodyDag'],'incrementalDag':v['sizes']['statement-free']['bodyDag']}
          for r,v in record['routes'].items()})

if __name__=='__main__':main()
