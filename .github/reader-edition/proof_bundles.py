#!/usr/bin/env python3
"""Publish bundled proof routes and reproducible, source-linked LOC inventories."""
import argparse,base64,hashlib,html,json,re,shutil,urllib.request
from pathlib import Path
from bs4 import BeautifulSoup
from zeta_zero_benchmark import uncomment
ROOT=Path(__file__).resolve().parents[2]
ASSETS=ROOT/'book/proof-bundles'
ML='51e6992efd06126df61a496bebf8f49482a4e129'


def decode_record(record):
    bits=base64.b64decode(record['codeLineBitmap'])
    return {i+1 for i in range(record['physicalLines']) if bits[i//8] & (1 << (i%8))}


def source_record(data):
    physical=len(data.decode().splitlines());lines=uncomment(data.decode()).splitlines();bits=bytearray((physical+7)//8)
    for i,line in enumerate(lines):
        if line.strip():bits[i//8]|=1 << (i%8)
    return dict(sha256=hashlib.sha256(data).hexdigest(),physicalLines=physical,
                codeLines=sum(bool(line.strip()) for line in lines),codeLineBitmap=base64.b64encode(bits).decode())


def references(urls):
    out=[]
    for item in urls:
        url=item['url'] if isinstance(item,dict) else item
        match=re.fullmatch(r'(https://github.com/[^/]+/[^/]+/blob/[^/]+/[^#]+)(?:#L(\d+)(?:-L(\d+))?)?',url)
        assert match,url
        start,end=match[2],match[3]
        # A start-only link identifies a source, not the end of its declaration.
        out.append(dict(url=match[1],label=item.get('label',Path(match[1]).name) if isinstance(item,dict) else Path(match[1]).name,
                        start=int(start) if end else None,end=int(end) if end else None))
    return out


def measure(refs,sources):
    selected={}
    for ref in refs:
        if ref['url'] not in sources:continue
        record=sources[ref['url']];code=decode_record(record)
        if ref['start'] is not None:
            assert 1<=ref['start']<=ref['end']<=record['physicalLines'],ref
            code &= set(range(ref['start'],ref['end']+1))
        selected.setdefault(ref['url'],set()).update(code)
    missing=sum(r['url'] not in sources for r in refs)
    return dict(codeLines=sum(map(len,selected.values())) if refs and not missing else None,
                measuredSources=len(selected),unmeasuredSources=missing,
                scope='Source files' if any(r['start'] is None for r in refs) else 'Linked declaration spans',
                spans=refs)


def union_measure(nodes,sources):
    refs=[r for n in nodes for r in n['loc']['spans']]
    result=measure(refs,sources)
    result['pendingBundles']=sum(n['status']=='pending' for n in nodes)
    result['unmeasuredBundles']=sum(n['loc']['codeLines'] is None for n in nodes)
    return result


def registered_graphs(site):
    model=json.loads((site/'reading/maps.json').read_text());graphs=[]
    for key,entry in model['theorems'].items():
        routes=[];nodes=[];edges=[]
        if entry.get('views') and (entry.get('checkedComparison') or entry.get('verifiedGraph')):
            views={r:BeautifulSoup((site/path).read_text(),'html.parser') for r,path in entry['views'].items()}
            route_ids=[r for r in views if r.isdigit()]
            if not route_ids:route_ids=['0']
            names=entry.get('routeNames',['Registered proof'])
            routes=[dict(id=r,name=(names[int(r)] if int(r)<len(names) and names[int(r)] else 'Registered proof'),status='registered') for r in route_ids]
            for element in views['all'].select('[data-node]'):
                node_id=element['data-node'];bundle=model['bundles'][node_id]
                rs=[r for r in route_ids if r not in views or views[r].select_one('[data-node="'+node_id+'"]')]
                refs=references([dict(url=d['sourceUrl'],label=d['name']) for d in bundle.get('declarations',[]) if d.get('sourceUrl')])
                nodes.append(dict(id=node_id,title=bundle['title'].replace(' (ℚ)','').replace('π','circle constant'),body=('Rational projection and polygon enclosures construct the geometric sector before a general integral.' if node_id=='def:c3-arctan' else bundle.get('strategy',{}).get('summary','Source-linked mathematical dependency bundle.')),mathHtml=bundle.get('mathHtml',''),status='registered',routes=rs,sources=refs,declarations=[d['name'] for d in bundle.get('declarations',[])],boundary=bundle.get('formalizationBoundary','')))
            edges=[dict(source=e['data-edge'].split('->')[0],target=e['data-edge'].split('->')[1],kind='registered') for e in views['all'].select('[data-edge]')]
        else:
            routes=[dict(id='0',name='Manuscript argument',status='outline')]
            for n in entry.get('nodes',[]):nodes.append(dict(id=n['id'],title=n['title'],body=n.get('text',''),mathHtml=n.get('mathHtml',''),status='pending',routes=['0'],sources=[],declarations=[]))
            edges=[dict(source=s,target=t,kind='outline') for s,t in entry.get('edges',[])]
        if not any('Mathlib' in r['name'] for r in routes):
            routes.append(dict(id='mathlib',name='Mathlib comparison',status='pending'))
            nodes.append(dict(id='mathlib-pending',title='Mathlib comparison not registered',body='No paired Mathlib proof is registered for this exact statement in this catalogue. This is a missing comparison, not an assertion that the library has no related theorem.',status='pending',routes=['mathlib'],sources=[],declarations=[]))
        if len([r for r in routes if r['id']!='mathlib'])==1:
            routes.append(dict(id='alternative',name='Alternative proof',status='pending'))
            nodes.append(dict(id='alternative-pending',title='Alternative proof not registered',body='An independent proof route for this exact statement remains to be supplied.',status='pending',routes=['alternative'],sources=[],declarations=[]))
        graphs.append(dict(id=key,title=entry['title'].replace('π','circle constant'),page=entry['page'],anchor=entry['id'],status=entry['status'],edgeSemantics='Registered arrows retain the existing bundled dependency map; outline arrows describe a strategy, not a checked Lean dependency.',routes=routes,nodes=nodes,edges=edges))
    return graphs


def curated_graphs(revision):
    spec=json.loads((ASSETS/'catalogue.json').read_text())
    prefix='https://github.com/liuyao12/computable-analysis/blob/'+revision+'/'
    ml='https://github.com/leanprover-community/mathlib4/blob/'+ML+'/'
    for graph in spec:
        for n in graph['nodes']:
            n['sources']=references([dict(url=p if p.startswith('https://') else (ml if p.startswith('Mathlib/') else prefix)+p,label=Path(p).name) for p in n.pop('files',[])])
            n.setdefault('declarations',[])
    return spec


def leibniz_graph(site):
    m=json.loads((site/'reading/leibniz-graph.json').read_text())
    return dict(id='showcase:leibniz',title='The Leibniz series',page='leibniz.html',anchor='theorem',status='Three audited native routes and a pinned Mathlib source comparison',edgeSemantics=m['edgeSemantics'],routes=[dict(id=str(r['id']),name=r['name'],status='registered') for r in m['routes']],nodes=[dict(id=n['id'],title=n['title'].replace('π','circle constant'),body='This bundle contributes to the '+', '.join(r['name'] for r in m['routes'] if r['id'] in n['routes'])+' route. The maintained Leibniz comparison gives the detailed mathematical strategy; the sources counted here are listed below.',status='registered',routes=list(map(str,n['routes'])),sources=references(n['refs']),declarations=[]) for n in m['nodes']],edges=[dict(**e,kind='outline') for e in m['edges']])


def build_catalogue(site,revision):
    sources=json.loads((ASSETS/'source-inventory.json').read_text())['sources']
    graphs=registered_graphs(site)+[leibniz_graph(site)]+curated_graphs(revision)
    for g in graphs:
        ids={n['id'] for n in g['nodes']};assert len(ids)==len(g['nodes'])
        for e in g['edges']:assert e['source'] in ids and e['target'] in ids
        for n in g['nodes']:
            for ref in n['sources']:
                prefix='https://github.com/liuyao12/computable-analysis/blob/'+revision+'/'
                if ref['url'].startswith(prefix):sources[ref['url']]=source_record((ROOT/ref['url'][len(prefix):]).read_bytes())
            n['loc']=measure(n['sources'],sources)
        for route in g['routes']:route['loc']=union_measure([n for n in g['nodes'] if route['id'] in n['routes']],sources)
        g['loc']=union_measure(g['nodes'],sources)
    used={r['url'] for g in graphs for n in g['nodes'] for r in n['sources']}
    return dict(schemaVersion=1,documentationRevision=revision,graphs=graphs,sources={u:sources[u] for u in sorted(used) if u in sources},metric='Nonblank physical Lean source lines, excluding nested comments. Explicit declaration spans where recorded; otherwise the whole named file. Union spans before adding route totals. Imported files are not automatically included.',warning='LOC is source inventory, not kernel proof size or proof verification. Unknown and pending are not zero. File inventories include unrelated declarations; analogous Mathlib theorems can have different hypotheses and foundations.')


def install(site,revision):
    catalogue=build_catalogue(site,revision)
    out=site/'reading';out.mkdir(exist_ok=True)
    (out/'proof-bundles.json').write_text(json.dumps(catalogue,ensure_ascii=False,indent=2)+'\n')
    doc=BeautifulSoup((site/'cosine.html').read_text(),'html.parser')
    doc.title.string='Bundled proof comparisons · Computable Analysis'
    doc.body['class']=doc.body.get('class',[])+['proof-bundles-page']
    for el in doc.select('.on-this-page,.chapter-rail,.chapter-footer'):el.decompose()
    for el in doc.select('script[src]'):
        if not any(x in el['src'] for x in ['mathjax','tex-mml','reader.js','book.js','math-setup']):el.decompose()
    for active in doc.select('#book-nav a.current'):
        active['class']=[v for v in active.get('class',[]) if v!='current'];active.attrs.pop('aria-current',None)
    nav=doc.select_one('#book-nav')
    if nav:
        active=nav.select_one('a[href="proof-bundles.html"]')
        if active is None:
            active=doc.new_tag('a',href='proof-bundles.html');active.string='Bundled proof comparisons';nav.append(active)
        active['class']=active.get('class',[])+['current'];active['aria-current']='page'
    kicker=doc.select_one('.chapter-kicker')
    if kicker:kicker.string='Proof comparisons'
    doc.article.clear();doc.article.append(BeautifulSoup((ASSETS/'viewer.html').read_text(),'html.parser'))
    doc.head.append(doc.new_tag('link',rel='stylesheet',href='reading/proof-bundles.css'))
    doc.head.append(doc.new_tag('script',src='reading/proof-bundles.js',defer=''))
    script=doc.new_tag('script',type='application/json',id='proof-bundle-data');script.string=json.dumps(catalogue,ensure_ascii=False).replace('<',r'\u003c');doc.body.append(script)
    doc.select_one('meta[name="documentation-revision"]')['content']=revision
    (site/'proof-bundles.html').write_text(str(doc))
    for name in ['css','js']:shutil.copyfile(ASSETS/('viewer.'+name),out/('proof-bundles.'+name))
    attach_links(site,catalogue)
    print('PASS:',len(catalogue['graphs']),'bundled theorem comparisons;',sum(len(g['nodes']) for g in catalogue['graphs']),'nodes')
    return catalogue


def attach_links(site,catalogue=None,pages=None):
    if catalogue is None:catalogue=json.loads((site/'reading/proof-bundles.json').read_text())
    for g in catalogue['graphs']:
        if pages is not None and g['page'] not in pages:continue
        page=site/g['page']
        if not page.is_file():
            assert g['page'] in {'gaussian-convolution.html','n-ball-volume.html'},g['page']
            continue
        d=BeautifulSoup(page.read_text(),'html.parser')
        if d.select_one('[data-bundled-theorem="'+g['id']+'"]'):continue
        anchor=d.select_one('[id="'+g['anchor']+'"]')
        if anchor is None:anchor=d.select_one('.showcase-statement') or d.article or d.body
        link=d.new_tag('p',attrs={'class':'bundled-proof-link','data-bundled-theorem':g['id']})
        a=d.new_tag('a',href='proof-bundles.html?theorem='+g['id']);a.string='Bundled proof routes and LOC →';link.append(a)
        if anchor.name in ['body','article']:anchor.append(link)
        else:
            parent=anchor.find_parent(class_='showcase-statement')
            (parent or anchor).insert_after(link)
        page.write_text(str(d))

def verify_sources(catalogue):
    from concurrent.futures import ThreadPoolExecutor
    def verify(pair):
        url,record=pair;raw=url.replace('https://github.com/','https://raw.githubusercontent.com/').replace('/blob/','/')
        for attempt in range(3):
            try:
                data=urllib.request.urlopen(raw,timeout=25).read();break
            except Exception:
                if attempt==2:raise
        assert source_record(data)==record,url
    with ThreadPoolExecutor(max_workers=8) as executor:list(executor.map(verify,catalogue['sources'].items()))


if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--site',required=True,type=Path);p.add_argument('--revision',required=True);p.add_argument('--verify-sources',action='store_true');a=p.parse_args()
    c=install(a.site,a.revision)
    if a.verify_sources:verify_sources(c)
