#!/usr/bin/env python3
"""Publish a source-linked mathematical map without changing existing proof maps."""
import argparse
import hashlib
import html
import json
import re
import shutil
import textwrap
from pathlib import Path

SOURCE = Path(__file__).with_name('leibniz-graph')
PAGE = 'leibniz-proofs.html'
START = '<!-- leibniz-three-proofs:start -->'
END = '<!-- leibniz-three-proofs:end -->'
ADDITION = re.compile(re.escape(START) + r'[\s\S]*?' + re.escape(END))

def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def validate(model):
    nodes = {n['id']: n for n in model['nodes']}
    assert len(nodes) == len(model['nodes']) == 17
    assert len(model['edges']) == len({(e['source'],e['target']) for e in model['edges']})
    for e in model['edges']:
        a,b = nodes[e['source']],nodes[e['target']]
        assert a['row'] < b['row'], 'A dependency must precede its conclusion'
        assert set(a['routes']) & set(b['routes']), 'No cross-foundation dependency'
    for n in model['nodes']:
        assert n['body'] and n['formula'] and n['refs']
        for ref in n['refs']:
            revision = model['mathlibRevision'] if 'leanprover-community' in ref['url'] else model['caRevision']
            assert '/blob/'+revision+'/' in ref['url']
    return nodes

def overview(model):
    """Static SVG remains usable without JavaScript and links to the explorable map."""
    ns=validate(model);esc=html.escape
    positions={n['id']:(18+n['col']*318,30+n['row']*133,606 if n['span']==2 else 288,104) for n in model['nodes']}
    parts=['<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 960 833" role="img" aria-labelledby="title desc"><title id="title">Three proofs of the Leibniz formula</title><desc id="desc">Rational interval arguments and polynomial FTC lead independently to geometric pi. Mathlib uses real and complex analysis and Abel’s endpoint theorem.</desc><defs><marker id="a" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="6" markerHeight="6" orient="auto"><path d="M0 0L10 5L0 10z" fill="#82958a"/></marker></defs>']
    for r in model['routes']:
        parts.append(f'<text x="{24+r["id"]*318}" y="16" font-family="sans-serif" font-size="10" fill="#587365">{esc(r["name"].upper())}</text>')
    for i,e in enumerate(model['edges']):
        x,y,w,h=positions[e['source']];X,Y,W,H=positions[e['target']]
        ax,ay,bx,by=x+w/2,y+h+1,X+W/2,Y-3
        if by-ay<123:
            d=f'M{ax} {ay}C{ax} {ay+14} {bx} {by-14} {bx} {by}'
        else:
            channel=max(x+w,X+W)+7 if i%2==0 else min(x,X)-7
            d=f'M{ax} {ay}L{ax} {ay+9}L{channel} {ay+9}L{channel} {by-10}L{bx} {by-10}L{bx} {by}'
        parts.append(f'<path d="{d}" fill="none" stroke="#bec8bf" stroke-width="1.25" marker-end="url(#a)"/>')
    for n in model['nodes']:
        x,y,w,h=positions[n['id']]
        color,stroke=('#f1f4ed','#adbaa9') if len(n['routes'])>1 else [('#eff5ef','#779784'),('#eef4f7','#89a8ba'),('#f4eff8','#b2a0c3')][n['routes'][0]]
        parts.append(f'<g transform="translate({x},{y})"><rect width="{w}" height="{h}" rx="7" fill="{color}" stroke="{stroke}"/><text x="14" y="20" font-family="sans-serif" font-size="9" fill="#647267">{esc(n["tag"].upper())}</text>')
        titles=textwrap.wrap(n['title'],60 if w>400 else 33,break_long_words=False)
        for i,t in enumerate(titles):
            parts.append(f'<text x="14" y="{43+i*19}" font-family="Georgia,serif" font-size="15" fill="#213c2e">{esc(t)}</text>')
        for i,t in enumerate(textwrap.wrap(n['subtitle'],75 if w>400 else 43,break_long_words=False)):
            parts.append(f'<text x="14" y="{80+i*14 if len(titles)>1 else 68+i*14}" font-family="sans-serif" font-size="10" fill="#647267">{esc(t)}</text>')
        parts.append('</g>')
    return ''.join(parts)+'</svg>'

def install(site, revision):
    assert re.fullmatch('[0-9a-f]{40}', revision)
    model=json.loads((SOURCE/'model.json').read_text());validate(model)
    page=site/'ch-infinite-series.html';metadata=site/'reading/leibniz-benchmark.json'
    original=page.read_text()
    previous_report=site/'reading/leibniz-graph-publication.json'
    if previous_report.exists():
        report=json.loads(previous_report.read_text())
        assert report['documentationRevision']==revision, 'Rebuild from the pinned reader artifact for a new revision'
        assert digest(page)==report['chapterSha256']
        assert all(digest(site/p)==h for p,h in report['artifactHashes'].items())
        return report
    protected={str(p.relative_to(site)):digest(p) for p in site.rglob('*') if p.is_file() and p not in [page,metadata]}
    start=original.index('<section id="leibniz-geometric-benchmark"')
    end=original.index('</section>',start)
    section=original[start:end]
    old=re.search(r'<pre\b[^>]*>[\s\S]*?</pre>',section)
    assert old
    figure=START+'''<figure style="margin:24px 0"><a href="leibniz-proofs.html" aria-label="Explore the three Leibniz proof routes"><img src="reading/leibniz-overview.svg" alt="Dependency graph: computational and FTC routes share rational foundations and geometric pi; Mathlib uses completed reals, the arctangent series and Abel’s theorem." width="960" height="833" style="display:block;width:100%;height:auto"></a><figcaption style="font-size:14px;margin-top:12px"><a href="leibniz-proofs.html">Explore all three proofs →</a> Select mathematical bundles, follow each route, and open its source references.</figcaption></figure>'''+END
    pos=start+old.start();stop=start+old.end()
    updated=original[:pos]+figure+original[stop:]
    assert updated.replace(figure,old.group(),1)==original
    out=site/'reading';out.mkdir(exist_ok=True)
    outline=[]
    for n in model['nodes']:
        refs=' · '.join(f'<a href="{html.escape(r["url"],quote=True)}">{html.escape(r["label"])}</a>' for r in n['refs'])
        outline.append(f'<article id="outline-{n["id"]}"><p class="eyebrow">{html.escape(n["tag"])}</p><h3>{html.escape(n["title"])}</h3><p class="formula">{html.escape(n["formula"])}</p><p>{html.escape(n["body"])}</p><p class="refs">{refs}</p></article>')
    body=(SOURCE/'page.html').read_text()
    replacements={'__OUTLINE__':''.join(outline),'__CA__':model['caRevision'],'__ML__':model['mathlibRevision'],'__CA_SHORT__':model['caRevision'][:8],'__ML_SHORT__':model['mathlibRevision'][:8],'__SCOPE__':html.escape(model['edgeSemantics'])+' The native proof separation is audited; the Mathlib outline is based on the pinned source. No new Lean theorem is claimed by this visualization.'}
    for a,b in replacements.items():body=body.replace(a,b)
    body=body.replace('</body>','<script type="application/json" id="graph-data">'+json.dumps(model,ensure_ascii=False).replace('<','\\u003c')+'</script></body>')
    (site/PAGE).write_text(body)
    for name in ['css','js']:shutil.copyfile(SOURCE/f'graph.{name}',out/f'leibniz-graph.{name}')
    (out/'leibniz-graph.json').write_text(json.dumps(model,ensure_ascii=False,indent=2)+'\n')
    (out/'leibniz-overview.svg').write_text(overview(model))
    page.write_text(updated)
    benchmark=json.loads(metadata.read_text());benchmark.update(interactiveGraphAdded=True,pageSha256=digest(page),graphPage=PAGE)
    metadata.write_text(json.dumps(benchmark,indent=2)+'\n')
    assert all(digest(site/p)==h for p,h in protected.items()), 'Unrelated reader artifact changed'
    artifacts=[PAGE]+['reading/leibniz-'+s for s in ['graph.css','graph.js','graph.json','overview.svg']]
    report=dict(documentationRevision=revision,caProofRevision=model['caRevision'],mathlibProofRevision=model['mathlibRevision'],page=PAGE,bundleCount=len(model['nodes']),edgeCount=len(model['edges']),mathematicalOutline=True,extractedDeclarationGraph=False,newLeanProofsClaimed=False,previousChapterSha256=hashlib.sha256(original.encode()).hexdigest(),chapterSha256=digest(page),artifactHashes={p:digest(site/p) for p in artifacts},protectedArtifactHashes=protected,checks=dict(priorChapterOutsideDiagramPreserved=True,existingProofMapsUnchanged=True,pinnedSources=True,acyclicDependencies=True,noCrossFoundationEdges=True))
    previous_report.write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: 17 mathematical bundles, 3 routes; prior chapter prose and proof maps preserved')
    return report

if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--site',type=Path,required=True);parser.add_argument('--revision',required=True)
    args=parser.parse_args();install(args.site,args.revision)
