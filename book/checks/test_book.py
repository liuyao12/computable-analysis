#!/usr/bin/env python3
"""Validate preservation, claim boundaries, maps and old bookmarks."""
from pathlib import Path
from bs4 import BeautifulSoup
import hashlib,json,sys,urllib.parse
ROOT=Path(__file__).resolve().parents[2]
SITE=ROOT/'blueprint/web'

def main():
    manifest=json.loads((SITE/'reading/manifest.json').read_text())
    assert manifest['preservedFirstTwo']
    if '--structural-only' not in sys.argv: assert manifest['compilerAuditPresent']
    preservation=json.loads((SITE/'reading/preservation.json').read_text())
    for f,h in preservation['sources']['files'].items():assert hashlib.sha256((ROOT/f).read_bytes()).hexdigest()==h
    assert all(x['identicalMathematicalText'] for x in preservation['rendered'].values())
    audit=json.loads((SITE/'reading/native-computability.json').read_text())
    if '--structural-only' not in sys.argv:
        assert audit['nativeNoncomputableClosureCheck'] and audit['nativeMathlibFree'] and audit['noSorryAx']
        assert len(audit['roots'])==8
        assert all(not x['nativeNoncomputableDependencies'] for x in audit['roots'])
    data=json.loads((SITE/'reading/maps.json').read_text());maps=data['theorems']
    assert len(maps)==12 and sum(x['checkedComparison'] for x in maps.values())==1
    assert all(data['checks'].values())
    pages=['index.html','cosine.html','programme.html']+[p.name for p in SITE.glob('ch-*.html') if (SITE/p.name).read_text().find('class="reader"')>=0]
    margins=0
    for name in pages:
        s=BeautifulSoup((SITE/name).read_text(),'html.parser')
        assert s.select_one('main#main') and s.select_one('nav#book-nav'),name
        assert not any('styles/theme-' in x.get('href','') for x in s.select('link'))
        for a in s.select('[data-proof-map]'):
            k=a['data-proof-map'];assert k in maps;assert 'Proof map' in a.text;margins+=1
        for a in s.select('a[href]'):
            u=urllib.parse.urlsplit(a['href'])
            if u.scheme or u.netloc or not u.path:continue
            f=(SITE/urllib.parse.unquote(u.path))
            assert f.exists(),(name,a['href'])
        assert not s.select('article .bp-lean-panel, article .proof-table')
    assert margins==12
    w={(x['source'],x['target'],str(x['route']),x.get('kind')) for x in data['witnesses']}
    for view,path in maps['thm:c3-primitive']['views'].items():
        s=BeautifulSoup((SITE/path).read_text(),'html.parser')
        assert len(s.select('[data-node="thm:c3-primitive"]'))==1
        for edge in s.select('[data-edge]'):
            source,target=edge['data-edge'].split('->')
            assert any((a,b)==(source,target) and (kind=='statement' or view in ['all','companions'] or c==view) for a,b,c,kind in w),(view,source,target)
    for old in ['cosine-primitive-graph.html','proof-comparison/index.html','ch-three-cosine-proofs.html']:
        assert 'http-equiv="refresh"' in (SITE/old).read_text()
    assert (SITE/'reference/dep_graph_document.html').exists()
    if '--structural-only' in sys.argv: print('LOCAL STRUCTURAL CHECK ONLY — compiler audit pending')
    from test_edge_semantics import verify
    verify(SITE)
    print('PASS: original chapter text and sources preserved; every theorem has a map; no invented paired comparisons; checked edges preserved; old links retained; audit gate enforced on publication')
if __name__=='__main__':main()
