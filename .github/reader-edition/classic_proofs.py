#!/usr/bin/env python3
"""Expose checked classical examples and source-linked proof comparisons."""
import argparse,hashlib,json,re,shutil,urllib.request
from pathlib import Path
from bs4 import BeautifulSoup
ROOT=Path(__file__).resolve().parents[2]
SOURCE=ROOT/'book/classics'
MATHLIB='338b8c00bd151fa07a0350cc17442e6eeda734e8'
MATHLIB_PATH='Mathlib/NumberTheory/ZetaValues.lean'
MATHLIB_HASH='27aa982f5c473d7e8c6e6030ead08ffce081a7ff616b2acd9130d04772f8c672'
LINKS=[('cartwright.html',r'Irrationality of \(\pi^2\)'),('leibniz.html','The Leibniz series'),('basel.html','The Basel problem')]
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def verify_mathlib(source_file=None):
    url=f'https://raw.githubusercontent.com/leanprover-community/mathlib4/{MATHLIB}/{MATHLIB_PATH}'
    data=source_file.read_bytes() if source_file else urllib.request.urlopen(url,timeout=60).read()
    assert hashlib.sha256(data).hexdigest()==MATHLIB_HASH
    names=['bernoulliFourierCoeff_recurrence','bernoulliFourierCoeff_eq','hasSum_zeta_nat','hasSum_zeta_two']
    for name in names:assert ('theorem '+name) in data.decode()
    return dict(revision=MATHLIB,path=MATHLIB_PATH,sha256=MATHLIB_HASH,declarations=names,verification='Pinned source inspection; no new Mathlib compilation or cross-foundation bridge claimed')
def install(site,revision,source_file=None):
    assert re.fullmatch('[0-9a-f]{40}',revision)
    assert not (site/'reading/classic-proofs-edition.json').exists()
    mathlib=verify_mathlib(source_file)
    audit=json.loads((site/'reading/cartwright-audit.json').read_text())
    assert audit['finalIrrationalityProved'] and audit['momentIdentityProved'] and all(audit['checks'].values())
    maps=json.loads((site/'reading/maps.json').read_text())
    cartwright=maps['theorems']['thm:cartwright-irrationality']
    assert cartwright['checkedComparison'] and cartwright['page']=='cartwright.html'
    assert len(cartwright['routeNames'])==3
    zeta=json.loads((site/'reading/zeta-real-edition.json').read_text())
    assert zeta['baselProved']
    leibniz=json.loads((site/'reading/leibniz-graph-publication.json').read_text())
    assert leibniz['mathlibProofRevision']==MATHLIB
    before={str(p.relative_to(site)):digest(p) for p in site.rglob('*') if p.is_file()}
    repo=f'https://github.com/liuyao12/computable-analysis/blob/{revision}/'
    native=repo+'ComputableAnalysis/'
    ml=f'https://github.com/leanprover-community/mathlib4/blob/{MATHLIB}/'
    template=(site/'cosine.html').read_text()
    for name,title in [('leibniz','The Leibniz series'),('basel','The Basel problem')]:
        doc=BeautifulSoup(template,'html.parser');doc.title.string=title+' · Computable Analysis'
        doc.select_one('meta[name="documentation-revision"]')['content']=revision
        page=(SOURCE/(name+'.html')).read_text().replace('__NATIVE__',native).replace('__MATHLIB__',ml).replace('__REPO__',repo)
        doc.article.clear()
        for node in list(BeautifulSoup(page,'html.parser').contents):doc.article.append(node)
        toc=doc.select_one('.on-this-page')
        if toc:
            toc.clear()
            for heading in doc.article.select('h2[id]'):
                a=doc.new_tag('a',href='#'+heading['id']);a.string=heading.get_text();toc.append(a)
        doc.head.append(doc.new_tag('link',rel='stylesheet',href='reading/classics.css'))
        if name=='basel':doc.head.append(doc.new_tag('script',src='reading/classics.js',defer=''))
        footer=doc.select_one('.chapter-footer a')
        if footer:footer['href']=repo+'book/classics/'+name+'.html';footer.string='Source '+revision[:8]+' ↗'
        (site/(name+'.html')).write_text(str(doc))
    navigation=[]
    for p in site.rglob('*.html'):
        if 'reference' in p.parts:continue
        original=p.read_text()
        match=re.search(r'<nav\b[^>]*\bid="book-nav"[^>]*>[\s\S]*?</nav>',original)
        if not match:continue
        nav=BeautifulSoup(match.group(),'html.parser').nav
        marker=next(s for s in nav.select('.nav-label') if s.get_text()=='The development')
        prefix='../' if nav.select_one('a[href="../cosine.html"]') else ''
        for span in nav.select('.nav-label'):
            if span.get_text()=='A worked comparison':span.string='Worked examples'
        for href,title in LINKS:
            a=BeautifulSoup(f'<a class="classic-navigation" href="{prefix+href}">{title}</a>','html.parser').a
            marker.insert_before(a)
        if p.name in ['cartwright.html','leibniz.html','basel.html']:
            for a in nav.select('a.current'):a['class']=[c for c in a.get('class',[]) if c!='current'];a.attrs.pop('aria-current',None)
            active=nav.select_one(f'a[href="{prefix+p.name}"]');active['class']=active.get('class',[])+['current'];active['aria-current']='page'
        updated=original[:match.start()]+str(nav)+original[match.end():]
        p.write_text(updated);navigation.append(str(p.relative_to(site)))
    shutil.copyfile(SOURCE/'classics.css',site/'reading/classics.css')
    shutil.copyfile(SOURCE/'classics.js',site/'reading/classics.js')
    after={str(p.relative_to(site)):digest(p) for p in site.rglob('*') if p.is_file()}
    changed={p:dict(before=h,after=after[p]) for p,h in before.items() if h!=after[p]}
    assert all(p.endswith('.html') for p in changed)
    report=dict(documentationRevision=revision,cartwrightProofRevision=audit['sourceCommit'],
      nativeSeriesProofRevision=revision,mathlib=mathlib,navigationPages=navigation,
      pages=[p for p,t in LINKS],changedArtifacts=changed,
      protectedArtifacts={p:h for p,h in before.items() if p not in changed},
      artifacts={p:h for p,h in after.items() if p not in before or p in changed},
      checks=dict(cartwrightAlreadyProved=True,cartwrightThreeCheckedRoutesPreserved=True,leibnizComparisonPreserved=True,baselNativeAudited=True,mathlibSourcePinned=True),
      newLeanProofsClaimed=False,baselCrossFoundationBridgeChecked=False)
    (site/'reading/classic-proofs-edition.json').write_text(json.dumps(report,indent=2)+'\n')
    print(f'PASS: three classical examples in {len(navigation)} sidebars; preserved checked comparisons and pinned Basel source')
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--site',required=True,type=Path);p.add_argument('--revision',required=True);p.add_argument('--mathlib-source',type=Path)
    a=p.parse_args();install(a.site,a.revision,a.mathlib_source)
