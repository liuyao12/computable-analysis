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
EULER_MATHLIB='51e6992efd06126df61a496bebf8f49482a4e129'
LINKS=[('cartwright.html',r'Irrationality of \(\pi^2\)'),('leibniz.html','The Leibniz series'),('basel.html','The Basel problem'),('euler.html','Euler’s sine product'),('arctan-taylor.html','Arctangent and Taylor series')]
ODE_LINKS=[('complex-analysis.html', 'Polygonal Cauchy theory'), ('fuchs.html', 'Fuchs’s theorem'), ('painleve.html', 'Painlevé’s classification')]
LINKS += ODE_LINKS
SHOWCASE_PAGES = ['cosine.html', 'integral-families.html'] + [href for href, _ in LINKS]
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def verify_mathlib(source_file=None):
    url=f'https://raw.githubusercontent.com/leanprover-community/mathlib4/{MATHLIB}/{MATHLIB_PATH}'
    data=source_file.read_bytes() if source_file else urllib.request.urlopen(url,timeout=60).read()
    assert hashlib.sha256(data).hexdigest()==MATHLIB_HASH
    names=['bernoulliFourierCoeff_recurrence','bernoulliFourierCoeff_eq','hasSum_zeta_nat','hasSum_zeta_two']
    for name in names:assert ('theorem '+name) in data.decode()
    return dict(revision=MATHLIB,path=MATHLIB_PATH,sha256=MATHLIB_HASH,declarations=names,verification='Pinned source inspection; no new Mathlib compilation or cross-foundation bridge claimed')
def install(site,revision,euler_audit,cauchy_audit,arctan_audit,source_file=None):
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
    euler=json.loads(euler_audit.read_text())
    assert euler['mathlibRevision']==EULER_MATHLIB and all(euler['checks'].values())
    assert len(euler['declarations'])==15 and euler['allPositiveEvenValuesProved'] and euler['dependencyCount']>0
    for name,h in euler['sourceHashes'].items():assert digest(ROOT/'book/euler-proof'/name)==h,name
    assert {r['name'] for r in euler['declarations']} >= {'EulerBasel.hasSum_reciprocal_squares','EulerBasel.coefficient_error','EulerEven.hasSum_even_zeta','EulerEven.hasSum_four','EulerEven.hasSum_six','EulerEven.hasSum_eight'}
    for row in euler['declarations']:assert set(row['axioms'])<= {'propext','Classical.choice','Quot.sound'}
    cauchy_log=cauchy_audit.read_text()
    assert 'PASS: polygonal Cauchy cancellation and local square residues' in cauchy_log
    assert 'PASS: no Mathlib module in the import closure; no sorryAx' in cauchy_log
    assert not re.search(r'\berror:|^AUDIT.*sorryAx', cauchy_log, re.M)
    arctan_log=arctan_audit.read_text()
    assert 'PASS: arctangent Taylor convergence and divergence' in arctan_log
    assert 'PASS: no Mathlib imports or sorryAx in arctangent audit' in arctan_log
    assert not re.search(r'\berror:', arctan_log)
    before={str(p.relative_to(site)):digest(p) for p in site.rglob('*') if p.is_file()}
    repo=f'https://github.com/liuyao12/computable-analysis/blob/{revision}/'
    native=repo+'ComputableAnalysis/'
    ml=f'https://github.com/leanprover-community/mathlib4/blob/{MATHLIB}/'
    template=(site/'cosine.html').read_text()
    for name,title in [('leibniz','The Leibniz series'),('basel','The Basel problem'),('euler','Euler’s sine-product proof'),('fuchs','Fuchs’s theorem'),('painleve','Painlevé’s classification'),('complex-analysis','Polygonal Cauchy theory'),('arctan-taylor','Arctangent: where Taylor stops')]:
        doc=BeautifulSoup(template,'html.parser');doc.title.string=title+' · Computable Analysis'
        doc.select_one('meta[name="documentation-revision"]')['content']=revision
        page=(SOURCE/(name+'.html')).read_text().replace('__NATIVE__',native).replace('__MATHLIB__',ml).replace('__REPO__',repo).replace('__EULER_MATHLIB__',f'https://github.com/leanprover-community/mathlib4/blob/{EULER_MATHLIB}/')
        doc.article.clear()
        for node in list(BeautifulSoup(page,'html.parser').contents):doc.article.append(node)
        toc=doc.select_one('.on-this-page')
        if toc:
            toc.clear()
            for heading in doc.article.select('h2[id]'):
                a=doc.new_tag('a',href='#'+heading['id']);a.string=heading.get_text();toc.append(a)
        doc.head.append(doc.new_tag('link',rel='stylesheet',href='reading/classics.css'))
        if name=='complex-analysis':
            doc.body['class']=doc.body.get('class',[])+['cauchy-page']
            doc.select_one('.page').append(BeautifulSoup((SOURCE/'cauchy-example.html').read_text(),'html.parser'))
            doc.head.append(doc.new_tag('link',rel='stylesheet',href='reading/cauchy-example.css'))
            doc.head.append(doc.new_tag('script',src='reading/cauchy-example.js',defer=''))
        if name=='arctan-taylor':
            doc.body['class']=doc.body.get('class',[])+['cauchy-page','arctan-page']
            doc.select_one('.page').append(BeautifulSoup((SOURCE/'arctan-example.html').read_text(),'html.parser'))
            for asset in ['cauchy-example.css','arctan-example.css']:
                doc.head.append(doc.new_tag('link',rel='stylesheet',href='reading/'+asset))
            doc.head.append(doc.new_tag('script',src='reading/arctan-example.js',defer=''))
        if name=='basel':doc.head.append(doc.new_tag('script',src='reading/classics.js',defer=''))
        footer=doc.select_one('.chapter-footer a')
        if footer:footer['href']=repo+'book/classics/'+name+'.html';footer.string='Source '+revision[:8]+' ↗'
        (site/(name+'.html')).write_text(str(doc))
    # Pinned reader pages retain their proof anchors and audited comparison data.
    # Their editable introductions live here, alongside the other showcase sources.
    for fragment in sorted((SOURCE/'statements').glob('*.html')):
        path=site/fragment.name
        doc=BeautifulSoup(path.read_text(),'html.parser')
        lead=doc.article.select_one('.lead')
        if fragment.name=='cosine.html':
            for node in list(lead.next_siblings):
                if getattr(node,'name',None)=='h2':break
                node.extract()
        elif fragment.name=='cartwright.html':
            for node in doc.article.find_all(string=True):
                if 'π' in node:node.replace_with(str(node).replace('π squared',r'\(\pi^2\)').replace('π',r'\(\pi\)'))
        cursor=lead
        for node in list(BeautifulSoup(fragment.read_text(),'html.parser').contents):
            cursor.insert_after(node);cursor=node
        doc.select_one('meta[name="documentation-revision"]')['content']=revision
        path.write_text(str(doc))
    for name in SHOWCASE_PAGES:
        path=site/name;doc=BeautifulSoup(path.read_text(),'html.parser')
        assert doc.select_one('.showcase-statement') and doc.select_one('#setup')
        toc=doc.select_one('.on-this-page')
        if toc:
            toc.clear()
            for heading in doc.article.select('h2[id]'):
                a=doc.new_tag('a',href='#'+heading['id']);a.string=heading.get_text();toc.append(a)
        if not doc.select_one('link[href="reading/classics.css"]'):
            doc.head.append(doc.new_tag('link',rel='stylesheet',href='reading/classics.css'))
        path.write_text(str(doc))
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
            if href in ['arctan-taylor.html','fuchs.html']:
                label=BeautifulSoup('<span class="nav-label">'+('Function theory' if href=='arctan-taylor.html' else 'Differential equations')+'</span>','html.parser').span
                marker.insert_before(label)
            a=BeautifulSoup(f'<a class="classic-navigation" href="{prefix+href}">{title}</a>','html.parser').a
            marker.insert_before(a)
        if p.name in [href for href,_ in LINKS]:
            for a in nav.select('a.current'):a['class']=[c for c in a.get('class',[]) if c!='current'];a.attrs.pop('aria-current',None)
            active=nav.select_one(f'a[href="{prefix+p.name}"]');active['class']=active.get('class',[])+['current'];active['aria-current']='page'
        updated=original[:match.start()]+str(nav)+original[match.end():]
        p.write_text(updated);navigation.append(str(p.relative_to(site)))
    for asset in ['cauchy-example.css','cauchy-example.js','arctan-example.css','arctan-example.js']:
        shutil.copyfile(SOURCE/asset,site/'reading'/asset)
    shutil.copyfile(arctan_audit,site/'reading/arctan-taylor-audit.log')
    shutil.copyfile(cauchy_audit,site/'reading/polygonal-cauchy-audit.log')
    shutil.copyfile(SOURCE/'classics.css',site/'reading/classics.css')
    shutil.copyfile(SOURCE/'classics.js',site/'reading/classics.js')
    shutil.copyfile(euler_audit,site/'reading/euler-proofs.json')
    shutil.copyfile(euler_audit.with_name('dependencies.txt'),site/'reading/euler-dependencies.txt')
    shutil.copyfile(euler_audit.with_name('general-dependencies.txt'),site/'reading/euler-general-dependencies.txt')
    after={str(p.relative_to(site)):digest(p) for p in site.rglob('*') if p.is_file()}
    changed={p:dict(before=h,after=after[p]) for p,h in before.items() if h!=after[p]}
    assert all(p.endswith('.html') for p in changed)
    report=dict(documentationRevision=revision,cartwrightProofRevision=audit['sourceCommit'],
      nativeSeriesProofRevision=revision,mathlib=mathlib,navigationPages=navigation,
      pages=SHOWCASE_PAGES,changedArtifacts=changed,
      protectedArtifacts={p:h for p,h in before.items() if p not in changed},
      artifacts={p:h for p,h in after.items() if p not in before or p in changed},
      checks=dict(cartwrightAlreadyProved=True,cartwrightThreeCheckedRoutesPreserved=True,leibnizComparisonPreserved=True,baselNativeAudited=True,mathlibSourcePinned=True,eulerProofAudited=True,allEvenZetaValuesAudited=True,polygonalCauchyAudited=True,arctanTaylorAudited=True),
      newLeanProofsClaimed=True,eulerMathlibRevision=EULER_MATHLIB,baselCrossFoundationBridgeChecked=False)
    (site/'reading/classic-proofs-edition.json').write_text(json.dumps(report,indent=2)+'\n')
    print(f'PASS: classical examples and differential-equation theorems in {len(navigation)} sidebars; preserved checked comparisons and pinned Basel source')
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--site',required=True,type=Path);p.add_argument('--revision',required=True);p.add_argument('--mathlib-source',type=Path);p.add_argument('--euler-audit',required=True,type=Path);p.add_argument('--cauchy-audit',required=True,type=Path);p.add_argument('--arctan-audit',required=True,type=Path)
    a=p.parse_args();install(a.site,a.revision,a.euler_audit,a.cauchy_audit,a.arctan_audit,a.mathlib_source)
