#!/usr/bin/env python3
"""Place and expand the Chapter 1 pi flashcards after the baseline reader pass.
Keep proof data, the original chapter mathematics and worked cosine unchanged.
"""
from __future__ import annotations
import argparse,hashlib,json,re
from pathlib import Path
from bs4 import BeautifulSoup
from pi_flashcards import install

DESTINATION='ch-foundations.html#pi-computations'
OTHER='rem:sources-of-raw-reals'
def parse(text):return BeautifulSoup(text,'html.parser')
def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def mathematical_text(doc):
    article=parse(str(doc.article))
    for item in article.select('#pi-computations'):item.decompose()
    article.find(id=OTHER).string='1.2.2 Other computations of numbers'
    return re.sub(r'\s+',' ',article.get_text(' ',strip=True))

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--site',type=Path,required=True);ap.add_argument('--revision',required=True)
    args=ap.parse_args();site=args.site
    report_path=site/'reading/analysis-edition.json';report=json.loads(report_path.read_text())
    assert report['proofDeclarationsAndEdgesUnchanged']
    protected=dict(report['protectedArtifacts'])
    for name in ['reading/maps.json','reading/animations/cosine.gif','reading/animations/cosine.png','reading/cosine-half-interval.json']:
        protected[name]=sha(site/name)
    worked={name:str(parse((site/name).read_text()).article) for name in ['cosine.html','dyadic-integral.html']}
    chapter_path=site/'ch-foundations.html';chapter=parse(chapter_path.read_text())
    before=mathematical_text(chapter);other=chapter.find(id=OTHER);gallery=chapter.select_one('#pi-computations')
    assert other and gallery and chapter.find(id='rem:algebraic-numbers-sqrt-two')
    gallery.extract();other.string='1.2.2 Other examples';other.insert_after(gallery)
    gallery.find(['h2','h3']).name='h3'
    for link in gallery.select('a[href]'):
        if link['href']=='pi-computations.html#programme':link['href']='#pi-computation-programme'
    if not gallery.select_one('#pi-computation-programme'):
        gallery.append(parse('''<details id="pi-computation-programme"><summary>Construction and equivalence programme</summary><p>Each formula suggests an independently specified rational-enclosure computation. Its chosen schedule needs a convergence certificate, and its identification with geometric π is a separate theorem. The displayed formulas are mathematical destinations, not a claim that every native equivalence is already proved.</p><p>Geometry, finite recurrences, series tails, algebraic substitutions and improper-integral estimates supply different parts of the foundation. Their checked declarations and alternative proof routes belong in the later chapters and worked comparisons.</p></details>''').details)
    cards=install(chapter,site,args.revision)
    assert cards['formulaCount']==10 and not gallery.select('#pi-cosine')
    assert mathematical_text(chapter)==before,'Original mathematical chapter content changed'
    toc=chapter.select_one('.on-this-page')
    if toc:
        for link in toc.select('a[href="#'+OTHER+'"]'):link.string='1.2.2 Other examples'
        links=toc.select('a[href="#pi-computations"]');anchor=toc.select_one('a[href="#'+OTHER+'"]')
        if anchor and links:links[0].extract();anchor.insert_after(links[0])
    chapter_path.write_text(str(chapter))
    home_path=site/'index.html';home=parse(home_path.read_text())
    for teaser in home.select('.pi-teaser, #pi-computations'):teaser.decompose()
    if not home.select_one('.chapter-one-examples-link'):
        link=parse('<p class="chapter-one-examples-link"><a href="'+DESTINATION+'">Other examples in Chapter 1: computations of π →</a></p>').p
        pair=home.select_one('.chapter-pair');assert pair;pair.insert_after(link)
    home_path.write_text(str(home))
    for page in sorted(site.glob('*.html')):
        if page.name=='pi-computations.html':continue
        doc=parse(page.read_text());nav=doc.select_one('#book-nav')
        if not nav:continue
        for link in nav.select('.pi-catalogue-navigation'):link['href']=DESTINATION;link.string='Other examples: π'
        page.write_text(str(doc))
    (site/'pi-computations.html').write_text('''<!doctype html><html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><meta http-equiv="refresh" content="0;url='''+DESTINATION+'''"><title>Other examples · Computable Analysis</title><link rel="canonical" href="'''+DESTINATION+'''"></head><body><p>The π catalogue is in <a href="'''+DESTINATION+'''">Chapter 1, Other examples</a>.</p></body></html>''')
    for name,text in worked.items():assert str(parse((site/name).read_text()).article)==text,name
    for name,expected in protected.items():assert sha(site/name)==expected,name
    report.update(documentationRevision=args.revision,homeTeaser=False,chapterOneCatalogue=True,
      catalogueSubsection=OTHER,catalogueImmediatelyAfterHeading=True,cosineQuadratureInCatalogue=False,
      cosineQuadratureLocation='cosine.html#numerical-comparison',oldCatalogueRedirect=DESTINATION,
      chapterOneMathematicsUnchanged=True,otherExamplesHeading='1.2.2 Other examples',
      workedComparisonContentUnchanged=True,**cards)
    report_path.write_text(json.dumps(report,indent=2)+'\n')
    audit=dict(documentationRevision=args.revision,proofSourceCommit=report['proofSourceCommit'],
      catalogueSubsection=OTHER,homeTeaser=False,cosineQuadratureInCatalogue=False,
      workedComparisonContentUnchanged=True,originalChapterMathematicsPreserved=True,
      proofDataAndCosineAnimationUnchanged=True,protectedArtifacts=protected,**cards)
    (site/'reading/catalogue-placement.json').write_text(json.dumps(audit,indent=2)+'\n')
    print('PASS: ten expanded pi flashcards under Other examples; Newton and Log(i); no cosine duplication; original proofs unchanged')
if __name__=='__main__':main()
