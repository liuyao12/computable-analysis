#!/usr/bin/env python3
"""Check final narrative coverage, explicit hash transitions and math rendering."""
import argparse
from collections import Counter
from functools import partial
from http.server import SimpleHTTPRequestHandler,ThreadingHTTPServer
import json
from pathlib import Path
import shutil
import threading
from bs4 import BeautifulSoup
from pedagogy import digest,narrative_pages,check_links,ROOT,SOURCE


def check(site):
    report=json.loads((site/'reading/pedagogy-edition.json').read_text())
    assert all(report['checks'].values()) and not report['newLeanTheoremsClaimed']
    assert report['sourceSha256']==digest(SOURCE.read_bytes())
    rows=report['reviewedPages'];assert {r['page'] for r in rows}==narrative_pages(site)
    for path,record in report['changedArtifacts'].items():
        assert record['existingMathematicalContentPreserved'] and digest((site/path).read_bytes())==record['after'],path
        doc=BeautifulSoup((site/path).read_text(),'html.parser')
        opening=doc.select_one('main #why-this-page')
        assert opening and len(opening.select('p'))>=2,path
        assert doc.select_one('main h1').find_next_sibling()==opening,path
        assert len(doc.select('[data-pedagogy="opening"]'))==1,path
        check_links(site,str(opening))
        review=next(r for r in rows if r['page']==path)
        assert len(doc.select('[data-pedagogy="bridge"]'))==len(review['sections']),path
        for anchor in review['sections']:
            bridge=doc.find(id=anchor).find_next_sibling()
            assert bridge.get('data-pedagogy')=='bridge',(path,anchor)
            check_links(site,str(bridge))
        ids=[n['id'] for n in doc.select('[id]')];assert len(ids)==len(set(ids)),path
    for path,sha in report['protectedArtifacts'].items():
        assert digest((site/path).read_bytes())==sha,path
    enclosure=json.loads((site/'reading/integral-enclosures-edition.json').read_text())
    def reach_narrative_input(target, sha):
        # The enclosure edition already records a later, checked supersession
        # of the older chapter hashes in the classical-navigation report.
        if target in enclosure['supersededChapterHashes'] and sha==enclosure['supersededChapterHashes'][target]:
            return enclosure['artifacts'][target]
        return sha
    # The old mathematical verification records remain byte-identical snapshots.
    for name in ['classic-proofs-edition','gaussian-convolution','n-ball','power-improper','construction-skills','integral-enclosures-edition']:
        path='reading/'+name+'.json'
        assert path in report['protectedArtifacts'],path
        prior=json.loads((site/path).read_text())
        hashes=prior.get('artifacts',prior.get('artifactHashes',{}))
        for target,sha in hashes.items():
            if target in report['changedArtifacts']:
                assert report['changedArtifacts'][target]['before']==reach_narrative_input(target,sha),(path,target)
    guides=json.loads((site/'reading/construction-skills.json').read_text())
    for guide in guides['skills']+guides['constructionExamples']:
        doc=BeautifulSoup((site/guide['page']).read_text(),'html.parser')
        paragraph=doc.select_one('article h1').find_next_sibling()
        assert paragraph.name=='p' and paragraph.select('a[href]'),guide['page']
        assert (site/'reading'/guide['source']).read_bytes()==(ROOT/guide['source']).read_bytes()
    return report


class Quiet(SimpleHTTPRequestHandler):
    def log_message(self,*args):pass


def main():
    p=argparse.ArgumentParser();p.add_argument('--site',type=Path,required=True);p.add_argument('--report',type=Path,required=True);p.add_argument('--static-only',action='store_true');args=p.parse_args()
    site=args.site.resolve();args.report.mkdir(parents=True,exist_ok=True);report=check(site)
    if not args.static_only:
        from playwright.sync_api import sync_playwright
        server=ThreadingHTTPServer(('127.0.0.1',0),partial(Quiet,directory=str(site)))
        threading.Thread(target=server.serve_forever,daemon=True).start()
        try:
            with sync_playwright() as p:
                options=dict(headless=True,args=['--no-sandbox'])
                executable=shutil.which('google-chrome') or shutil.which('chromium')
                if executable:options['executable_path']=executable
                browser=p.chromium.launch(**options)
                for width in [1440,390]:
                    context=browser.new_context(viewport=dict(width=width,height=900))
                    page=context.new_page()
                    for name in report['changedArtifacts']:
                        page.goto(f'http://127.0.0.1:{server.server_port}/{name}',wait_until='networkidle')
                        if page.locator('script[src*="mathjax"]').count():
                            page.wait_for_function('window.MathJax && MathJax.startup && MathJax.startup.document')
                            page.evaluate('MathJax.startup.promise')
                        assert page.locator('#why-this-page mjx-merror,#why-this-page [data-mjx-error]').count()==0,name
                        assert page.evaluate('''() => Array.from(document.querySelectorAll('[data-pedagogy]')).every(e => e.scrollWidth <= e.clientWidth + 2)'''),(name,width)
                        if name in ['ch-foundations.html','ch-integrals.html','ch-complex-paths.html','fuchs.html']:
                            page.screenshot(path=str(args.report/(name[:-5]+'-'+str(width)+'.png')))
                    context.close()
                browser.close()
        finally:server.shutdown()
    (args.report/'checks.json').write_text(json.dumps(dict(pagesReviewed=len(report['reviewedPages']),
        motivatedOpenings=len(report['changedArtifacts']),sectionTransitions=sum(len(r['sections']) for r in report['reviewedPages']),
        existingProofReportsPreserved=True,sourceDownloadsMatch=True,browserChecked=not args.static_only),indent=2)+'\n')
    print('PASS: all narrative pages reviewed; motivations, prior-context links, preserved proof reports, downloads and final hashes')


if __name__=='__main__':main()
