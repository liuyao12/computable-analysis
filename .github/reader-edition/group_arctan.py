#!/usr/bin/env python3
"""Group arctangent representations without altering computations or proofs.

Run after pi_patterns.py and its checks. Old method fragments remain reachable;
Log(i), Newton, and the remaining cards are preserved exactly.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from collections import Counter
from pathlib import Path
from bs4 import BeautifulSoup

MEMBERS = ['pi-geometry', 'pi-arctan', 'pi-leibniz', 'pi-brouncker', 'pi-machin']
METHODS = ['pi-geometry', 'pi-arctan-integral', 'pi-leibniz', 'pi-brouncker', 'pi-machin']
TITLE_FORMULA = r'\pi=4\arctan(1)'
STYLE = '''
#pi-arctan .pi-computation-method{margin-top:20px;padding-top:14px;border-top:1px solid var(--line)}
#pi-arctan .pi-computation-method:first-of-type{margin-top:12px}
#pi-arctan .pi-computation-method>h4{font:600 13px/1.6 system-ui;margin:0 0 10px}
#pi-arctan .pi-computation-method>a{font:11px/1.6 system-ui}
#pi-arctan .pi-computation-method{scroll-margin-top:96px}
'''
SCRIPT = '''
(function(){
  function reveal(){
    let key;try{key=decodeURIComponent(location.hash.slice(1));}catch(_){return;}
    const target=document.getElementById(key);
    if(!target||!target.closest('#pi-arctan .pi-computation-method, #pi-log-one-plus-i'))return;
    for(let p=target;p;p=p.parentElement)if(p.tagName==='DETAILS')p.open=true;
    requestAnimationFrame(()=>target.scrollIntoView({block:'start'}));
  }
  window.addEventListener('hashchange',reveal);
  document.addEventListener('DOMContentLoaded',function(){
    reveal();
    if(window.MathJax&&MathJax.startup&&MathJax.startup.promise)MathJax.startup.promise.then(reveal);
  });
})();
'''

def parse(text):return BeautifulSoup(text,'html.parser')
def digest(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def outside(doc):
    copy=parse(str(doc.article));copy.select_one('#pi-computations').decompose()
    return copy.get_text(' ',strip=True)
def formulas(node):return Counter(e.get_text() for e in node.select('.formula'))

def install(site: Path,revision: str):
    page=site/'ch-foundations.html';doc=parse(page.read_text());gallery=doc.select_one('#pi-computations')
    grid=gallery.select_one('.pi-gallery-grid')
    assert len(grid.select(':scope > .pi-formula-card'))==11
    chapter_before=outside(doc);formula_before=formulas(gallery)
    remaining={c['id']:str(c) for c in grid.select(':scope > .pi-formula-card') if c['id'] not in MEMBERS}
    excluded={'ch-foundations.html','reading/analysis-edition.json','reading/catalogue-placement.json','reading/arctan-group.json'}
    protected={str(p.relative_to(site)):digest(p) for p in site.rglob('*') if p.is_file() and str(p.relative_to(site)) not in excluded}
    cards=[grid.find(id=key) for key in MEMBERS];assert all(cards)
    group=parse('<article class="pi-formula-card" id="pi-arctan"><h3>Arctangent</h3>'
      '<div class="formula">\\['+TITLE_FORMULA+'\\]</div>'
      '<p>One value, several constructions.</p>'
      '<details class="pi-formula-details"><summary>Ways to compute arctan(1)</summary>'
      '<p>Geometry, quadrature, series, continued fractions, and angle addition give different computations of the same value.</p>'
      '</details></article>').article
    cards[0].insert_before(group);panel=group.details
    for card,new_id in zip(cards,METHODS):
        card.extract();card.name='section';card['id']=new_id;card['class']=['pi-computation-method']
        card.h3.name='h4';panel.append(card)
    group.find(id='pi-arctan-integral').append(parse('<p><a href="#pi-log-one-plus-i">Why this integral is the imaginary part of a logarithm</a></p>').p)
    assert len(grid.select(':scope > .pi-formula-card'))==7
    assert len(group.select('.pi-computation-method'))==5
    assert formulas(gallery)==formula_before+Counter({r'\['+TITLE_FORMULA+r'\]':1})
    assert all(str(gallery.find(id=key))==text for key,text in remaining.items())
    assert outside(doc)==chapter_before
    assert not group.select('#pi-machin details')
    assert len(group.select('#pi-machin .formula'))==1
    assert r'\arctan' in group.find(id='pi-machin').get_text()
    style=doc.new_tag('style',id='arctan-group-style');style.string=STYLE;doc.head.append(style)
    script=doc.new_tag('script',id='arctan-group-fragments');script.string=SCRIPT;doc.head.append(script)
    page.write_text(str(doc))
    for f,h in protected.items():assert digest(site/f)==h,f
    for f in ['analysis-edition.json','catalogue-placement.json']:
        path=site/'reading'/f;metadata=json.loads(path.read_text())
        assert metadata['formulaCount']==11
        metadata.update(documentationRevision=revision,formulaCount=7,underlyingRepresentationCount=11,
                        arctangentGrouped=True,arctangentMethods=METHODS)
        path.write_text(json.dumps(metadata,indent=2)+'\n')
    record=dict(documentationRevision=revision,flashcardCount=7,underlyingRepresentationCount=11,
      arctangentGrouped=True,group='pi-arctan',mainFormula=TITLE_FORMULA,methods=METHODS,
      preservedCards=list(remaining),originalFormulasRetained=True,chapterOutsideGalleryUnchanged=True,
      machinUsesArctanOnly=True,oldMethodFragmentsPreserved=True,proofDataAndNumericsUnchanged=True,
      newLeanProofsClaimed=False,protectedArtifacts=protected)
    (site/'reading/arctan-group.json').write_text(json.dumps(record,indent=2)+'\n')
    print('PASS: seven flashcards; five arctangent methods grouped; old formulas, other cards, numerical records and proofs preserved')

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--site',type=Path,required=True);ap.add_argument('--revision',required=True)
    args=ap.parse_args();install(args.site,args.revision)
if __name__=='__main__':main()
