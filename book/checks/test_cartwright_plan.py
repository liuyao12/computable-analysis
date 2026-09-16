#!/usr/bin/env python3
"""Do not let a verified arithmetic interface masquerade as a full pi proof."""
from pathlib import Path
import hashlib,json,sys
from fractions import Fraction
import xml.etree.ElementTree as ET
from bs4 import BeautifulSoup
ROOT=Path(__file__).resolve().parents[2];SITE=ROOT/'blueprint/web'
sys.path.insert(0,str(ROOT/'book'))
from add_cartwright_plan import closure,measure,P,T

def main():
 maps=json.loads((SITE/'reading/maps.json').read_text());raw=json.loads((SITE/'reading/cartwright-arithmetic.json').read_text())
 report=json.loads((SITE/'reading/cartwright-plan.json').read_text());nodes={n['id']:n for n in raw['nodes']}
 assert all(raw['checks'].values()) and len(raw['declarations'])==11
 assert all('sorryAx' not in r['axioms'] for r in raw['audits'])
 assert not report['finalIrrationalityProved'] and not report['momentIdentityProved']
 assert all(v is None for v in report['plannedMiddleCosts'].values())
 sets={'preparation':closure(nodes,[P+'denominator_cleared']),'conclusion':closure(nodes,[P+'no_positive_small_sequence'])}
 sets['sharedUnion']=sets['preparation']|sets['conclusion']
 for name,names in sets.items():assert report['metrics'][name]==measure(nodes,names)
 assert report['metrics']['sharedUnion']['declarations']<sum(report['metrics'][n]['declarations'] for n in ['preparation','conclusion'])
 assert maps['theorems'][T]['outlineGraph'] and not maps['theorems'][T]['checkedComparison']
 assert 'verifiedGraph' not in maps['theorems'][T]
 edges=[e for e in maps['witnesses'] if e.get('map')==T];assert sum(not e['planned'] for e in edges)==2
 for e in edges:
  if e['planned']:assert e['witness']==[];continue
  for dep,user in zip(e['witness'],e['witness'][1:]):assert dep in nodes[user]['typeRefs']+nodes[user]['bodyRefs']
 exact={d['name']:d for d in raw['declarations']}
 for view,path in maps['theorems'][T]['views'].items():
  svg=ET.parse(SITE/path);visible=[e.get('data-node') for e in svg.iter() if e.get('data-node')]
  assert visible.count(T)==1 and len(visible)==(11 if view=='all' else 9)
  for key in visible:
   b=maps['bundles'][key];assert bool(b['declarations'])==(b['proofStatus']=='checked')
   for d in b['declarations']:assert all(d[k]==exact[d['name']][k] for k in ['name','kind','type','value','ownerModule'])
 for path,h in report['unchangedArtifacts'].items():assert hashlib.sha256((SITE/path).read_bytes()).hexdigest()==h
 # Numerical regressions only; Lean supplies the unrestricted proof.
 for a in [1,2,3,-2]:
  for b in [1,2,-3]:
   p,q=Fraction(1),Fraction(1);k,l=1,b
   for n in range(10):
    assert Fraction(k)==b**n*p
    p,q=q,(2*n+3)*q-Fraction(a,b)*p
    k,l=l,(2*n+3)*b*l-a*b*k
 page=BeautifulSoup((SITE/'cartwright.html').read_text(),'html.parser')
 assert page.select_one('[data-proof-map="'+T+'"]')
 assert len(page.select('tbody tr'))==3
 assert 'not a completed formal proof' in page.get_text()
 print('PASS: arithmetic-only proof frontier, exact checked declarations, witnessed solid edges, unscored planned middles, deduplicated costs and preserved existing graphs')
if __name__=='__main__':main()
