#!/usr/bin/env python3
"""Publish a mathematically layered PLAN; only its arithmetic blocks are proved."""
from pathlib import Path
from copy import deepcopy
from collections import deque, defaultdict
import hashlib,json,sys
from bs4 import BeautifulSoup
import pygraphviz as pgv
from build import shell
ROOT=Path(__file__).resolve().parents[1];SITE=ROOT/'blueprint/web'
sys.path.insert(0,str(ROOT/'blueprint/checks'))
from build_proof_comparison import strip_comments
P='ComputableAnalysis.CartwrightArithmetic.'
T='thm:cartwright-plan'

CONTENT={
 'cart:recurrence':('Integer recurrence','preparation','checked',['polynomialPair','polynomialValue','integerPair','integerValue'],r'<p>Define the moment polynomials by a finite recurrence and an integer sequence by denominator clearing.</p><div class="displaymath">\[K_0=1,\quad K_1=b,\quad K_{n+2}=(2n+3)bK_{n+1}-abK_n.\]</div><p>This construction is exact integer arithmetic. No integral value is used to define it.</p>'),
 'cart:denominators':('Denominators cleared','preparation','checked',['denominator_pair','denominator_cleared'],r'<p>For rational a/b with b nonzero, the checked identity is</p><div class="displaymath">\[K_n=b^nP_n(a/b).\]</div><p>Tracking consecutive terms makes the denominator cancellation a single induction. It avoids introducing the entire polynomial library for a degree-bound argument.</p>'),
 'cart:moment':('Chosen cosine moments','middle','planned',[],r'<p>Construct the weighted monotone integrals independently of their proposed values:</p><div class="displaymath">\[J_n=\int_0^1(1-t^2)^nC(t/2)\,dt.\]</div><p>Supply a concrete joint evaluation/subdivision schedule and prove convergence. This moment family has not yet been formalized in this project.</p>'),
 'cart:direct':('Finite-sum recurrence','middle','planned',[],r'<p>Proposed direct route: finite product differences, summation by parts and explicit remainder bounds. Prove the same moment recurrence without calling the general FTC. This proof is not yet implemented.</p>'),
 'cart:ftc':('FTC and integration by parts','middle','planned',[],r'<p>Proposed reusable-calculus route: certify the product derivative and integration by parts, then obtain</p><div class="displaymath">\[\lambda^2J_{n+2}=2(n+2)(2n+3)J_{n+1}-4(n+1)(n+2)J_n.\]</div><p>The existing concave-primitive FTC does not automatically cover every intermediate product; its appropriate extensions must be supplied rather than assumed.</p>'),
 'cart:mathlib':('Mathlib moments and bridges','middle','planned',[],r'<p>Proposed comparison route: identify the same native weighted quadrature with Mathlib interval integration, prove the moment recurrence using Mathlib integration by parts, and transport it back.</p><p>The pinned Mathlib pi-irrationality development uses this family, but its private supporting lemmas are not automatically a public bridge for our statement. No checked native moment comparison is claimed here.</p>'),
 'cart:evaluation':('Moment evaluation and bounds','middle','planned',[],r'<p>All proposed alternatives should prove the same evaluation of the same chosen moment programs:</p><div class="displaymath">\[\lambda^{2n+1}J_n\simeq 2^n n!P_n(\lambda^2),\quad 0&lt;J_n\le1.\]</div><p>The moment identity and its positivity/smallness estimates have not yet been checked for these native programs. They remain the central proof obligations.</p>'),
 'cart:interface':('Bounds on an integer','middle','planned',[],r'<p>Under the hypothetical equality \(\lambda^2=a/b\), transfer the evaluation to the exact integer recurrence. The arithmetic consumer needs only</p><div class="displaymath">\[0&lt;K_n,\qquad K_n2^nn!\le2a^n.\]</div><p>This is a planned bridge, not an axiom and not a completed certificate. Bounds are supplied to the separately proved arithmetic theorem only once established.</p>'),
 'cart:factorial':('An explicit factorial bound','conclusion','checked',['factorial_tail_lower','witnessIndex','factorial_dominates'],r'<p>For positive natural a choose N=2a². A block of factorial factors gives</p><div class="displaymath">\[2a^N&lt;2^NN!.\]</div><p>The proof is finite. No asymptotic theorem or analytic limit occurs in its actual dependency closure.</p>'),
 'cart:obstruction':('No positive integer fits','conclusion','checked',['integer_obstruction','no_positive_small_sequence'],r'<p>A positive integer is at least one. Combine this with the explicit factorial bound to rule out the supplied smallness inequality.</p><p>The checked theorem is conditional on its integer inequalities. It does not claim that the missing cosine-moment bridge has supplied them. Its own statement and proof dependencies contain no pi, computable real, integral, or Mathlib declaration.</p>'),
 T:('Irrationality of pi squared','conclusion','planned',[],r'<p>The planned assembly assumes a rational value of \(\lambda^2\), obtains the integer inequalities from the moment evaluation, and applies the verified arithmetic obstruction.</p><p><strong>This final theorem is not yet formalized.</strong> Its eventual transitive dependencies will include the middle argument even though the reusable final arithmetic lemma is calculus-free.</p>')}

def closure(nodes,roots):
 seen=set();todo=list(roots)
 while todo:
  n=todo.pop()
  if n in seen:continue
  seen.add(n);todo.extend(nodes[n]['typeRefs']+nodes[n]['bodyRefs'])
 return seen

def witness(nodes,root,goal):
 prev={root:None};todo=deque([root])
 while todo:
  n=todo.popleft()
  if n==goal:
   out=[]
   while n is not None:out.append(n);n=prev[n]
   return out
  for d in nodes[n]['typeRefs']+nodes[n]['bodyRefs']:
   if d not in prev:prev[d]=n;todo.append(d)
 raise ValueError((root,goal))

def measure(nodes,names):
 lines=defaultdict(set);mapped=0;cache={}
 for n in names:
  d=nodes[n];path=ROOT/(d['module'].replace('.','/')+'.lean');span=d['sourceRange']
  if not span or not path.is_file():continue
  mapped+=1
  if path not in cache:cache[path]=strip_comments(path.read_text()).splitlines()
  lines[path].update(range(span['start'],span['end']+1))
 return dict(declarations=len(names),bodyDag=sum(nodes[n]['bodyDag'] for n in names),
   mappedLOC=sum(bool(cache[p][i-1].strip()) for p,indices in lines.items() for i in indices if 0<i<=len(cache[p])),
   mappedDeclarations=mapped,unmappedDeclarations=len(names)-mapped,
   sourceCoverage='Available project declaration ranges only; missing Lean-library sources are not zero-cost proofs.')

def main():
 reading=SITE/'reading';maps=json.loads((reading/'maps.json').read_text());sha=maps['sourceCommit']
 raw=json.loads((ROOT/'comparison/reports/cartwright-arithmetic.json').read_text());assert all(raw['checks'].values())
 nodes={n['id']:n for n in raw['nodes']};decs={d['name']:d for d in raw['declarations']}
 protected={str(p.relative_to(SITE)):hashlib.sha256(p.read_bytes()).hexdigest() for p in [SITE/'proof-bench/data.json',reading/'map-comparison.json',*reading.glob('cosine-*.svg'),reading/'dyadic-product.svg']}
 stages={'preparation':closure(nodes,[P+'denominator_cleared']),'conclusion':closure(nodes,[P+'no_positive_small_sequence'])}
 sizes={k:measure(nodes,v) for k,v in stages.items()};sizes['sharedUnion']=measure(nodes,set.union(*stages.values()))
 for key,(title,phase,status,names,math) in CONTENT.items():
  cards=[]
  for short in names:
   d=deepcopy(decs[P+short]);d['realDependencyPath']=[];d['sourceUrl']=f'https://github.com/liuyao12/computable-analysis/blob/{sha}/ComputableAnalysis/CartwrightArithmetic.lean';cards.append(d)
  maps['bundles'][key]=dict(title=title,phase=phase,proofStatus=status,anchors=[P+n for n in names],
    groups=[dict(title='Checked arithmetic declarations',names=[P+n for n in names])] if names else [],
    declarations=cards,classification='native' if status=='checked' else 'planned',mathHtml=math,
    strategy=dict(role='Checked arithmetic' if status=='checked' else 'Planned proof step — not yet checked',summary='',groups={}))
 # Solid arrows are verified declaration paths. Dashed arrows are explicitly
 # editorial, proposed mathematical uses; they are not claims of Lean dependencies.
 edges=[]
 def add(s,t,route=None,actual=None):
  edges.append(dict(source=s,target=t,map=T,route=route,kind='proof',planned=actual is None,
    witness=witness(nodes,P+actual[0],P+actual[1]) if actual else [],
    label='Checked arithmetic dependency' if actual else 'Planned mathematical dependency',
    note='The source/target bridge still needs a Lean proof.' if not actual else 'Stored type/body references; no integral or real-number program is used.'))
 add('cart:recurrence','cart:denominators',actual=('denominator_cleared','integerPair'))
 add('cart:factorial','cart:obstruction',actual=('no_positive_small_sequence','factorial_dominates'))
 for i,key in enumerate(['cart:direct','cart:ftc','cart:mathlib']):
  add('cart:moment',key,i);add(key,'cart:evaluation',i)
 add('cart:recurrence','cart:evaluation');add('cart:denominators','cart:interface');add('cart:evaluation','cart:interface')
 add('cart:interface','cart:obstruction');add('cart:obstruction',T)
 views={}
 for route in ['all','0','1','2']:
  visible=set(CONTENT)
  if route!='all':visible-=set(['cart:direct','cart:ftc','cart:mathlib'])-{['cart:direct','cart:ftc','cart:mathlib'][int(route)]}
  g=pgv.AGraph(strict=True,directed=True,rankdir='TB',bgcolor='transparent',nodesep='.42',ranksep='.52',pad='.2')
  g.node_attr.update(shape='box',style='rounded,filled',fontname='Helvetica',fontsize='12',margin='.16,.12')
  g.edge_attr.update(arrowhead='vee',arrowsize='.65')
  for key in sorted(visible):
   title,phase,status,_,_=CONTENT[key]
   g.add_node(key,label=title+('' if status=='checked' else '\nplanned'),fillcolor='#edf3e9' if status=='checked' else '#faf8f3',color='#54725b' if status=='checked' else '#b0a893',style='rounded,filled' if status=='checked' else 'rounded,dashed,filled')
  for phase,label in [('preparation','Arithmetic preparation'),('middle','Integral and calculus arguments'),('conclusion','Finite arithmetic and assembly')]:
   g.add_subgraph([k for k in visible if CONTENT[k][1]==phase],name='cluster_'+phase,label=label,color='#dddcd2',fontname='Helvetica',fontsize='11',style='rounded')
  active=[e for e in edges if e['source'] in visible and e['target'] in visible and (route=='all' or e['route'] is None or str(e['route'])==route)]
  for e in active:g.add_edge(e['source'],e['target'],style='dashed' if e['planned'] else 'solid',color=['#a45032','#326493','#7755a0'][e['route']] if e['route'] is not None else '#424b42')
  # Graphviz does not itself reject a cycle. Test one explicitly.
  deg={str(n):g.in_degree(n) for n in g.nodes()};todo=[n for n,v in deg.items() if not v];done=0
  while todo:
   n=todo.pop();done+=1
   for x in g.successors(n):
    x=str(x);deg[x]-=1
    if not deg[x]:todo.append(x)
  assert done==len(visible) and not list(g.successors(T))
  g.layout('dot');svg=BeautifulSoup(g.draw(format='svg').decode(),'html.parser').svg
  for k in ['width','height']:svg.attrs.pop(k,None)
  for n in svg.select('g.node'):
   key=n.title.get_text();n['data-node']=key;n['data-proof-status']=CONTENT[key][2];n['tabindex']='0';n['role']='button';n['aria-label']=CONTENT[key][0]
  for e in svg.select('g.edge'):
   s,t=e.title.get_text().split('->');rec=next(x for x in active if x['source']==s and x['target']==t)
   e['data-edge']=s+'->'+t;e['data-planned']=str(rec['planned']).lower();e['tabindex']='0';e['role']='button'
  filename=f'reading/cartwright-{route}.svg';(SITE/filename).write_text(str(svg));views[route]=filename
 maps['theorems'][T]=dict(id=T,title='Arithmetic with calculus in the middle',sink=T,outlineGraph=True,checkedComparison=False,
   status='Arithmetic component checked · middle proofs and irrationality assembly planned',page='cartwright.html',views=views,
   routeNames=['Direct finite sums (planned)','FTC (planned)','Mathlib + bridges (planned)'])
 maps['witnesses']=[e for e in maps['witnesses'] if e.get('map')!=T]+edges
 report=dict(sourceCommit=sha,status='partial-arithmetic-only',finalIrrationalityProved=False,momentIdentityProved=False,
   metrics=sizes,plannedMiddleCosts={x:None for x in ['direct','ftc','mathlib']},roots=raw['roots'],checks=raw['checks'],
   unchangedArtifacts=protected,method='Same arithmetic consumer for every proposed route; no missing middle is assigned a zero cost.')
 maps['cartwrightPlan']=dict(url='reading/cartwright-plan.json',**report)
 jsfile=reading/'graph.js';js=jsfile.read_text()
 assert 'entry.outlineGraph' not in js, 'Run the book builder before rebuilding this plan'
 js=js.replace('entry.checkedComparison||entry.verifiedGraph','entry.checkedComparison||entry.verifiedGraph||entry.outlineGraph')
 js=js.replace('!entry.checkedComparison&&!entry.verifiedGraph)', '!entry.checkedComparison&&!entry.verifiedGraph&&!entry.outlineGraph)')
 js += '\n'+(ROOT/'book/assets/cartwright-plan.js').read_text()
 jsfile.write_text(js)
 (reading/'maps.json').write_text(json.dumps(maps,separators=(',',':')))
 (reading/'cartwright-plan.json').write_text(json.dumps(report,indent=2)+'\n')
 (reading/'cartwright-arithmetic.json').write_text(json.dumps(raw,separators=(',',':')))
 labels={'preparation':'Arithmetic preparation','conclusion':'Arithmetic conclusion','sharedUnion':'Both arithmetic blocks, counted once'}
 rows=''.join(f'<tr><td>{labels[k]}</td><td>{s["declarations"]:,}</td><td>{s["mappedLOC"]:,}</td><td>{s["mappedDeclarations"]:,} / {s["declarations"]:,}</td></tr>' for k,s in sizes.items())
 table='<div class="numeric-scroll"><table><thead><tr><th>Checked block</th><th>Referenced declarations</th><th>Mapped project LOC</th><th>Source coverage</th></tr></thead><tbody>'+rows+'</tbody></table></div>'
 table+='<p>Count each referenced type/body declaration once. LOC is the union of available project-source ranges, excluding comments and blank lines. Lean library sources without available ranges remain unmapped, not zero work. This table is not a comparison of the unfinished integral proofs.</p>'
 chapter=BeautifulSoup((ROOT/'book/chapters/cartwright.html').read_text().replace('<!-- ARITHMETIC_METRICS -->',table),'html.parser')
 box=chapter.find(id=T);aside=chapter.new_tag('aside',attrs={'class':'theorem-margin'});link=chapter.new_tag('a',href='proof-map.html?theorem='+T,attrs={'data-proof-map':T});link.string='Proof plan ↗';aside.append(link);note=chapter.new_tag('small');note.string='Arithmetic checked';aside.append(note);box.append(aside)
 (SITE/'cartwright.html').write_text(shell('Arithmetic with calculus in the middle',str(chapter),'cartwright.html','NEXT APPLICATION — PARTLY FORMALIZED','Arithmetic component checked; analytic routes remain planned.',sha,[(h['id'],h.get_text()) for h in chapter.select('h2[id]')]))
 old=SITE/'cosine.html';text=old.read_text();nav='<p id="cartwright-next"><a href="cartwright.html">Next application: from weighted cosine integrals to irrationality →</a></p>';old.write_text(text.replace('</article>',nav+'</article>',1))
 manifest=json.loads((reading/'manifest.json').read_text());manifest['theoremMaps']=len(maps['theorems']);manifest['partlyFormalizedPlans']=1;(reading/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
 for path,h in protected.items():assert hashlib.sha256((SITE/path).read_bytes()).hexdigest()==h
 print('PASS: arithmetic audited; planned calculus explicitly unproved; original graphs and costs preserved')
 print(json.dumps(sizes,indent=2))
if __name__=='__main__':main()
