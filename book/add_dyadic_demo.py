#!/usr/bin/env python3
"""Add a separately checked dyadic-evaluation theorem, not a fake fourth route."""
from pathlib import Path
from collections import deque
from copy import deepcopy
import hashlib,json
from bs4 import BeautifulSoup
import pygraphviz as pgv
from build import shell, add_margins
from dyadic_numerics import product_row, table_html
ROOT=Path(__file__).resolve().parents[1]
P='ComputableAnalysis.';TARGET='thm:dyadic-product'

GROUPS={
 'lem:dyadic-identities':('Dyadic trigonometric identities',[
  'ClockTrigonometry.cosine_addition','ClockTrigonometry.sine_addition',
  'ClockTrigonometry.cosine_half_square','ClockTrigonometry.sine_half_square',
  'ClockTrigonometry.cosine_nonnegative','ClockTrigonometry.cosine_endpoint','ClockTrigonometry.sine_endpoint']),
 'def:dyadic-radicals':('Nested-radical circle coordinates',[
  'HalfAngleRadicals.rootBox','HalfAngleRadicals.halfStep','HalfAngleRadicals.path',
  'DyadicTrigonometry.cosine','DyadicTrigonometry.powerCompute','DyadicTrigonometry.powerCosine',
  'DyadicTrigonometry.powers_valid']),
 'lem:dyadic-values':('Dyadic values agree',[
  'DyadicCosinePrimitive.gridPoint','DyadicCosinePrimitive.dyadic_values','DyadicTrigonometry.powers_equiv']),
 'def:radical-quadrature':('Radical cosine quadrature',[
  'DyadicCosineIntegral.fixedMesh','DyadicCosineIntegral.integral','DyadicCosineIntegral.integral_valid']),
 'lem:radical-quadrature':('Quadrature agreement',[
  'DyadicCosineIntegral.fixedMesh_equiv','DyadicCosineIntegral.integral_equiv_reciprocalPi']),
 'lem:cosine-endpoints':('Cosine primitive and endpoints',[
  'ClosedCosineIntegral.quarterIntegral_equiv_reciprocalPi']),
 TARGET:('Product equals one',[
  'DyadicCosinePrimitive.product','DyadicCosinePrimitive.Statement',
  'DyadicCosinePrimitive.product_valid','DyadicCosinePrimitive.product_eq_one'])}
TEXT={
 'lem:dyadic-identities':r'''<p>Halving and addition give every dyadic circle point. Nonnegativity selects the positive square roots.</p><div class="displaymath">\[C(x/2)^2\simeq(1+C(x))/2,\quad S(x/2)^2\simeq(1-C(x))/2.\]</div><p>The internal Lean clock argument t is a quarter-turn fraction: its cosine is our C(t/2). These identities are proved from the arctangent construction, without borrowing the cosine integral theorem.</p>''',
 'def:dyadic-radicals':r'''<p>Start at slope u=1, the quarter-turn endpoint. Apply a finite prescribed number of positive square-root bisections in</p><div class="displaymath">\[u_{k+1}=\frac{u_k}{1+\sqrt{1+u_k^2}}.\]</div><p>Then use rational circle coordinates and finite rotation products. For depth d and numerator j this supplies C(j/(2·2^d)). The numerical definitions do not call π or arctangent. Defining the algorithm is separate from proving that it evaluates C.</p>''',
 'lem:dyadic-values':r'''<p>For every d and 0≤j≤2^d, the radical coordinate programs agree with the original closed S and C at x=j/(2·2^d).</p><p>This is the required bridge. The exact Lean statement uses CosinePrimitive.C and S, not an unrelated conventional cosine. The bridge does not call either native cosine endpoint proof.</p>''',
 'def:radical-quadrature':r'''<p>Form left rectangle sums on dyadic meshes using only radical cosine samples, enlarge by the proved rational discretization error, and intersect retained meshes.</p><p>This is the actual checked Lean integral program. Its conservative allowance is 1000/2^d. The sharper monotone rectangles in the numerical illustration are a different schedule; the page does not label their numbers as Lean stage outputs.</p>''',
 'lem:radical-quadrature':r'''<p>First transport each fixed finite sum through the dyadic-value equivalence. Then transfer the all-stage enlarged-box bounds and use the same finite-intersection construction.</p><p>This establishes that the radical quadrature represents the same reciprocal of geometric π as the arctangent-based cosine integral. A raw overlap chain alone is not treated as transitive: the validity hypotheses are retained.</p>''',
 'lem:cosine-endpoints':r'''<p>The existing cosine primitive formula and separately proved S(0)=0, S(1/2)=1 identify the arctangent-based integral on [0,1/2] with 1/π.</p><p>This theorem is used in proving the result, not in executing the radical sample algorithm. The original three-proof comparison is unchanged.</p>''',
 TARGET:r'''<p>The two factors are independently defined valid interval programs: geometric π and radical cosine quadrature.</p><div class="displaymath">\[\pi I_{\rm rad}\simeq1.\]</div><p>The product is not definitionally one. The black input arrows unfold the statement's definitions. The colored route proves agreement after transporting the dyadic values and finite sums.</p>'''}

def path(nodes,start,goal,definitions=False,body_entry=False):
 prev={start:None};q=deque([start])
 while q:
  n=q.popleft()
  if n==goal:
   out=[]
   while n is not None:out.append(n);n=prev[n]
   return out
  d=nodes[n]
  if definitions and d['kind']!='def':continue
  keys=['bodyRefs'] if definitions or (body_entry and n==start) else ['bodyRefs','typeRefs']
  for x in sorted({x for k in keys for x in d[k]}):
   if x not in prev:prev[x]=n;q.append(x)
 return None


def main():
 site=ROOT/'blueprint/web';reading=site/'reading'
 m=json.loads((reading/'maps.json').read_text());sha=m['sourceCommit']
 audit=json.loads((ROOT/'comparison/reports/dyadic-evaluation.json').read_text())
 assert all(audit['checks'].values())
 nodes={r['id']:r for r in audit['nodes']};decls={r['name']:r for r in audit['declarations']}
 # Preserve existing proof diagrams byte-for-byte and keep their measurement roots.
 protected={str(p.relative_to(site)):hashlib.sha256(p.read_bytes()).hexdigest()
     for p in [site/'proof-bench/data.json',*reading.glob('cosine-*.svg')]}
 for label,(title,names) in GROUPS.items():
  names=[P+n for n in names];cards=[]
  for name in names:
   d=deepcopy(decls[name]);d['realDependencyPath']=[]
   d['sourceUrl']=f'https://github.com/liuyao12/computable-analysis/blob/{sha}/'+d['ownerModule'].replace('.','/')+'.lean'
   cards.append(d)
  m['bundles'][label]={'title':title,'anchors':names,'groups':[{'title':'Checked definitions and statements','names':names}],
      'declarations':cards,'declarationCount':len(cards),'classification':'native','mathHtml':TEXT[label],
      'strategy':{'role':'A checked evaluation alternative','summary':'Proof bodies are omitted; the exact Lean types and selected executable definitions remain inspectable.','groups':{}}}
 labels=['def:c3-intervals','def:c3-arctan','def:c3-pi','def:c3-trig','def:c3-integrals',*GROUPS]
 graph=pgv.AGraph(strict=True,directed=True,rankdir='TB',splines='spline',bgcolor='transparent',ranksep='.65',nodesep='.35')
 graph.node_attr.update(shape='box',style='rounded,filled',fillcolor='#eef3ed',color='#879a8c',fontname='Helvetica',fontsize='12',margin='.15,.12')
 graph.edge_attr.update(arrowhead='vee',arrowsize='.7')
 for label in labels:graph.add_node(label,label=m['bundles'][label]['title'])
 graph.get_node(TARGET).attr.update(penwidth='2.4',color='#355d49')
 edges=[]
 def edge(source,target,start,goal,kind='proof',label=None):
  witness=path(nodes,P+start,P+goal,definitions=kind=='statement',body_entry=kind=='proof')
  assert witness,(source,target,start,goal)
  e={'source':source,'target':target,'witness':witness,'kind':kind,'route':0 if kind=='proof' else None,
     'globalEdge':True,'label':label or ('Dyadic evaluation proof' if kind=='proof' else 'Definition dependency'),
     'map':TARGET}
  edges.append(e)
  graph.add_edge(source,target,color='#326493' if kind=='proof' else '#202020',
      **{'class':'proof-edge' if kind=='proof' else 'statement-edge' if kind=='statement' else 'construction-edge'})
 edge('def:c3-intervals','def:c3-arctan','CosinePrimitive.A','RealRaw','construction')
 edge('def:c3-arctan','def:c3-pi','CosinePrimitive.pi','CosinePrimitive.A','construction')
 edge('def:c3-arctan','def:c3-trig','ClosedArctanInverse.provider','ArctanGeometry.arctanGeom','construction')
 edge('def:c3-trig','lem:dyadic-identities','ClockTrigonometry.cosine_half_square','ClosedArctanInverse.raw')
 edge('def:c3-intervals','def:dyadic-radicals','DyadicTrigonometry.powerCosine','RealRaw','construction')
 edge('lem:dyadic-identities','lem:dyadic-values','DyadicCosinePrimitive.dyadic_values','ClockTrigonometry.cosine_addition')
 edge('def:dyadic-radicals','lem:dyadic-values','DyadicCosinePrimitive.dyadic_values','DyadicTrigonometry.powerCosine')
 edge('def:c3-integrals','def:radical-quadrature','DyadicCosineIntegral.integral','Integral.Dovetail.raw','construction')
 edge('def:dyadic-radicals','def:radical-quadrature','DyadicCosineIntegral.integral','DyadicTrigonometry.powerCosine','construction')
 edge('lem:dyadic-values','lem:radical-quadrature','DyadicCosineIntegral.fixedMesh_equiv','DyadicTrigonometry.powers_equiv')
 edge('def:radical-quadrature','lem:radical-quadrature','DyadicCosineIntegral.integral_equiv_reciprocalPi','DyadicCosineIntegral.integral')
 edge('def:c3-trig','lem:cosine-endpoints','ClosedCosineIntegral.quarterIntegral_equiv_reciprocalPi','ClosedArctanInverse.provider')
 edge('lem:cosine-endpoints','lem:radical-quadrature','DyadicCosineIntegral.integral_equiv_reciprocalPi','ClosedCosineIntegral.quarterIntegral_equiv_reciprocalPi')
 edge('lem:radical-quadrature',TARGET,'DyadicCosinePrimitive.product_eq_one','DyadicCosineIntegral.integral_equiv_reciprocalPi')
 edge('def:c3-pi',TARGET,'DyadicCosinePrimitive.Statement','CosinePrimitive.pi','statement','Geometric π in the statement')
 edge('def:c3-integrals',TARGET,'DyadicCosinePrimitive.Statement','Integral.Dovetail.raw','statement','Integral construction in the statement')
 edge('def:radical-quadrature',TARGET,'DyadicCosinePrimitive.Statement','DyadicCosineIntegral.integral','statement','Radical integral in the statement')
 # Independent acyclicity check; all displayed edges retain witnesses.
 indegree={str(n):graph.in_degree(n) for n in graph.nodes()};q=[n for n,k in indegree.items() if k==0];count=0
 while q:
  n=q.pop();count+=1
  for nxt in graph.successors(n):
   nxt=str(nxt);indegree[nxt]-=1
   if not indegree[nxt]:q.append(nxt)
 assert count==len(indegree) and list(graph.successors(TARGET))==[]
 graph.layout('dot');svg=BeautifulSoup(graph.draw(format='svg').decode(),'html.parser').svg
 for key in ['width','height']:svg.attrs.pop(key,None)
 for n in svg.select('g.node'):
  ident=n.title.get_text();n['data-node']=ident;n['role']='button';n['tabindex']='0';n['aria-label']=m['bundles'][ident]['title']
 for e in svg.select('g.edge'):
  a,b=e.title.get_text().split('->');item=next(x for x in edges if x['source']==a and x['target']==b)
  e['data-edge']=a+'->'+b;e['data-edge-kind']=item['kind'];e['role']='button';e['tabindex']='0'
 (reading/'dyadic-product.svg').write_text(str(svg))
 m['witnesses']=[e for e in m['witnesses'] if e.get('map')!=TARGET]+edges
 m['theorems'][TARGET]={'id':TARGET,'title':'Geometric π times radical quadrature','sink':TARGET,
    'checkedComparison':False,'verifiedGraph':True,'status':'Checked computational corollary · not a fourth proof of the basepoint statement',
    'page':'dyadic-integral.html','views':{'all':'reading/dyadic-product.svg'},'routeNames':['Dyadic evaluation proof']}
 rows=[product_row(d) for d in [3,5,7,9,11,13]]
 page=BeautifulSoup((ROOT/'book/chapters/dyadic-integral.html').read_text().replace('<!-- DYADIC_TABLE -->',table_html(rows)),'html.parser')
 add_margins(page,m['theorems'],'dyadic-integral.html')
 note=page.select_one('.theorem-margin small');note.string='Checked radical evaluation'
 (site/'dyadic-integral.html').write_text(shell('A cosine integral made of radicals',str(page),'dyadic-integral.html',
    'DYADIC EVALUATION','The original three-proof comparison remains unchanged.',sha,
    [(h['id'],h.get_text(' ',strip=True)) for h in page.select('h2[id]')]))
 m['dyadicEvaluation']={'checks':audit['checks'],'proofCount':1,'comparisonWithOriginalThree':False,
    'normalization':'pi times integral from 0 to 1/2 C equals one',
    'illustrationIsLeanStageExecution':False,'unchangedArtifacts':protected}
 (reading/'maps.json').write_text(json.dumps(m,separators=(',',':')))
 (reading/'dyadic-numerics.json').write_text(json.dumps({'sourceCommit':sha,'rows':rows,'rootPrecision':72,
    'piMethod':'4 A(1), rational inner and outer polygons','cosineMethod':'nested positive square roots and reflection',
    'integralMethod':'monotone endpoint rectangles','leanStageExecution':False},indent=2)+'\n')
 (reading/'dyadic-evaluation.json').write_text(json.dumps(audit,separators=(',',':')))
 manifest=json.loads((reading/'manifest.json').read_text());manifest['theoremMaps']=len(m['theorems']);manifest['checkedSingleProofMaps']=1;manifest['dyadicEvaluation']=m['dyadicEvaluation']
 (reading/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
 link='<p class="dyadic-evaluation-link"><a href="dyadic-integral.html">Geometric π × radical cosine integral: a second numerical experiment and its identity bridge →</a></p>'
 old=site/'cosine.html';text=old.read_text();text=text if 'class="dyadic-evaluation-link"' in text else text.replace('<h2 id="numerical-comparison">',link+'<h2 id="numerical-comparison">',1);old.write_text(text)
 for f,h in protected.items():assert hashlib.sha256((site/f).read_bytes()).hexdigest()==h
 print('PASS: checked dyadic identity node, three definition-only statement inputs, witnessed proof edges, new product theorem; original graphs and measurements unchanged')
 print('Product bounds at 8192 cells:',rows[-1]['productDisplay'])
if __name__=='__main__':main()
