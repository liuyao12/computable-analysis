#!/usr/bin/env python3
"""Mathematics-first reader. Preserve the original source and verification layers."""
from __future__ import annotations
import argparse,hashlib,html,json,re,shutil,subprocess
from pathlib import Path
from bs4 import BeautifulSoup
import pygraphviz as pgv
from proof_semantics import prepare as separate_statement_and_proof
ROOT=Path(__file__).resolve().parents[1]

CHAPTERS=[('ch-foundations.html','01','Numbers and functions'),
 ('ch-circle-sphere.html','02','Circle, sphere and cylinder'),
 ('ch-rational-circle-trigonometry.html','03','Angles and trigonometry'),
 ('ch-integrals.html','04','Integral computations'),
 ('ch-effective-calculus.html','05','Derivatives and the FTC'),
 ('ch-infinite-series.html','06','Infinite series'),
 ('ch-exponential-logarithm.html','07','Exponential and logarithm'),
 ('ch-algebra-fta.html','08','Algebraic computations'),
 ('ch-local-models.html','09','Local models'),
 ('ch-complex-paths.html','10','Complex paths'),
 ('ch-improper-parameters.html','11','Improper integrals'),
 ('ch-fourier.html','12','Fourier computations'),
 ('ch-impulses.html','13','Impulses'),
 ('ch-differential-equations.html','14','Differential equations'),
 ('ch-special-equations.html','15','Special-function equations'),
 ('ch-transforms-zeta.html','16','Transforms and zeta'),
 ('ch-elliptic.html','17','Elliptic integrals')]
# Editorial map summaries are explicitly NOT claims of formally extracted dependencies.
OUTLINES={
 'prop:raw-prefix-stabilization': [('Finite error bounds','At each stage compute a rational centre and an error that encloses every later centre.'),('Finite intersection','Intersect the first n+1 enclosures. Their common future centres give compatibility; retaining one sufficiently narrow interval gives shrinking widths.')],
 'prop:computed-inputs':[('An input and interval continuity','The input is itself a nested-enclosure computation. The function supplies an interval evaluator and the quantitative continuity data stated in the chapter.'),('Evaluation and refinement','Refine the input sufficiently, enclose its image, and stabilize the finite results. The continuity data controls output error.')],
 'thm:sphere-volume':[('Finite cylinder stacks','Bound spherical slices from inside and outside by finite stacks of circular cylinders.'),('A shrinking volume gap','Finite sums of squared slice heights give the limiting factor. Rational volume error bounds identify the resulting computation with the stated multiple of the disk area.')],
 'thm:sphere-area':[('Frusta and polygonal surfaces','Approximate the meridian by finite segments and compare the resulting conical frusta with cylindrical bands.'),('Surface error bounds','Control the accumulated gap as the subdivision is refined. The chapter’s surface computation is compared with the lateral area of the cylinder.')],
 'thm:fixed-schedule-derivative':[('Curvature and secants','Convexity orders forward and backward secants. The hypotheses specify the input chart and evaluation schedules.'),('A supplied shrinking estimate','Compatibility alone does not give a derivative at a corner. Use the explicitly assumed shrinking-width bound for the selected schedule.')],
 'thm:convex-ftc':[('A computed convex derivative','Keep the convexity hypotheses and the resolution data for the specified derivative construction.'),('Finite telescoping','Compare the controlled derivative rectangles with increments of the original computation, then sum the finite increments.')],
 'thm:ftc-finite-output':[('Endpoint control','Use the theorem’s interval and resolution hypotheses, not just pointwise rational differentiability.'),('Two output inequalities','Keep finite endpoint errors throughout the sum and establish overlap of every integral box with every endpoint-difference box.')],
 'thm:finite-taylor-ftc-prefix':[('A supplied series and tail','A coefficient computation and a majorant control the series on a larger interval.'),('Smaller-domain error control','Differentiate or integrate finite prefixes, then use derivative and integral tail bounds on the smaller interval.')],
 'thm:recenter-model':[('A local series chart','Start with the stated radius, coefficient estimates and displacement bound.'),('Finite binomial rearrangement','Recenter finite sums, then control the infinite coefficient tails by the majorant. The smaller radius is part of the conclusion.')],
 'thm:beta-gamma':[('Independent positive-parameter integrals','Keep the domains and endpoint-tail data for beta and gamma specified in the chapter.'),('Finite substitution and tails','Make the change of variables on bounded pieces, control omitted tails, and compare the independent computations.')],
 'thm:basel-geometric-overlap':[('Reciprocal squares and trigonometry','Use the independently constructed reciprocal-square series and geometric trigonometric values.'),('Finite comparison','The chapter compares finite expressions and bounds their tails; the result must connect the two named computations, not define one by the other.')]
}


def soup(s): return BeautifulSoup(s,'html.parser')
def clean(node):
    b=soup(str(node))
    for x in b.select('.thm_header_extras,.thm_header_hidden_extras,.proof_qed,.mathjax_ignore,.showmore,.footnotes .navigation'): x.decompose()
    for x in b.select('script,style'):x.decompose()
    return b

def text_digest(node):
    b=clean(node)
    return hashlib.sha256(re.sub(r'\s+',' ',b.get_text(' ',strip=True)).encode()).hexdigest()

def nav(current):
    rows=[('<span class="nav-label">The book</span>')]
    for f,n,title in CHAPTERS:
        if f=='ch-algebra-fta.html':rows.append(f'<details class="later-chapters"{" open" if current in [x[0] for x in CHAPTERS[7:]] else ""}><summary>Further chapters</summary>')
        rows.append(f'<a class="{"current" if current==f else ""}" href="{f}"><span>{n}</span>{title}</a>')
    rows.append('</details>')
    rows += ['<span class="nav-label">A worked comparison</span>',f'<a class="{"current" if current=="cosine.html" else ""}" href="cosine.html">The cosine primitive</a>',
      '<span class="nav-label">The development</span>','<a href="programme.html">Purpose and boundary</a>',
      '<a href="proof-bench/">Proof-size comparison</a>','<a href="reference/index.html">Technical reference ↗</a>']
    return ''.join(rows)

def shell(title,body,file,number='',subtitle='',sha='',toc=None):
    toc=toc or []
    contents=''.join(f'<a href="#{html.escape(i)}">{html.escape(t)}</a>' for i,t in toc)
    return f'''<!doctype html><html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><meta name="description" content="A mathematical foundation for calculus through certified rational computations."><title>{html.escape(title)} · Computable calculus</title><link rel="stylesheet" href="reading/book.css"><script>window.MathJax={{tex:{{inlineMath:[['\\\\(','\\\\)']],processEscapes:true}},options:{{skipHtmlTags:['script','noscript','style','textarea','pre','code']}}}};</script><script defer src="https://cdn.jsdelivr.net/npm/mathjax@3/es5/tex-chtml.js"></script><script defer src="reading/book.js"></script></head>
<body><a class="skip" href="#main">Skip to mathematics</a><header class="book-header"><button id="menu-button" aria-expanded="false" aria-controls="book-nav">Contents</button><a class="brand" href="index.html">Computable <em>calculus</em></a><a class="header-about" href="programme.html">An alternative foundation</a></header>
<nav id="book-nav" aria-label="Book chapters">{nav(file)}</nav>
<div class="page"><main id="main" class="reader"><div class="chapter-kicker">{html.escape(number or 'COMPUTABLE ANALYSIS')}</div><article>{body}</article><footer class="chapter-footer"><span>{html.escape(subtitle or 'Mathematics first. Formal details at each theorem.')}</span><a href="https://github.com/liuyao12/computable-analysis/tree/{sha}">Source {sha[:8]} ↗</a></footer></main><aside class="on-this-page"><span>On this page</span>{contents}</aside></div>
<dialog id="proof-dialog"><div class="dialog-top"><span>Proof structure</span><button id="close-proof" aria-label="Close proof map and return to the text">Return to text ×</button></div><iframe id="proof-frame" title="Mathematical proof map"></iframe></dialog></body></html>'''

def add_margins(body,catalog,file):
    for node in body.find_all('div',class_=lambda c:c and c.endswith('_thmwrapper')):
        cap=node.find(class_=lambda c:c and c.endswith('_thmcaption'))
        if not cap or cap.get_text(strip=True) not in ['Theorem','Lemma','Proposition','Corollary']:continue
        ident=node.get('id');
        if not ident:continue
        title=node.find(class_=lambda c:c and c.endswith('_thmtitle'))
        title=title.get_text(' ',strip=True) if title else cap.get_text(strip=True)
        content=node.find(class_=lambda c:c and c.endswith('_thmcontent'))
        if ident not in catalog:
            proof=node.find_next_sibling(class_=lambda c:c and c.endswith('proof_wrapper'))
            catalog[ident]={'id':ident,'title':title,'page':file,'checkedComparison':False,
                'status':'Editorial proof outline · paired Lean comparison not registered',
                'statement':str(clean(content)),'proofIdea':str(clean(proof)) if proof else '',
                'outline':[{'title':t,'text':p} for t,p in OUTLINES.get(ident,[])], 'nodes':[], 'edges':[]}
        aside=body.new_tag('aside',attrs={'class':'theorem-margin','aria-label':'Proof details'})
        a=body.new_tag('a',href='proof-map.html?theorem='+ident,attrs={'data-proof-map':ident})
        a.string='Proof map ↗';aside.append(a)
        note=body.new_tag('small');note.string='3 checked routes' if catalog[ident]['checkedComparison'] else 'Reading outline';aside.append(note)
        if catalog[ident]['checkedComparison']:
            c=body.new_tag('a',href='proof-bench/');c.string='Compare proofs';aside.append(c)
        node.append(aside)


def programme(inventory,audit):
    r=inventory['nativeSourceNoncomputableCount']
    rows=''.join(f'<tr><td><code>{html.escape(x["file"])}</code></td><td><code>{html.escape(x["declaration"])}</code></td></tr>' for x in inventory['migrationInventory'])
    return f'''<h1>Purpose, scope and the computational boundary</h1>
<p class="lead">Useful calculus without obtaining numerical objects from noncomputable declarations.</p>
<h2 id="boundary">What belongs in the foundation</h2><p>The native route starts with rational arithmetic, finite data and algorithms. A public number or function must supply a terminating evaluator and enough mathematical control to establish its domain, enclosure correctness and arbitrary precision. A certificate is evidence that a construction works, not permission to choose missing numerical data.</p>
<p>The optional Mathlib comparison can interpret these computations in Mathlib’s reals, but it is downstream of the native package. It cannot become an unnoticed ingredient of our algorithms. Classical reasoning in proofs and inherited native-computation axioms are reported separately from numerical executability.</p>
<h2 id="audit">The current audit</h2><p>The source inventory currently records <strong>{r} historical native noncomputable declarations</strong>. They are migration work, not evidence that the target boundary has been met everywhere. New additions are rejected by a baseline check. Replacing one of these helpers requires supplying its missing witness or algorithm, not merely deleting the keyword.</p>
<p>The Lean audit separately checks the stored dependency closures of the published arctangent, pi, sine, cosine, quadrature, two native cosine proofs, and rational-imaginary exponential. It checks native noncomputable tags and the Mathlib boundary; ordinary external proof dependencies remain visible. Concrete pi, sine, cosine and quadrature evaluations are also compiled and run.</p>
<p><a href="reading/native-computability.json">Declaration audit</a> · <a href="reading/native-source-boundary.json">Full source inventory</a> · <a href="three-proofs/definition-audit.json">Definition independence</a></p>
<details><summary>Inspect the {r} historical source declarations</summary><div class="wide-table"><table><thead><tr><th>Module</th><th>Declaration</th></tr></thead><tbody>{rows}</tbody></table></div></details>
<h2 id="scope">Adequacy is a programme, not a current claim</h2><p>The intended scope is the calculus used in substantial scientific and engineering work: controlled elementary functions, integration, differentiation, local approximation, complex exponentials, and differential equations. Each operation must state the estimates and domain restrictions on which it depends.</p>
<p>The existing later chapters are kept as a mathematical manuscript. Their theorem-side maps distinguish a reading outline from an audited formal comparison. The current three-route comparison is one cosine example, not evidence of complete coverage of those fields.</p>
<h2 id="next">How the redesign guides the next work</h2><p>First finish the migration of native noncomputable helpers and expand the audited computational entry points. Then add paired comparisons for polynomial and rational functions, the actual sine derivative, algebraic inverses, and exponentials. Finally use complex rotations and linear ODEs in explicit scientific problems with certified tolerances.</p>
<p>Proof size will be measured cumulatively, so reused mathematics and representation bridges are charged once rather than anew for every theorem. Numerical runtime, useful error estimates, hypotheses and logical trust remain separate measurements. The aim is not to win an import-count contest; it is to make this foundation adequate, inspectable and reusable.</p>
<h2 id="edition">About this edition</h2><p>The original sources of Chapters 1 and 2 are unchanged, protected by hashes. The other mathematical chapters remain available in their original order. The reader is a new presentation, not the old blueprint skin. Formal declarations, build reports and legacy links remain in a separate technical reference.</p><p><a href="reading/preservation.json">Chapter preservation record</a> · <a href="reference/index.html">Previous technical presentation</a></p>'''

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--site',type=Path,default=ROOT/'blueprint/web');ap.add_argument('--commit');args=ap.parse_args()
    site=args.site;source=site/'reference'
    if not source.exists():
        source.mkdir()
        for f in list(site.iterdir()):
            if f==source:continue
            if f.is_dir():shutil.copytree(f,source/f.name)
            else:shutil.copy2(f,source/f.name)
    graphtext=(source/'cosine-primitive-graph.html').read_text()
    at=graphtext.index('const proofGraphData=')+len('const proofGraphData=')
    g,_=json.JSONDecoder().raw_decode(graphtext[at:]);sha=args.commit or g['info']['sourceCommit']
    g=separate_statement_and_proof(g,ROOT/'comparison/reports/proof-bench-raw.json')
    book=site/'reading';book.mkdir(exist_ok=True)
    preserved=json.loads((ROOT/'book/preserved-chapters.json').read_text())
    for p,h in preserved['files'].items():assert hashlib.sha256((ROOT/p).read_bytes()).hexdigest()==h
    legacy=soup(graphtext)
    for k,d in g['nodeDetails'].items():
        modal=legacy.find(id=k+'_modal');mathnode=modal.find(class_=lambda c:c and c.endswith('_thmcontent')) if modal else None
        d['mathHtml']=str(clean(mathnode)) if mathnode else ''
    svgviews={}
    for view,dot in g['views'].items():
        gr=pgv.AGraph(string=dot)
        gr.graph_attr.update(bgcolor='transparent',pad='.25',nodesep='.42',ranksep='.58')
        gr.node_attr.update(fontname='Helvetica',fontsize='12',penwidth='1.2')
        for n in gr.nodes():
            d=g['nodeDetails'].get(str(n),{});kind=d.get('classification','native')
            fill={'native':'#eef3ed','mathlib':'#f0eafa','mixed':('#eef3ed' if view in ['0','1'] else '#f0eafa' if view=='2' else '#eef3ed:#f0eafa')}.get(kind,'#eef3ed')
            n.attr.update(fillcolor=fill,color='#879a8c',fontcolor='#24372c',style='rounded,filled',shape='box',margin='.17,.13')
            if str(n)=='thm:c3-primitive':n.attr.update(penwidth='2.2',color='#355d49')
        gr.layout('dot');svg=gr.draw(format='svg').decode();
        sv=soup(svg).svg
        sv.attrs.pop('width',None);sv.attrs.pop('height',None);sv['aria-label']='Bundled proof dependency graph'
        sv['role']='img'
        for node in sv.select('g.node'):
            title=node.find('title').get_text();node['data-node']=title;node['tabindex']='0';node['role']='button';node['aria-label']=g['nodeDetails'].get(title,{}).get('title',title)
        for edge in sv.select('g.edge'):
            edge['data-edge']=edge.find('title').get_text();edge['tabindex']='0';edge['role']='button'
            classes=edge.get('class',[])
            kind='statement' if 'statement-edge' in classes else 'proof' if 'proof-edge' in classes else 'construction'
            edge['data-edge-kind']=kind
            edge['aria-label']='Inspect '+kind+' dependency path'
        (book/f'cosine-{view}.svg').write_text(str(sv));svgviews[view]=f'reading/cosine-{view}.svg'
    catalog={'thm:c3-primitive':{'id':'thm:c3-primitive','title':'The cosine primitive','checkedComparison':True,'status':'Three checked proofs of the same proposition','page':'cosine.html','views':svgviews}}
    protection={}
    for file,num,title in CHAPTERS:
        if not (source/file).exists():continue
        original=soup((source/file).read_text()).select_one('.main-text');assert original
        body=clean(original)
        h1=body.find('h1');head=h1.get_text(' ',strip=True);h1.string=re.sub(r'^\d+\s+','',head)
        for h in body.find_all('h1')[1:]:h.name='h2'
        add_margins(body,catalog,file)
        toc=[(h.get('id',''),h.get_text(' ',strip=True)) for h in body.select('h2[id]')]
        label='Original chapter preserved' if num in ['01','02'] else 'Mathematical manuscript · formal comparison status at each theorem'
        (site/file).write_text(shell(title,str(body),file,'CHAPTER '+num,label,sha,toc))
        if num in ['01','02']:
            test=soup(str(body));
            for a in test.select('.theorem-margin'):a.decompose()
            test.find('h1').string=head
            protection[file]={'originalTextHash':text_digest(original),'readerTextHash':text_digest(test), 'identicalMathematicalText':text_digest(original)==text_digest(test)}
            assert protection[file]['identicalMathematicalText'],file
    for file,src,kicker in [('index.html','preface.html','A MATHEMATICAL BOOK'),('cosine.html','cosine.html','WORKED THEOREM')]:
        body=soup((ROOT/'book/chapters'/src).read_text());add_margins(body,catalog,file)
        title=body.h1.get_text(' ',strip=True)
        (site/file).write_text(shell(title,str(body),file,kicker,'',sha,[(h['id'],h.get_text(' ',strip=True)) for h in body.select('h2[id]')]))
    inv=json.loads((ROOT/'comparison/reports/native-source-boundary.json').read_text())
    auditpath=ROOT/'comparison/reports/native-computability.json'
    audit=json.loads(auditpath.read_text()) if auditpath.exists() else {'pending':True,'scope':'Compiler audit will be run by CI before publication.'}
    (site/'programme.html').write_text(shell('Purpose and computational boundary',programme(inv,audit),'programme.html','THE PROGRAMME','',sha))
    for k,c in catalog.items():
        if c['checkedComparison']:continue
        nodes=[];edges=[]
        for i,step in enumerate(c['outline']):
            nid=f'step-{i}';nodes.append({'id':nid,'title':step['title'],'text':step['text']});
            if i:edges.append([f'step-{i-1}',nid])
        nodes.append({'id':'conclusion','title':c['title'],'mathHtml':c['statement'],'text':'Original manuscript statement. A paired Lean proof comparison has not been registered for this theorem.'})
        if c['outline']:edges.append([f'step-{len(c["outline"])-1}','conclusion'])
        c['nodes']=nodes;c['edges']=edges
    (book/'maps.json').write_text(json.dumps({'sourceCommit':sha,'proofSourceCommit':g['info']['sourceCommit'],'theorems':catalog,'bundles':g['nodeDetails'],'witnesses':g['witnesses'],'edgeSemantics':g['info']['edgeSemantics'],'checks':g['info']['checks']},separators=(',',':')))
    for file in ['book.css','book.js','graph.js','graph.html','proof-edges.css']:
        dest=site/'proof-map.html' if file=='graph.html' else book/file
        shutil.copyfile(ROOT/'book/assets'/file,dest)
    shutil.copyfile(ROOT/'blueprint/three-proofs/lean-highlight.js',book/'lean-highlight.js')
    for file,data in [('native-source-boundary.json',inv),('native-computability.json',audit),('preservation.json',{'sources':preserved,'rendered':protection})]:
        (book/file).write_text(json.dumps(data,indent=2)+'\n')
    def redirect(f,to):
        path=site/f;path.parent.mkdir(exist_ok=True,parents=True);path.write_text(f'<!doctype html><html lang="en"><head><meta charset="utf-8"><meta http-equiv="refresh" content="0;url={html.escape(to)}"><title>Computable calculus</title></head><body><a href="{html.escape(to)}">Continue to the mathematical book</a></body></html>')
    redirect('cosine-primitive-graph.html','proof-map.html?theorem=thm:c3-primitive')
    redirect('proof-comparison/index.html','../proof-map.html?theorem=thm:c3-primitive')
    redirect('ch-two-cosine-proofs.html','cosine.html')
    redirect('ch-three-cosine-proofs.html','cosine.html')
    manifest={'sourceCommit':sha,'proofSourceCommit':g['info']['sourceCommit'],'chapters':len(CHAPTERS),
      'theoremMaps':len(catalog),'checkedPairedMaps':sum(c['checkedComparison'] for c in catalog.values()),
      'preservedFirstTwo':all(v['identicalMathematicalText'] for v in protection.values()),
      'noncomputableInventory':inv['nativeSourceNoncomputableCount'],'compilerAuditPresent':not audit.get('pending',False),
      'edgeSemanticsVersion':1,
      'kind':'Mathematical reader; older detailed blueprint preserved under reference/.'}
    (book/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
    print(json.dumps(manifest,indent=2))
if __name__=='__main__':main()
