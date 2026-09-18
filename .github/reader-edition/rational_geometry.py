#!/usr/bin/env python3
"""Publish the checked finite geometry after the existing reader passes.

The TeX opening is the content source. Original chapters, formulas and proof
comparisons outside this opening are preserved; new declarations are exported
by Lean, not transcribed by the renderer.
"""
from __future__ import annotations
import argparse, copy, hashlib, html, json, re, subprocess
from collections import deque
from fractions import Fraction as Q
from pathlib import Path
from bs4 import BeautifulSoup

ROOT=Path(__file__).resolve().parents[2]
P='ComputableAnalysis.'
G=P+'RationalGeometry.'; C=P+'QuarterCircleGeometry.'
FANS='thm:rational-polygon-fans'; QUARTER='thm:quarter-circle-polygons'

def parse(s): return BeautifulSoup(s,'html.parser')
def digest(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def formula(s): return '<div class="displaymath">\\['+html.escape(s)+'\\]</div>'
def text(s):
    s=re.sub(r'\s+',' ',s.strip())
    return re.sub(r'\$([^$]+)\$',lambda m:r'\('+m[1]+r'\)',html.escape(s))

def render_opening(source,figure):
    source=re.sub(r'(?m)^%.*\n','',source)
    pat=re.compile(r'\\begin\{figure\}.*?\\end\{figure\}|\\\[.*?\\\]|\\(?:section|subsection|paragraph)\{[^}]+\}(?:\s*\\label\{[^}]+\})?',re.S)
    out=[];pos=0;section=0
    for m in pat.finditer(source):
        out += ['<p>'+text(s)+'</p>' for s in re.split(r'\n\s*\n',source[pos:m.start()]) if s.strip()]
        token=m[0]
        if token.startswith(r'\['): out.append(formula(token[2:-2]))
        elif token.startswith(r'\begin{figure}'):
            f=copy.deepcopy(figure)
            f.select_one('.caption_text').string='A rational computation, whose geometric interpretation will follow.'
            out.append(str(f))
        else:
            kind,title=re.match(r'\\(section|subsection|paragraph)\{([^}]+)\}',token).groups()
            label=re.search(r'\\label\{([^}]+)\}',token)
            ident=label[1] if label else 'geometry-'+re.sub('[^a-z0-9]+','-',title.lower()).strip('-')
            if kind=='section': section+=1;title='2.'+str(section)+' '+title
            tag='h2' if kind=='section' else 'h3'
            out.append(f'<{tag} id="{ident}">{html.escape(title)}</{tag}>')
        pos=m.end()
    out += ['<p>'+text(s)+'</p>' for s in re.split(r'\n\s*\n',source[pos:]) if s.strip()]
    return parse('\n'.join(out)),section

GROUPS={
 'geo:points':('Rational points and vectors',[G+'Point',G+'Polygon',G+'det']),
 'geo:areas':('Triangle area',[G+'AreaForm',G+'determinantAreaForm',G+'AreaForm.unique',G+'triangleArea',G+'triangle_boundary',G+'triangle_subdivision']),
 'geo:boundary':('Cyclic polygon boundary',[G+'edgeArea',G+'walk',G+'cycleSum',G+'area',G+'startAt']),
 'geo:fan':('Cancellation in a fan',[G+'fanArea',G+'fanFrom',G+'triangulationArea',G+'fanArea_eq_area',G+'triangulationArea_eq_area']),
 'geo:cyclic':('Change the starting vertex',[G+'area_startAt']),
 FANS:('The same polygon area',[G+'triangulationArea_startAt',G+'fanArea_startAt',G+'area_reverse']),
 'geo:transforms':('Affine transformations',[G+'AffineMap',G+'AffineMap.apply',G+'AffineMap.area_apply',G+'AffineMap.Orthogonal',G+'AffineMap.determinant_sq_of_orthogonal',G+'area_translation',G+'area_homothety']),
 'geo:volume':('Tetrahedral volume',[G+'Point3',G+'det3',G+'tetrahedronVolume',G+'tetrahedron_swap',G+'tetrahedron_subdivision',G+'tetrahedron_scale']),
 'geo:computation':('Quarter-circle computation',[C+'raw',C+'raw_compute',C+'raw_width']),
 'geo:validity':('The computation is valid',[C+'raw_valid']),
 'geo:circle-polygons':('Inner and outer polygons',[C+'point',C+'innerPolygon',C+'outerPolygon',C+'inner_area_nonneg',C+'outer_area_nonneg']),
 QUARTER:('Quarter-circle area',[C+'area_legacy',C+'raw_compute_polygon_areas',C+'raw_compute_any_fans'])}
DESCRIPTIONS={
 'geo:points':'Every coordinate is rational. The ordered list records a cyclic traversal, with an implicit closing edge.',
 'geo:areas':'Area is the normalized alternating bilinear determinant. A triangle has half the parallelogram area. This is constructed and characterized, not installed as a global axiom.',
 'geo:boundary':'Add the rational contributions of successive edges, including the closing edge. No absolute value, simplicity or convexity assumption is used.',
 'geo:fan':'Expand every triangle into its three boundary contributions. The radial edges cancel, leaving the polygon boundary. This works for any rational fan point.',
 'geo:cyclic':'Cut the same cyclic list at a different vertex. Its boundary-edge sum is unchanged.',
 FANS:'The vertex-fan computation gives the same rational area for every starting vertex. For nonconvex and self-crossing cycles this is an oriented sum, not necessarily a disjoint triangulation. Reversing the traversal reverses area.',
 'geo:transforms':'One affine transformation theorem gives translation invariance, area preservation for determinant-one maps, reflection sign, and quadratic scaling. A proper rigid motion is a special case.',
 'geo:volume':'The ordered tetrahedron uses determinant divided by six. Subdivision and cubic scaling are exact finite identities. This panel does not claim a completed theory of arbitrary polyhedral surfaces.',
 'geo:computation':'The original midpoint-refinement evaluator is retained. Its stage is exactly the displayed pair of rational sums, with gap at most 4 raised to minus the stage. Numerical instructions do not call the new polygon-area theory.',
 'geo:validity':'Orderedness, nesting and shrinking widths are proved for the existing rational program. This proof does not use the new polygonal interpretation. It is a separate certificate, not a premise needed for a finite stage equality.',
 'geo:circle-polygons':'The inner list follows the rational circle samples; the outer list inserts rational tangent intersections. Both are traversed in the positive orientation. Nonnegativity is proved for these lists, not assumed for arbitrary cycles.',
 QUARTER:'At every stage the existing interval endpoints equal the new polygon areas exactly. Either endpoint can be computed using any rational fan point and any starting vertex. Together with the independent validity proof, these are the quarter-circle area computation.'}

def path(nodes,start,goal,kind):
    prev={start:None};queue=deque([start])
    while queue:
        n=queue.popleft()
        if n==goal:
            out=[]
            while n is not None:out.append(n);n=prev[n]
            return out
        d=nodes[n]
        keys=['bodyRefs','typeRefs']
        if n==start and kind=='proof':keys=['bodyRefs']
        if kind=='statement':
            if n==start:keys=['typeRefs']
            elif d['kind']=='theorem':continue
            else:keys=['bodyRefs','typeRefs']
        for x in sorted({x for key in keys for x in d[key]}):
            if x not in prev:prev[x]=n;queue.append(x)
    return None

MAPS={FANS:[
 ('geo:points','geo:areas',G+'triangleArea',G+'Point','construction'),
 ('geo:points','geo:boundary',G+'area',G+'det','construction'),
 ('geo:areas','geo:fan',G+'fanArea_eq_area',G+'triangle_boundary','proof'),
 ('geo:boundary','geo:cyclic',G+'area_startAt',G+'cycleSum','proof'),
 ('geo:fan',FANS,G+'triangulationArea_startAt',G+'triangulationArea_eq_area','proof'),
 ('geo:cyclic',FANS,G+'triangulationArea_startAt',G+'area_startAt','proof'),
 ('geo:boundary',FANS,G+'triangulationArea_startAt',G+'area','statement')],
 QUARTER:[
 ('geo:computation','geo:validity',C+'raw_valid',C+'raw','statement'),
 ('geo:points','geo:circle-polygons',C+'innerPolygon',G+'Point','construction'),
 ('geo:points','geo:boundary',G+'area',G+'det','construction'),
 ('geo:boundary',FANS,G+'triangulationArea_startAt',G+'area','statement'),
 ('geo:computation',QUARTER,C+'raw_compute_any_fans',C+'raw','statement'),
 ('geo:circle-polygons',QUARTER,C+'raw_compute_polygon_areas',C+'inner_area_nonneg','proof'),
 (FANS,QUARTER,C+'raw_compute_any_fans',G+'fanArea_startAt','proof'),
 ('geo:boundary',QUARTER,C+'raw_compute_polygon_areas',G+'area','statement')]}

def graph(model,audit,target,site,revision):
    nodes={x['id']:x for x in audit['nodes']};specs=MAPS[target]
    ids=sorted({s for s,_,_,_,_ in specs}|{t for _,t,_,_,_ in specs})
    witnesses=[]
    for source,dest,start,goal,kind in specs:
        witness=path(nodes,start,goal,kind)
        if not witness:raise ValueError(('Missing dependency',source,dest,start,goal,kind))
        witnesses.append(dict(source=source,target=dest,witness=witness,kind=kind,route=0 if kind=='proof' else None,
          globalEdge=True,map=target,label='Finite proof' if kind=='proof' else 'Objects in the statement' if kind=='statement' else 'Definition dependency'))
    lines=['digraph G { rankdir=TB; bgcolor="transparent"; nodesep="0.3"; ranksep="0.5";',
      'node [shape=box,style="rounded,filled",fillcolor="#eef3ed",color="#879a8c",fontname="Helvetica",fontsize=12,margin=".14,.12"];',
      'edge [arrowhead=vee,arrowsize=.65];']
    for key in ids:lines.append(json.dumps(key)+' [label='+json.dumps(GROUPS[key][0])+'];')
    for w in witnesses:lines.append(json.dumps(w['source'])+' -> '+json.dumps(w['target'])+' [color="'+('#326493' if w['kind']=='proof' else '#202020')+'"];')
    lines.append('}')
    result=subprocess.run(['dot','-Tsvg'],input='\n'.join(lines),text=True,capture_output=True,check=True).stdout
    svg=parse(result).svg
    svg.attrs.pop('width',None);svg.attrs.pop('height',None)
    for g in svg.select('g.node'):
        key=g.title.get_text();g['data-node']=key;g['role']='button';g['tabindex']='0';g['aria-label']=GROUPS[key][0]
    for g in svg.select('g.edge'):
        edge=g.title.get_text();a,b=edge.split('->');record=next(x for x in witnesses if x['source']==a and x['target']==b)
        g['data-edge']=edge;g['data-edge-kind']=record['kind'];g['role']='button';g['tabindex']='0'
    filename='reading/'+('rational-polygon-fans' if target==FANS else 'quarter-circle-geometry')+'.svg'
    (site/filename).write_text(str(svg))
    model['witnesses']+=witnesses
    model['theorems'][target]=dict(id=target,title=GROUPS[target][0],sink=target,checkedComparison=False,
      verifiedGraph=True,proofSourceCommit=revision,status='Checked rational geometry · definitions and finite proof dependencies',
      page='ch-circle-sphere.html',views={'all':filename},routeNames=['Finite geometry'])
    return witnesses


def install(site,revision,audit_path):
    audit=json.loads(audit_path.read_text());assert all(audit['checks'].values())
    cards={d['name']:d for d in audit['declarations']}
    model=json.loads((site/'reading/maps.json').read_text());old=copy.deepcopy(model)
    protected={str(p.relative_to(site)):digest(p) for p in site.rglob('*') if p.is_file()
      and str(p.relative_to(site)) not in ['ch-circle-sphere.html','reading/maps.json','reading/graph.js']}
    for key,(title,names) in GROUPS.items():
        declarations=[]
        for name in names:
            d=copy.deepcopy(cards[name]);d['realDependencyPath']=[]
            d['sourceUrl']=f'https://github.com/liuyao12/computable-analysis/blob/{revision}/'+d['ownerModule'].replace('.','/')+'.lean'
            declarations.append(d)
        model['bundles'][key]=dict(title=title,anchors=names,declarations=declarations,declarationCount=len(declarations),
          groups=[dict(title='Definitions and checked statements',names=names)],classification='native',
          mathHtml='<p>'+DESCRIPTIONS[key]+'</p>',strategy=dict(role='Finite geometry',summary='',groups={}))
    witnesses=[]
    for target in MAPS:witnesses+=graph(model,audit,target,site,revision)
    page=site/'ch-circle-sphere.html';doc=parse(page.read_text());body=doc.select_one('.main-text')
    figure=doc.find(id='fig:rational-parameter-line');assert figure
    anchor=next(h for h in body.find_all('h2',recursive=False) if 'Circumference and sector length' in h.get_text())
    tail=[copy.deepcopy(x) for x in [anchor,*anchor.next_siblings]]
    original_tail=''.join(str(x) for x in tail)
    opening,sections=render_opening((ROOT/'blueprint/src/02-rational-geometry.tex').read_text(),figure)
    h1=copy.deepcopy(body.h1);body.clear();body.append(h1)
    for x in list(opening.contents):body.append(x)
    marker=doc.new_tag('span',id='rational-geometry-original-tail');body.append(marker)
    for x in tail:body.append(x)
    # Renumber only section headings; original tail prose and displayed equations stay unchanged.
    for h in marker.find_next_siblings('h2'):
        h.string=re.sub(r'^2\.(\d+)',lambda m:'2.'+str(int(m[1])+sections-2),h.get_text())
    toc=doc.select_one('.on-this-page');toc.clear();title=doc.new_tag('span');title.string='On this page';toc.append(title)
    for h in body.find_all('h2'):
        a=doc.new_tag('a',href='#'+h['id']);a.string=h.get_text();toc.append(a)
    for ident,target,groups in [
      ('thm:quarter-circle-raw',QUARTER,['geo:computation','geo:validity']),
      (FANS,FANS,['geo:fan',FANS]),
      (QUARTER,QUARTER,[QUARTER])]:
        h=doc.find(id=ident);wrapper=doc.new_tag('section',attrs={'class':'geometry-theorem'})
        h.insert_before(wrapper);items=[];node=h
        while node is not None and (node is h or getattr(node,'name',None) not in ['h2','h3']):
            items.append(node);node=node.next_sibling
        for x in items:wrapper.append(x.extract())
        aside=parse('<aside class="theorem-margin"><a data-proof-map="'+target+'" href="proof-map.html?theorem='+target+'">Proof map ↗</a><small>Checked finite geometry</small></aside>').aside
        wrapper.append(aside)
        detail=doc.new_tag('details',attrs={'class':'geometry-statements'});summary=doc.new_tag('summary');summary.string='Exact Lean definitions and statements';detail.append(summary)
        for group in groups:
            title=doc.new_tag('h4');title.string=GROUPS[group][0];detail.append(title)
            for d in model['bundles'][group]['declarations']:
                pre=doc.new_tag('pre');code=doc.new_tag('code');code.string=d['kind']+' '+d['name']+' : '+d['type']+(' :=\n'+d['value'] if d.get('value') is not None else '')
                pre.append(code);detail.append(pre)
                a=doc.new_tag('a',href=d['sourceUrl'],target='_blank',rel='noopener');a.string='Pinned Lean source ↗';detail.append(a)
        wrapper.append(detail)
    style=doc.new_tag('style',id='rational-geometry-style');style.string='''
.geometry-theorem{position:relative;margin:1.5rem 0}.geometry-statements{margin:1rem 0;font-size:13px}
.geometry-statements pre{white-space:pre;overflow-x:auto;max-width:100%;padding:14px;background:#f3f5f2;font:12px/1.65 monospace}
.geometry-statements a{font:11px system-ui}.geometry-statements h4{font:600 13px system-ui;margin-top:1.5rem}
@media(max-width:900px){.geometry-theorem .theorem-margin{position:static;display:block;width:auto;margin:1rem 0}}
''';doc.head.append(style)
    script=doc.new_tag('script',src='reading/lean-highlight.js',defer='');doc.head.append(script)
    init=doc.new_tag('script');init.string="window.addEventListener('DOMContentLoaded',()=>document.querySelectorAll('.geometry-statements code').forEach(c=>window.LeanSnippet?.highlight(c)));";doc.body.append(init)
    marker.extract();doc.find(id=anchor['id']).insert_before(marker)
    page.write_text(str(doc))
    (site/'reading/maps.json').write_text(json.dumps(model,separators=(',',':')))
    js=site/'reading/graph.js';s=js.read_text();s=s.replace('model.proofSourceCommit.slice(0,12)','(entry.proofSourceCommit||model.proofSourceCommit).slice(0,12)');js.write_text(s)
    for k in ['theorems','bundles']:
        assert all(model[k][key]==value for key,value in old[k].items())
    assert model['witnesses'][:len(old['witnesses'])]==old['witnesses']
    for p,h in protected.items():assert digest(site/p)==h,p
    record=dict(documentationRevision=revision,newProofSourceCommit=revision,baseProofSourceCommit=old['proofSourceCommit'],
      checks=audit['checks'],newTheoremMaps=[FANS,QUARTER],exactDeclarationCount=len(cards),theoremRoots=len(audit['audits']),
      earlierTheoremEntriesUnchanged=True,integralDefinitionsUnchanged=True,chapterOneUnchanged=True,
      areaConvention='Oriented area is called area; a polygon is an ordered list read cyclically.',
      originalTail=original_tail,protectedArtifacts=protected,newEdgeWitnesses=witnesses,
      sourceOpeningSha256=digest(ROOT/'blueprint/src/02-rational-geometry.tex'))
    (site/'reading/rational-geometry.json').write_text(json.dumps(audit,separators=(',',':')))
    (site/'reading/rational-geometry-edition.json').write_text(json.dumps(record,indent=2)+'\n')
    print('PASS: computation first; cyclic polygons and arbitrary fans; exact stage-area bridge; integrals and earlier proof comparisons unchanged')

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--site',type=Path,required=True);p.add_argument('--revision',required=True);p.add_argument('--audit',type=Path,required=True);a=p.parse_args();install(a.site,a.revision,a.audit)
