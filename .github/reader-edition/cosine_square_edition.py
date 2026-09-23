#!/usr/bin/env python3
"""Install the checked squared-cosine showcase after the preserved reader passes.
The new proofs are built against the exact pinned mathematical foundation.
"""
import argparse, hashlib, json, re, shutil
from fractions import Fraction as Q
from pathlib import Path
from bs4 import BeautifulSoup
from PIL import Image, ImageDraw
from analysis_edition import grid, decimal, PROOF_SHA
from cosine_illustrations import label, SCALE, PAPER, INK, GREEN, GOLD, AREA, GAP, MUTED

ROOT=Path(__file__).resolve().parents[2]
SOURCE=ROOT/'book/cosine-square'
TITLE='The cosine-square integral'

def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def xy(x,y):return 148+300*float(x),422-300*float(y)
def line(im,points,color=INK,width=1):
    ImageDraw.Draw(im).line([(round(x*SCALE),round(y*SCALE)) for x,y in points],fill=color,width=round(width*SCALE))
def polygon(im,points,color):
    ImageDraw.Draw(im).polygon([(round(x*SCALE),round(y*SCALE)) for x,y in points],fill=color)
def axes(im):
    for v in [Q(0),Q(1,2),Q(1)]:
        x,y=xy(0,v);line(im,[(x-5,y),(x+150,y)],'#e2e5db');label(im,x-34,y-7,'$'+str(v)+'$',14)
    line(im,[xy(0,0),xy(Q(11,20),0)],'#7a877b')
    line(im,[xy(0,0),xy(0,Q(21,20))],'#7a877b')
    for v in [Q(0),Q(1,4),Q(1,2)]:
        x,y=xy(v,0);line(im,[(x,y),(x,y+5)],'#7a877b');label(im,x-9,y+14,'$'+str(v)+'$',14)
    label(im,320,428,'$x$',17);label(im,148,96,'$y$',17)
def curve():return [(Q(j,512),((lo+hi)/2)**2) for j,(lo,hi) in enumerate(grid(8))]
def save_animation(out,name,frames,durations,poster):
    frames=[im.resize((800,640),Image.Resampling.LANCZOS) for im in frames]
    palette=frames[-1].quantize(colors=192)
    indexed=[im.quantize(palette=palette,dither=Image.Dither.NONE) for im in frames]
    indexed[0].save(out/(name+'.gif'),save_all=True,append_images=indexed[1:],duration=durations,loop=0,disposal=2,optimize=False)
    frames[poster].save(out/(name+'.png'))
    return {ext:digest(out/(name+'.'+ext)) for ext in ['gif','png']}

def row(n):
    samples=grid(n);N=2**n;h=Q(1,2*N)
    lo=h*sum((a*a for a,b in samples[1:]),Q(0))
    hi=h*sum((b*b for a,b in samples[:-1]),Q(0))
    assert lo<=Q(1,4)<=hi
    return dict(stage=n,cells=N,lower=str(lo),upper=str(hi),display=[decimal(lo),decimal(hi,True)])

def rectangles(out):
    frames=[];rows=[row(n) for n in range(1,5)]
    for r in rows:
        n=r['stage'];N=r['cells'];samples=grid(n)
        im=Image.new('RGB',(1600,1280),PAPER)
        label(im,30,24,'The cosine-square integral',27,serif=True)
        label(im,30,68,r'$[0,1/2]$ · equal axis scales · refining rectangle bounds',16,MUTED)
        axes(im)
        for j in range(N):
            a,b=Q(j,2*N),Q(j+1,2*N);lo=samples[j+1][0]**2;hi=samples[j][1]**2
            polygon(im,[xy(a,0),xy(a,lo),xy(b,lo),xy(b,0)],AREA)
            polygon(im,[xy(a,lo),xy(a,hi),xy(b,hi),xy(b,lo)],GAP)
            line(im,[xy(a,lo),xy(b,lo)],GREEN);line(im,[xy(a,hi),xy(b,hi)],GOLD)
        line(im,[xy(x,y) for x,y in curve()],INK,2)
        label(im,358,143,r'$y=\cos^2(\pi x)$',25)
        label(im,358,198,rf'$n={n}$; ${N}$ equal cells',18)
        label(im,358,248,'Right rectangles: lower bound',16,GREEN)
        label(im,358,281,'Left rectangles: upper bound',16,GOLD)
        label(im,358,345,r'$\int_0^{1/2}\cos^2(\pi x)\,dx=\frac{1}{4}$',23)
        label(im,30,491,'Outward-rounded area bounds',17)
        label(im,30,527,'$['+',\;'.join(r['display'])+']$',25,GREEN)
        label(im,30,593,'Nested-radical illustration; the Lean program uses rational-circle samples.',14,MUTED)
        frames.append(im)
    hashes=save_animation(out,'cosine-square',frames,[1600]*3+[2800],2)
    return dict(frames=rows,hashes=hashes,mathFont='Computer Modern',equalAxisScale=300,
                illustrationMethod='Squared positive half-angle radical enclosures; outward rational arithmetic.',literalLeanStages=False)

def symmetry(out):
    frames=[];durations=[];points=curve()
    # Three clear endpoint states, with smooth motion of the copied area.
    states=[(0.,0.,'The original area',1800)]
    states += [(k/12,0.,'Reflect the copy horizontally',90) for k in range(1,13)]
    states += [(1.,0.,'Reflection preserves area',1800)]
    states += [(1.,k/12,'Turn the copy vertically',90) for k in range(1,13)]
    states += [(1.,1.,'Two equal areas fill the rectangle',3000)]
    shape=[(Q(0),Q(0))]+points+[(Q(1,2),Q(0))]
    for horizontal,vertical,caption,duration in states:
        im=Image.new('RGB',(1600,1280),PAPER)
        label(im,30,24,'One symmetry, two equal areas',27,serif=True)
        label(im,30,68,r'$f(x)=\cos^2(\pi x)$',18,MUTED)
        polygon(im,[xy(x,y) for x,y in shape],AREA)
        overlay=Image.new('RGBA',im.size,(0,0,0,0))
        transformed=[xy((1-horizontal)*float(x)+horizontal*(.5-float(x)),(1-vertical)*float(y)+vertical*(1-float(y))) for x,y in shape]
        polygon(overlay,transformed,(205,156,82,140))
        im=Image.alpha_composite(im.convert('RGBA'),overlay).convert('RGB')
        axes(im);line(im,[xy(x,y) for x,y in points],GREEN,2)
        label(im,360,149,r'$f\!\left(\frac{1}{2}-x\right)=\sin^2(\pi x)$',21)
        label(im,360,214,r'$\cos^2(\pi x)+\sin^2(\pi x)=1$',21)
        label(im,360,292,r'$I+I=\frac{1}{2}$',27)
        label(im,360,355,r'$I=\frac{1}{4}$',29,GREEN)
        label(im,30,500,caption,21)
        label(im,30,552,r'Reflect in $x=1/4$, then in $y=1/2$.',17,MUTED)
        label(im,30,596,r'Each endpoint transformation preserves area.',15,MUTED)
        frames.append(im);durations.append(duration)
    return dict(hashes=save_animation(out,'cosine-square-symmetry',frames,durations,-1),frames=len(frames),mathFont='Computer Modern')

def table():
    rows=[row(n) for n in [1,2,3,4,6,8]]
    body=''.join(f'<tr><td>\\({r["stage"]}\\)</td><td>\\({r["cells"]}\\)</td><td>\\([{r["display"][0]}, {r["display"][1]}]\\)</td></tr>' for r in rows)
    return '<div class="numeric-scroll"><table class="numerical-bounds square-stage-table"><caption>Independent rational illustrations; all bounds round outwards.</caption><thead><tr><th>Stage \\(n\\)</th><th>Cells</th><th>Enclosure of the area</th></tr></thead><tbody>'+body+'</tbody></table></div>',rows

def source_link(revision,file):return f'https://github.com/liuyao12/computable-analysis/blob/{revision}/book/cosine-square/{file}'

def graph_html(revision):
    base=f'https://github.com/liuyao12/computable-analysis/blob/{PROOF_SHA}/ComputableAnalysis/'
    source=lambda f:source_link(revision,'ComputableAnalysis/'+f)
    nodes=[
      ('shared','Geometric input','Circle coordinates and their identities',r'\(C^2+S^2=1\)',
       'Rational polygons define the angle clock. Closed inversion supplies the sine and cosine coordinates; complementary angles exchange them.',base+'ClockTrigIdentities.lean'),
      ('shared','One computation','The squared-cosine rectangle program',r'\(I_n\to I\)',
       'Square rational-circle samples on a dyadic mesh. A proved error bound, prefix intersection, and range clipping produce valid nested intervals. The program does not use its eventual value.',source('CosineSquareData.lean')),
      ('symmetry','Reflection','Pair the left and right cells',r'\(f(x)+f(1/2-x)=1\)',
       'Finite reflection reverses the grid. The Pythagorean identity cancels the paired squared heights, up to explicit sample error.',source('CosineSquareSymmetry.lean')),
      ('ftc','Derivative certificate','Build the product primitive',r'\(F(x)=x/2+S(x)C(x)/(2\pi)\)',
       'The sine and cosine derivative certificates combine by the product rule. Rational algebra and the circle identity give the squared-cosine derivative.',source('CosineSquareFTC.lean')),
      ('symmetry','Finite error bound','The paired area is one half',r'\(2I=1/2\)',
       'The endpoint rectangle gap and the evaluation error tend to zero. The selected sums approach the rational target without any primitive.',source('CosineSquareSymmetry.lean')),
      ('ftc','Finite FTC','Telescope, then evaluate the endpoints',r'\(I=F(1/2)-F(0)\)',
       'Telescope the primitive increments on each fixed mesh, compare with the independently chosen sums, and let the mesh refine. The endpoint product tends to zero.',source('CosineSquareFTC.lean')),
      ('shared','Same checked conclusion','The actual integral computes one quarter',r'\(I\simeq 1/4\)',
       'Both exported proofs establish <code>RealRaw.Equiv</code> for exactly the same valid integral evaluator. The audit checks that neither value proof depends on the other.',source('CosineSquareData.lean'))]
    parts=[]
    for route,tag,title,formula,body,href in nodes:
        attrs='data-common="true"' if route=='shared' else f'data-proof-route="{route}"'
        parts.append(f'<article class="{route}" {attrs}><p class="step">{tag}</p><h3>{title}</h3><div class="math">{formula}</div><p>{body}</p><p class="refs"><a href="{href}">Pinned Lean source ↗</a></p></article>')
    return '''<h1>Two proofs of the cosine-square integral</h1><p class="lead">One independently defined interval program; two checked evaluations.</p><nav class="square-map-routes" aria-label="Proof route"><button data-square-route="all" aria-pressed="true">Both proofs</button><button data-square-route="symmetry" aria-pressed="false">Symmetry</button><button data-square-route="ftc" aria-pressed="false">FTC</button></nav><div class="square-flow">'''+''.join(parts)+'''</div><p class="square-map-note">Read each route from top to bottom. These are mathematical dependency bundles; the complete elaborated declaration dependencies are in the audit. The FTC uses complementary-angle geometry to establish the cosine derivative, but does not use the symmetry evaluation of the integral.</p><p><a href="reading/cosine-square-proofs.json">Theorem types, axioms, and both dependency closures</a> · <a href="cosine.html">Back to the worked example</a></p>'''

def install(site,revision,audit_path):
    assert re.fullmatch('[0-9a-f]{40}',revision)
    assert not (site/'reading/cosine-square-edition.json').exists(), 'Build from the preserved reader before applying this edition'
    audit=json.loads(audit_path.read_text());assert all(audit['checks'].values())
    expected=['integral_valid','integral_width','integral_via_symmetry','integral_via_FTC']
    assert [d['name'].split('.')[-1] for d in audit['declarations'][:4]]==expected
    index=set((SOURCE/'lean_decls').read_text().splitlines())
    assert {d['name'] for d in audit['declarations']}==index
    assert all('sorryAx' not in d['axioms'] for d in audit['declarations'])
    original={str(p.relative_to(site)):digest(p) for p in site.rglob('*') if p.is_file()}
    worked=site/'cosine.html';old=worked.read_text()
    (site/'cosine-primitive.html').write_text(old)
    olddoc=BeautifulSoup(old,'html.parser')
    for a in olddoc.select('a[href="cosine.html"]'):a['href']='cosine-primitive.html'
    back=olddoc.new_tag('p',attrs={'class':'square-source'});link=olddoc.new_tag('a',href='cosine.html');link.string='Return to the cosine-square example →';back.append(link);olddoc.article.insert(0,back)
    (site/'cosine-primitive.html').write_text(str(olddoc))
    out=site/'reading';anim=out/'animations';anim.mkdir(exist_ok=True)
    rectangle=rectangles(anim);reflection=symmetry(anim)
    tab,rows=table()
    page=(SOURCE/'page.html').read_text().replace('__TABLE__',tab)
    for key,file in [('__SYMMETRY_SOURCE__','ComputableAnalysis/CosineSquareSymmetry.lean'),('__FTC_SOURCE__','ComputableAnalysis/CosineSquareFTC.lean'),('__PACKAGE_SOURCE__','README.md')]:page=page.replace(key,source_link(revision,file))
    doc=BeautifulSoup(old,'html.parser');doc.title.string=TITLE+' · Computable Analysis'
    doc.select_one('meta[name="documentation-revision"]')['content']=revision
    footer=doc.select_one('.chapter-footer a')
    if footer:footer['href']=source_link(revision,'README.md');footer.string='Source '+revision[:8]+' ↗'
    doc.article.clear()
    for node in list(BeautifulSoup(page,'html.parser').contents):doc.article.append(node)
    doc.head.append(doc.new_tag('link',rel='stylesheet',href='reading/cosine-square.css'))
    toc=doc.select_one('.on-this-page')
    if toc:
        toc.clear()
        for id,title in [('the-clock','The circle coordinates'),('numerical-comparison','The computation'),('symmetry','Proof by symmetry'),('ftc','Proof by FTC'),('mean-square','Mean-square amplitude'),('checked-result','Checked formalization')]:
            a=doc.new_tag('a',href='#'+id);a.string=title;toc.append(a)
    worked.write_text(str(doc))
    graph=BeautifulSoup(str(doc),'html.parser');graph.title.string='Cosine-square integral · Proof routes';graph.article.clear()
    for node in list(BeautifulSoup(graph_html(revision),'html.parser').contents):graph.article.append(node)
    if graph.select_one('.on-this-page'):graph.select_one('.on-this-page').decompose()
    graph.head.append(graph.new_tag('script',src='reading/cosine-square-graph.js',defer=''))
    (site/'cosine-square-proofs.html').write_text(str(graph))
    shutil.copyfile(SOURCE/'style.css',out/'cosine-square.css')
    shutil.copyfile(SOURCE/'graph.js',out/'cosine-square-graph.js')
    # All book navigation to the showcase gets the new name; old theorem links
    # and the original formal comparison remain attached to the support page.
    changed=[]
    for p in site.rglob('*.html'):
        if 'reference' in p.parts:continue
        text=p.read_text()
        text=re.sub(r'(<a\b[^>]*href="(?:\.\./)?cosine\.html"[^>]*>)The cosine primitive(</a>)',r'\1The cosine-square integral\2',text)
        text=re.sub(r'(href=")((?:\.\./)?)cosine\.html#cosine-primitive',r'\1\2cosine-primitive.html#cosine-primitive',text)
        if text!=p.read_text():p.write_text(text)
    maps_path=out/'maps.json';maps=json.loads(maps_path.read_text())
    oldtheorem=maps['theorems']['thm:c3-primitive'];oldtheorem['page']='cosine-primitive.html'
    maps_path.write_text(json.dumps(maps,separators=(',',':')))
    shutil.copyfile(audit_path,out/'cosine-square-proofs.json')
    current={str(p.relative_to(site)):digest(p) for p in site.rglob('*') if p.is_file()}
    changed={name:{'before':sha,'after':current.get(name)} for name,sha in original.items() if current.get(name)!=sha}
    protected={name:sha for name,sha in original.items() if name not in changed}
    report=dict(documentationRevision=revision,proofRevision=revision,baseProofRevision=PROOF_SHA,
      target=r'\int_0^{1/2}\cos^2(\pi x)\,dx=\frac{1}{4}',newLeanProofsClaimed=True,
      checkedTheorems=[d['name'] for d in audit['declarations']],checks=audit['checks'],
      rectangleAnimation=rectangle,symmetryAnimation=reflection,illustrationTable=rows,
      previousCosinePrimitive='cosine-primitive.html',changedArtifacts=changed,protectedArtifacts=protected,
      artifacts={name:sha for name,sha in current.items() if name not in original or name in changed})
    (out/'cosine-square-edition.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: checked cosine-square showcase, both proof routes, animations and preserved support theorem')
    return report

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--site',type=Path,required=True);p.add_argument('--revision',required=True);p.add_argument('--audit',type=Path,required=True)
    args=p.parse_args();install(args.site,args.revision,args.audit)
