#!/usr/bin/env python3
"""Reader-only edition over an immutable, verified proof snapshot.
No Lean declarations or measurements are changed. The gallery is a teaser,
not a claim that every representation bridge is already formalized.
The cosine illustration uses exact radical/polygon bounds, not Lean outputs.
"""
from __future__ import annotations
import argparse, hashlib, json, re
from fractions import Fraction as Q
from functools import lru_cache
from math import isqrt
from pathlib import Path
from bs4 import BeautifulSoup
from PIL import Image, ImageDraw
from cosine_illustrations import label as render_label, make_circle_animation

TITLE = 'Computable Analysis'
SUBTITLE = 'An alternative foundation to Calculus'
PROOF_SHA = 'f630241adeae35fc06a5fd4921a4df6396e291d0'
BITS = 72
FORMULAS = [
 ('pi-geometry','Geometric sector area',r'\pi=4A(1)','ch-circle-sphere.html','Rational polygons give the geometric starting point.'),
 ('pi-arctan','Rational-kernel quadrature',r'\frac{\pi}{4}=\int_0^1\frac{dx}{1+x^2}','cosine.html#the-clock','Geometric area and finite rectangle sums.'),
 ('pi-leibniz','Leibniz series',r'\frac{\pi}{4}=\sum_{j=0}^{\infty}\frac{(-1)^j}{2j+1}','ch-infinite-series.html','Finite prefixes and an alternating remainder.'),
 ('pi-brouncker','Brouncker continued fraction',r'\frac4\pi=1+\cfrac{1^2}{2+\cfrac{3^2}{2+\cfrac{5^2}{2+\ddots}}}','pi-computations.html#programme','Finite convergents and rational recurrence identities.'),
 ('pi-wallis','Wallis product',r'\frac\pi2=\prod_{j=1}^{\infty}\frac{4j^2}{4j^2-1}','integral-families.html#thm:wallis-product','Integration by parts gives rational product bounds.'),
 ('pi-basel','Euler–Basel series',r'\frac{\pi^2}{6}=\sum_{j=1}^{\infty}\frac1{j^2}','pi-computations.html#programme','A series computation and its identification with geometric area.'),
 ('pi-arcsine','Reciprocal-square-root quadrature',r'\frac\pi6=\int_0^{1/2}\frac{dx}{\sqrt{1-x^2}}','pi-computations.html#programme','Algebraic evaluation, separated reciprocals and substitution.'),
 ('pi-segment','Circle-segment quadrature',r'\frac\pi{12}+\frac{\sqrt3}{8}=\int_0^{1/2}\sqrt{1-x^2}\,dx','pi-computations.html#programme','Finite geometry and the product rule.'),
 ('pi-gaussian','Gaussian quadrature',r'\sqrt{2\pi}=\int_{-\infty}^{\infty}e^{-x^2/2}\,dx','pi-computations.html#programme','Exponential evaluation, finite multidimensional sums and tail bounds.'),
 ('pi-cosine','Cosine quadrature',r'\frac1\pi=\int_0^{1/2}\cos(\pi x)\,dx','dyadic-integral.html','Dyadic samples from nested radicals; the construction comes later.')]
CSS = '''
.book-subtitle{font:normal 20px/1.5 Georgia,serif;color:var(--muted);margin:-12px 0 30px!important}
.pi-teaser{border-left:2px solid #9caf98;background:#f1f4ed;padding:18px 23px;margin:26px 0 35px}
.pi-teaser h2{font-size:23px;margin:0 0 10px}.pi-teaser p{font-size:16px;margin:8px 0}
.pi-teaser .displaymath{font-size:23px;margin:16px 0}.pi-teaser a{font:12px/1.6 system-ui}
.pi-gallery{margin:30px 0}.pi-gallery>h2{margin-bottom:15px}
.pi-gallery-grid{display:grid;grid-template-columns:repeat(2,minmax(0,1fr));gap:0 23px}
.pi-formula-card{min-width:0;padding:18px 0;border-top:1px solid var(--line)}
.pi-formula-card h3{font:normal 18px/1.4 Georgia,serif;margin:0 0 14px}
.pi-formula-card .formula{overflow-x:auto;max-width:100%;font-size:16px;padding:3px 0}
.pi-formula-card .formula mjx-container[display=true]{margin:.7em 0!important}
.pi-formula-card p,.pi-formula-card a{font:11px/1.65 system-ui;color:var(--muted);margin:10px 0 0}
.pi-gallery-note{font:12px/1.65 system-ui;color:var(--muted)}
.pi-gallery-link{font-size:12px!important}.header-about{max-width:280px;text-align:right}
.reader .equal-scale-animation{max-width:760px}.equal-scale-animation img{aspect-ratio:800/640}
@media(max-width:720px){.pi-gallery-grid{grid-template-columns:1fr}.pi-teaser{padding:16px}.pi-teaser .displaymath{font-size:20px}.book-subtitle{font-size:18px}.pi-formula-card .formula{font-size:17px}}
'''

def parse(text): return BeautifulSoup(text,'html.parser')
def digest(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def snippet(text): return list(parse(text).contents)

def gallery():
    cards=''.join(f'<article class="pi-formula-card" id="{key}"><h3>{name}</h3><div class="formula">\\[{formula}\\]</div><p>{description}</p><a href="{url}">Construction and context →</a></article>' for key,name,formula,url,description in FORMULAS)
    return f'''<section id="pi-computations" class="pi-gallery" data-edition-addition="pi-gallery"><h2>Many computations of π</h2><p>Geometry, series, continued fractions and integrals give different computations of one number. Their equivalences are mathematical theorems, not definitions of the same instructions.</p><div class="pi-gallery-grid">{cards}</div><p class="pi-gallery-note">A preview of the programme. Each construction needs its own rational enclosures, convergence certificate and identification with geometric π. This list does not assert that every listed identity has already been formalized.</p><p class="pi-gallery-link"><a href="pi-computations.html#programme">Read the construction and equivalence programme →</a></p></section>'''

def root_interval(lo,hi):
    scale=1<<BITS
    a=isqrt(lo.numerator*scale*scale//lo.denominator)
    b=isqrt(hi.numerator*scale*scale//hi.denominator)
    if b*b*hi.denominator < hi.numerator*scale*scale:b+=1
    out=Q(a,scale),Q(b,scale)
    assert out[0]**2<=lo<=hi<=out[1]**2
    return out

@lru_cache(maxsize=None)
def grid(d):
    """cos(pi*j/(2*2**d)) through positive half-angle roots only."""
    if d==0:return ((Q(1),Q(1)),(Q(0),Q(0)))
    old=grid(d-1);n=len(old)-1;out=[]
    for j in range(2*n+1):
        if j%2==0:out.append(old[j//2]);continue
        if j<=n:lo,hi=old[j];a,b=(1+lo)/2,(1+hi)/2
        else:lo,hi=old[2*n-j];a,b=(1-hi)/2,(1-lo)/2
        out.append(root_interval(a,b))
    return tuple(out)

def pi_bounds(n):
    """Independent geometric pi=4 A(1), outward dyadic polygon sums."""
    scale=1<<BITS;lo=hi=0
    for j in range(n):
        a,b=Q(j,n),Q(j+1,n)
        l=(b-a)*(1+a*b)/((1+a*a)*(1+b*b));u=(b-a)/(1+a*b)
        lo+=l.numerator*scale//l.denominator
        hi+=-(-u.numerator*scale//u.denominator)
    return Q(4*lo,scale),Q(4*hi,scale)

def decimal(q,upper=False,places=9):
    scale=10**places
    k=-(-q.numerator*scale//q.denominator) if upper else q.numerator*scale//q.denominator
    sign='−' if k<0 else '';k=abs(k)
    return f'{sign}{k//scale}.{k%scale:0{places}d}'

def example(d):
    samples=grid(d);n=1<<d;h=Q(1,2*n)
    lo=h*sum((p[0] for p in samples[1:]),Q(0));hi=h*sum((p[1] for p in samples[:-1]),Q(0))
    pl,ph=pi_bounds(max(64,n));rl,rh=1/ph,1/pl
    assert lo<=hi and max(lo,rl)<=min(hi,rh)
    return dict(depth=d,cells=n,upperLimit='1/2',lower=str(lo),upper=str(hi),
                reciprocalLower=str(rl),reciprocalUpper=str(rh),
                integralDisplay=[decimal(lo),decimal(hi,True)],reciprocalDisplay=[decimal(rl),decimal(rh,True)])

def table(rows):
    body=''.join(f'<tr><td>{r["cells"]}</td><td>[{", ".join(r["integralDisplay"])}]</td><td>[{", ".join(r["reciprocalDisplay"])}]</td></tr>' for r in rows)
    return f'<div class="numeric-scroll" data-edition-addition="half-interval-table"><table class="numerical-bounds"><caption>Upper endpoint 1/2 in every row; decimal bounds rounded outwards.</caption><thead><tr><th>Cells</th><th>Radical rectangle integral</th><th>Independent geometric 1/π</th></tr></thead><tbody>{body}</tbody></table></div>'

def make_animation(out):
    """Fixed [0,1/2], equal pixel scales, refining sample bounds, not a moving t."""
    out.mkdir(parents=True,exist_ok=True)
    scale=2
    frames=[];rows=[];xy=lambda x,y:(148+300*float(x),422-300*float(y))
    for d in range(1,5):
        row=example(d);rows.append(row);samples=grid(d);n=1<<d
        im=Image.new('RGB',(1600,1280),'#faf9f5');draw=ImageDraw.Draw(im)
        def text(x,y,t,size=16,color='#27382f',serif=False):render_label(im,x,y,t,size,color,serif)
        def line(points,color,width=1):draw.line([(int(x*scale),int(y*scale)) for x,y in points],fill=color,width=width*scale)
        def poly(points,color):draw.polygon([(int(x*scale),int(y*scale)) for x,y in points],fill=color)
        text(30,24,'Cosine quadrature',27,serif=True)
        text(30,68,r'Fixed interval $[0, 1/2]$ · equal $x$ and $y$ scales · dyadic refinement',16,color='#758176')
        for tick in [Q(0),Q(1,4),Q(1,2),Q(3,4),Q(1)]:
            x,y=xy(0,tick);line([(x-5,y),(x+150,y)],'#e2e5db')
            text(x-51,y-11,'$'+str(tick)+'$',13)
        for j in range(n):
            a,b=Q(j,2*n),Q(j+1,2*n);l=samples[j+1][0];u=samples[j][1]
            poly([xy(a,0),xy(a,l),xy(b,l),xy(b,0)],'#dce8d7')
            poly([xy(a,l),xy(a,u),xy(b,u),xy(b,l)],'#ede0c9')
            line([xy(a,l),xy(b,l)],'#456d55',1);line([xy(a,u),xy(b,u)],'#a87a46',1)
        curve=grid(8);line([xy(Q(j,512),(a+b)/2) for j,(a,b) in enumerate(curve)],'#27382f',2)
        for j,(a,b) in enumerate(samples):
            x,y=xy(Q(j,2*n),(a+b)/2);r=2 if n<=16 else 1
            draw.ellipse(((x-r)*scale,(y-r)*scale,(x+r)*scale,(y+r)*scale),fill='#27382f')
        line([xy(0,0),xy(Q(11,20),0)],'#7a877b',1);line([xy(0,0),xy(0,Q(21,20))],'#7a877b',1)
        for tick,label in [(Q(0),'0'),(Q(1,4),'1/4'),(Q(1,2),'1/2')]:
            x,y=xy(tick,0);line([(x,y),(x,y+5)],'#7a877b');text(x-12,y+13,'$'+label+'$',13)
        text(317,428,'$x$',16);text(149,96,'$y$',16)
        text(362,145,r'$y = \cos(\pi x)$',24,serif=True)
        text(362,196,r'Upper endpoint: $1/2$',17)
        text(362,228,rf'$n = {d}$; ${n}$ cells; $h = 1/{2*n}$',17)
        text(362,273,'Right endpoints: lower sum',16,color='#456d55')
        text(362,306,'Left endpoints: upper sum',16,color='#a87a46')
        text(362,357,r'$1$ unit = $300$ pixels on both axes',14,color='#758176')
        text(30,486,'Rectangle bounds for the integral',17)
        text(30,515,'$['+', '.join(row['integralDisplay'])+']$',23,color='#456d55')
        text(438,486,r'Geometric $1/\pi$, independently',17)
        text(438,521,'$['+', '.join(row['reciprocalDisplay'])+']$',17)
        text(30,579,r'The sample evaluator uses nested radicals; geometric $\pi$ uses polygon areas.',15,color='#758176')
        text(30,607,'Illustrative rational bounds, not literal Lean output stages.',14,color='#758176')
        frames.append(im.resize((800,640),Image.Resampling.LANCZOS))
    palette=frames[0].quantize(colors=192)
    indexed=[im.quantize(palette=palette,dither=Image.Dither.NONE) for im in frames]
    indexed[0].save(out/'cosine.gif',save_all=True,append_images=indexed[1:],duration=[1600]*3+[2800],loop=0,disposal=2,optimize=False)
    frames[2].save(out/'cosine.png')
    return dict(upperLimit='1/2',fixedEndpoint=True,xPixelsPerUnit=300,yPixelsPerUnit=300,
                plotWidthPixels=150,plotHeightPixels=300,frames=rows,
                table=[example(d) for d in [3,5,7,9]],leanStageExecution=False,
                method='Independent positive half-angle radical samples and geometric polygon reciprocal bounds.',
                gifSha256=digest(out/'cosine.gif'),posterSha256=digest(out/'cosine.png'))

def remove_label(s):
    return re.sub(r'Computable calculus','Computable Analysis',s,flags=re.IGNORECASE)

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--site',type=Path,required=True);ap.add_argument('--revision',required=True)
    args=ap.parse_args();site=args.site;reading=site/'reading'
    manifest=json.loads((reading/'manifest.json').read_text())
    assert manifest['sourceCommit']==manifest['proofSourceCommit']==PROOF_SHA
    assert manifest['preservedFirstTwo'] and manifest['cartwrightComplete'] and manifest['integralPortfolio']
    protected={str(p.relative_to(site)):digest(p) for p in site.rglob('*') if p.is_file() and
        (p.suffix=='.svg' or p.suffix=='.json' and p.name not in ['maps.json','analysis-edition.json','cosine-half-interval.json'] or 'reference' in p.parts)}
    maps=json.loads((reading/'maps.json').read_text())
    semantic_before=json.dumps({'witnesses':maps['witnesses'],'theorems':maps['theorems'],
       'declarations':{k:b['declarations'] for k,b in maps['bundles'].items()}},sort_keys=True)
    animation=make_animation(reading/'animations')
    circle_animation=make_circle_animation(reading/'animations')
    (reading/'cosine-half-interval.json').write_text(json.dumps(animation,indent=2)+'\n')
    (reading/'analysis-edition.css').write_text(CSS)
    updated=[]
    original_foundation=None
    for p in sorted(site.glob('*.html')):
        text=p.read_text();doc=parse(text)
        if not doc.select_one('main.reader'):
            if doc.title and 'Computable calculus' in doc.title.get_text():
                doc.title.string=remove_label(doc.title.get_text());p.write_text(str(doc))
            continue
        if p.name=='ch-foundations.html':original_foundation=re.sub(r'\s+',' ',doc.article.get_text(' ',strip=True))
        if doc.title:doc.title.string=remove_label(doc.title.get_text())
        brand=doc.select_one('a.brand')
        if brand:
            brand.clear();brand.append('Computable ');em=doc.new_tag('em');em.string='Analysis';brand.append(em)
        about=doc.select_one('.header-about')
        if about:about.string=SUBTITLE
        if not doc.select_one('link[href="reading/analysis-edition.css"]'):
            doc.head.append(doc.new_tag('link',rel='stylesheet',href='reading/analysis-edition.css'))
        meta=doc.select_one('meta[name="documentation-revision"]') or doc.new_tag('meta',attrs={'name':'documentation-revision'})
        meta['content']=args.revision
        if not meta.parent:doc.head.append(meta)
        nav=doc.select_one('#book-nav')
        if nav and not nav.select_one('.pi-catalogue-navigation'):
            a=doc.new_tag('a',href='pi-computations.html',attrs={'class':'pi-catalogue-navigation'});a.string='Computations of π'
            first=nav.select_one('a[href="ch-foundations.html"]')
            if first:first.insert_after(a)
            else:nav.append(a)
        if p.name=='index.html':
            heading=doc.select_one('article h1');heading.clear();heading.append('Computable ')
            em=doc.new_tag('em');em.string='Analysis';heading.append(em)
            subtitle=doc.new_tag('p',attrs={'class':'book-subtitle'});subtitle.string=SUBTITLE
            heading.insert_after(subtitle)
            teaser=parse(r'''<section id="pi-computations" class="pi-teaser" data-edition-addition="pi-teaser"><h2>Many computations of π</h2><p>One number, many independent constructions. A first glimpse:</p><h3>Cosine quadrature</h3><div class="displaymath">\[\boxed{\frac1\pi=\int_0^{1/2}\cos(\pi x)\,dx.}\]</div><p><a href="ch-foundations.html#pi-computations">Explore the catalogue in Chapter 1 →</a> · <a href="pi-computations.html">All π computations →</a></p></section>''').section
            lead=doc.select_one('article p.lead');lead.insert_after(teaser)
            doc.title.string=TITLE+' — '+SUBTITLE
        if p.name=='ch-foundations.html':
            section=parse(gallery()).section
            anchor=doc.find(id='rem:calculus-as-equivalence')
            assert anchor,'Preserve the existing chapter and insert beside its pi destinations'
            anchor.insert_before(section)
            toc=doc.select_one('.on-this-page')
            if toc:
                a=doc.new_tag('a',href='#pi-computations');a.string='Many computations of π';toc.append(a)
            original=parse(str(doc.article));original.select_one('#pi-computations').decompose()
            assert re.sub(r'\s+',' ',original.get_text(' ',strip=True))==original_foundation
        if p.name=='cosine.html':
            figure=doc.select_one('[data-animation="cosine"]');figure['class']=['math-animation','equal-scale-animation']
            figure.figcaption.string=r'Fixed upper limit \(1/2\). Equal \(x\)/\(y\) scale; right lower and left upper rectangles refine at dyadic sample points. The geometric reciprocal is evaluated independently.'
            figure.img['alt']='Equal-scale cosine plot on [0,1/2] with dyadic rectangle bounds and independent geometric reciprocal bounds.'
            doc.select_one('[data-animation="arctan"] figcaption').string=r'Subdivide the vertical segment from \(0\) to \(u\) equally, then project every mark from \((-1,0)\) to the circle. Here \(u=2/3\); stage \(n\) has \(2^n\) subdivisions. At \(u=1\) its sector is a quarter disk, hence \(\pi=4A(1)\).'
            old=figure.find_next_sibling('div',class_='numeric-scroll');assert old
            old.replace_with(parse(table(animation['table'])).div)
        p.write_text(str(doc));updated.append(p.name)
    catalogue=parse((site/'index.html').read_text());catalogue.title.string='Computations of π · '+TITLE
    catalogue.article.clear()
    contents='<h1>Computations of π</h1><p class="lead">Different algorithms, one computed number.</p>'+gallery()+r'''<section id="programme"><h2>Construction and equivalence</h2><p>The formulas above are a preview, not imported definitions. For each one, first prescribe a finite rational-enclosure algorithm and prove that its outputs are valid. Then identify it with geometric π by a separate theorem. The comparison should expose both the computation and the proof route.</p><p><a href="cosine.html">Cosine quadrature</a>, <a href="dyadic-integral.html">dyadic radical evaluation</a> and <a href="integral-families.html">Wallis bounds</a> already have published checked developments. The catalogue does not promote the remaining local experiments or unfinished representation bridges to completed Lean results.</p><p>The restored gallery reconstructs the mathematical catalogue; it is not a recovered copy of the earlier image file. The original chapter text and checked theorem data remain unchanged.</p><h2>Cosine quadrature at equal scale</h2><div class="displaymath">\[\frac1\pi=\int_0^{1/2}\cos(\pi x)\,dx.\]</div><figure class="math-animation equal-scale-animation" data-animation="cosine"><img src="reading/animations/cosine.gif" width="800" height="640" alt="Equal-scale plot of cosine on [0,1/2] with refining rational rectangle bounds."/><figcaption>The upper endpoint stays at 1/2. Numerical rectangle bounds use nested-radical samples; the reciprocal of geometric π is computed separately.</figcaption><button type="button" data-animation-toggle>Pause animation</button></figure>'''+table(animation['table'])+'''<p class="pi-gallery-note">These are outward-rounded rational illustrations, not literal Lean output stages. Display agreement is not a substitute for the formal theorem.</p></section>'''
    for c in snippet(contents):catalogue.article.append(c)
    toc=catalogue.select_one('.on-this-page');toc.clear()
    for c in snippet('<span>On this page</span><a href="#pi-computations">The catalogue</a><a href="#programme">Construction and equivalence</a>'):toc.append(c)
    (site/'pi-computations.html').write_text(str(catalogue))
    # Only explanatory HTML/captions change, never a declaration or edge.
    for key in ['def:c3-integrals','thm:c3-primitive']:
        b=maps['bundles'].get(key,{})
        if b.get('illustration',{}).get('id')=='cosine':
            b['illustration']['alt']='Equal-scale cosine quadrature on [0,1/2].'
            b['illustration']['caption']='Fixed upper endpoint 1/2; equal axis scales. Independent radical rectangle and geometric reciprocal bounds; not literal Lean output stages.'
        body=parse(b.get('mathHtml',''))
        for old in body.select('.numeric-scroll'):old.replace_with(parse(table(animation['table'])).div)
        b['mathHtml']=str(body).replace('t = 1/3','t = 1/2').replace('t=1/3','t=1/2')
    semantic_after=json.dumps({'witnesses':maps['witnesses'],'theorems':maps['theorems'],
       'declarations':{k:b['declarations'] for k,b in maps['bundles'].items()}},sort_keys=True)
    assert semantic_after==semantic_before
    (reading/'maps.json').write_text(json.dumps(maps,separators=(',',':')))
    # Original animation audit remains historical; this edition records its override separately.
    for file,expected in protected.items():assert digest(site/file)==expected,file
    record=dict(title=TITLE,subtitle=SUBTITLE,documentationRevision=args.revision,proofSourceCommit=PROOF_SHA,
       chapterOneCatalogue=True,homeTeaser=True,formula=r'\frac1\pi=\int_0^{1/2}\cos(\pi x)\,dx',
       originalChapterOneTextPreserved=True,proofDeclarationsAndEdgesUnchanged=True,newLeanProofsClaimed=False,
       updatedReaderPages=updated,protectedArtifacts=protected,cosineAnimation=animation,circleAnimation=circle_animation,
       originalImageRecovered=False)
    (reading/'analysis-edition.json').write_text(json.dumps(record,indent=2)+'\n')
    print('PASS: Computable Analysis; home teaser; Chapter 1 gallery; fixed half-interval/equal-scale GIF; proof data unchanged')

if __name__=='__main__':main()
