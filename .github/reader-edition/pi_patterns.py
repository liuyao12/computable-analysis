#!/usr/bin/env python3
"""Factored Newton terms, Machin, and alternative rational Log(i) computations.

Reader-only enrichment after the existing flashcard pass. No numerical pi/log
is supplied and no new Lean equivalence or benchmark is claimed. All error
boxes use rational arithmetic. Each logarithm identity uses the same branch.
"""
from __future__ import annotations
import argparse, hashlib, json
from fractions import Fraction as Q
from math import factorial
from pathlib import Path
from bs4 import BeautifulSoup

TAYLOR_INPUTS=((Q(-1,4),Q(1,4)),(Q(-1,5),Q(2,5)),(Q(0),Q(1,2)),(Q(1,5),Q(2,5)))
CAYLEY_INPUTS=((Q(-1,5),Q(2,5)),(Q(1,5),Q(2,5)))
ONE=(Q(1),Q(0)); I=(Q(0),Q(1))
SOURCE='https://arxiv.org/html/2601.10300v1#S1.E1'

def parse(s): return BeautifulSoup(s,'html.parser')
def formula(s): return '<div class="formula">\\['+s+'\\]</div>'
def mul(a,b): return (a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0])
def add(a,b): return (a[0]+b[0],a[1]+b[1])
def div(a,b):
    d=b[0]**2+b[1]**2
    if not d: raise ValueError('Nonzero denominator required')
    z=mul(a,(b[0],-b[1])); return (z[0]/d,z[1]/d)
def power(z,n):
    out=ONE
    for _ in range(n): out=mul(out,z)
    return out

def outward(x,upper=False,places=12):
    scale=10**places
    k=-((-x.numerator*scale)//x.denominator) if upper else x.numerator*scale//x.denominator
    sign='-' if k<0 else '';k=abs(k)
    return f'{sign}{k//scale}.{k%scale:0{places}d}'

def error_label(q):
    """An outward-rounded three-significant-digit scientific upper bound."""
    e=0
    while q<Q(10)**e: e-=1
    unit=Q(10)**(e-2);r=q/unit;k=-(-r.numerator//r.denominator)
    return f'{k/100:.2f} × 10^{e}'

def atan_prefix(q,n):
    if not 0<q<1 or n<1: raise ValueError('0<q<1 and positive term count required')
    return sum(((-1)**k*q**(2*k+1)/Q(2*k+1) for k in range(n)),Q(0))

def approximation(method,n):
    if n<1: raise ValueError('Positive term count required')
    total=(Q(0),Q(0))
    if method=='local-taylor':
        for w in TAYLOR_INPUTS:
            p=ONE
            for k in range(1,n+1):
                p=mul(p,w);c=Q((-1)**(k+1),k)
                total=add(total,(c*p[0],c*p[1]))
        radius=Q(4,(n+1)*2**n)
    elif method=='symmetric-log':
        for w in CAYLEY_INPUTS:
            p=w;square=mul(w,w)
            for k in range(n):
                c=Q(2,2*k+1);total=add(total,(c*p[0],c*p[1]));p=mul(p,square)
        # |w| <= 1/2 and |w|² = 1/5 for both inputs.
        radius=Q(5,2*(2*n+1)*5**n)
    elif method=='machin':
        total=(Q(0),8*atan_prefix(Q(1,5),n)-2*atan_prefix(Q(1,239),n))
        radius=Q(8,(2*n+1)*5**(2*n+1))+Q(2,(2*n+1)*239**(2*n+1))
    else: raise ValueError('Unknown method')
    return dict(method=method,termsPerSeries=n,real=str(total[0]),imaginary=str(total[1]),radius=str(radius),
        realBox=[str(total[0]-radius),str(total[0]+radius)],
        imaginaryBox=[str(total[1]-radius),str(total[1]+radius)],
        imaginaryDisplay=[outward(total[1]-radius),outward(total[1]+radius,True)],
        radiusDisplay=error_label(radius))

def log_one_approximation(n):
    if n<1: raise ValueError('Positive term count required')
    q=(Q(1,5),Q(2,5));square=mul(q,q);p=q;total=(Q(0),Q(0))
    for k in range(n):
        c=Q(2,2*k+1);total=add(total,(c*p[0],c*p[1]));p=mul(p,square)
    value=4*total[1];radius=Q(5,(2*n+1)*5**n)
    return dict(terms=n,logReal=str(total[0]),logImaginary=str(total[1]),
        pi=str(value),radius=str(radius),box=[str(value-radius),str(value+radius)],
        display=[outward(value-radius),outward(value+radius,True)])

def log_one_record():
    return dict(argument=['1','1'],seriesInput=['1/5','2/5'],
        branch='Log(1)=0 on the right half-plane; straight segment to 1+i',
        rows=[log_one_approximation(n) for n in (4,8,16,32)],
        usesNumericalPi=False,usesNumericalLog=False,usesNumericalArctan=False,
        newLeanProofsClaimed=False)

def check_log_one(r):
    q=(Q(1,5),Q(2,5))
    assert div(add(ONE,q),(1-q[0],-q[1]))==(Q(1),Q(1))
    assert q[0]**2+q[1]**2==Q(1,5)<Q(1,4)
    for row in r['rows']:
        n=row['terms'];v=Q(row['pi']);bound=Q(row['radius'])
        assert bound==8*Q(1,2)*Q(1,5)**n/((2*n+1)*(1-Q(1,5)))
        assert v==2*Q(approximation('symmetric-log',n)['imaginary'])
        # Compare independently computed Machin enclosures; not a proof of the tail.
        independent=approximation('machin',n)
        assert max(v-bound,2*Q(independent['imaginaryBox'][0]))<=min(v+bound,2*Q(independent['imaginaryBox'][1]))
        assert list(map(Q,row['box']))==[v-bound,v+bound]
        assert Q(row['display'][0])<=v-bound<=v+bound<=Q(row['display'][1])
        later=log_one_approximation(n+1)
        assert abs(v-Q(later['pi']))<=bound+Q(later['radius'])

def log_one_fragment(r):
    rows=''.join('<tr><td>\\('+str(x['terms'])+'\\)</td><td>\\(['+',\\;'.join(x['display'])+']\\)</td><td>\\(\\frac{5}{'+str(2*x['terms']+1)+r'\cdot5^{'+str(x['terms'])+'}}\\)</td></tr>' for x in r['rows'])
    table='<div class="pi-calculation-scroll"><table class="log-one-table"><caption>Rational enclosures of \\(\\pi\\)</caption><thead><tr><th>\\(N\\)</th><th>Enclosure</th><th>Error bound</th></tr></thead><tbody>'+rows+'</tbody></table></div>'
    return (Path(__file__).resolve().parents[2]/'book/pi-log-one-plus-i.html').read_text().replace('__LOG_ONE_TABLE__',table)

def newton_data(count=8):
    a=Q(1,2);out=[]
    for k in range(1,count+1):
        t=a/Q((2*k+1)*2**(2*k+1))
        out.append(dict(k=k,coefficient=str(a),integratedTerm=str(t),
            nextTermRatio=str(Q((2*k-1)*(2*k+1),4*(2*k+2)*(2*k+3)))))
        a*=Q(2*k-1,2*k+2)
    return out

def record():
    return dict(version=2,formulaCount=11,newtonFactored=True,machinCard=True,
        branch='Principal value at i, obtained from Log(1)=0 with no extra winding',
        logarithmMethods=['local-taylor','symmetric-log','machin'],
        logOnePlusI=log_one_record(),
        comparisons=[approximation(m,n) for n in (4,8,16,32,64)
            for m in ('local-taylor','symmetric-log','machin')],
        newtonTerms=newton_data(),usesNumericalPi=False,usesNumericalLog=False,
        leanStageExecution=False,newLeanProofsClaimed=False,
        note='N counts terms in each series: four series versus two versus two. These are error-bound comparisons, not runtime benchmarks.',
        source=SOURCE)

def check_arithmetic(r):
    assert r==record()
    check_log_one(r['logOnePlusI'])
    product=ONE
    for w in TAYLOR_INPUTS:
        assert w[0]**2+w[1]**2<=Q(1,4)
        product=mul(product,add(ONE,w))
    assert product==I
    product=ONE
    for w in CAYLEY_INPUTS:
        assert w[0]**2+w[1]**2==Q(1,5)
        product=mul(product,div(add(ONE,w),(1-w[0],-w[1])))
    assert product==I
    rotation=lambda q:div((Q(1),q),(Q(1),-q))
    assert div(power(rotation(Q(1,5)),4),rotation(Q(1,239)))==I
    # These rational argument bounds identify the intended branch, not just exp(L)=i.
    # 0 < 2*(4 atan(1/5)-atan(1/239)) < 8/5 < pi; pi>2 follows geometrically.
    assert 0<2*(4*(Q(1,5)-Q(1,3*5**3))-Q(1,239))<Q(8,5)<2
    assert Q(120,119)-Q(1,239)==1+Q(120,119*239)
    terms=r['newtonTerms']
    assert [Q(x['integratedTerm']) for x in terms[:5]]==[Q(1,48),Q(1,1280),Q(1,14336),Q(5,589824),Q(7,5767168)]
    for j,x in enumerate(terms):
        k=x['k'];odd=1
        for v in range(1,2*k-2,2):odd*=v
        assert Q(x['coefficient'])==Q(odd,2**k*factorial(k))
        assert Q(x['integratedTerm'])==Q(odd,2**(3*k+1)*factorial(k)*(2*k+1))
        ratio=Q(x['nextTermRatio']);assert 0<ratio<Q(1,4)
        if j+1<len(terms):assert Q(terms[j+1]['integratedTerm'])==Q(x['integratedTerm'])*ratio
    for row in r['comparisons']:
        n=row['termsPerSeries'];radius=Q(row['radius'])
        if row['method']=='symmetric-log':
            assert radius==4*Q(1,2)*Q(1,5)**n/((2*n+1)*(1-Q(1,5)))
            assert Q(row['real'])==0
        if row['method']=='machin':assert Q(row['real'])==0
        for key,centre in [('realBox','real'),('imaginaryBox','imaginary')]:
            a,b=map(Q,row[key]);assert a==Q(row[centre])-radius and b==Q(row[centre])+radius
        a,b=map(Q,row['imaginaryBox']);da,db=map(Q,row['imaginaryDisplay']);assert da<=a<=b<=db
    # Agreement is a regression test, never the justification of a tail bound.
    for n in (4,8,16,32,64):
        rows=[a for a in r['comparisons'] if a['termsPerSeries']==n]
        assert max(Q(a['imaginaryBox'][0]) for a in rows)<=min(Q(a['imaginaryBox'][1]) for a in rows)

NEWTON_MAIN=r'''\begin{aligned}
\frac\pi{12}+\frac{\sqrt3}{8}
&=\frac12-\frac12\frac{(1/2)^3}{3}\\
&\quad-\frac{1\cdot1}{2\cdot4}\frac{(1/2)^5}{5}\\
&\quad-\frac{1\cdot1\cdot3}{2\cdot4\cdot6}\frac{(1/2)^7}{7}\\
&\quad-\frac{1\cdot1\cdot3\cdot5}{2\cdot4\cdot6\cdot8}\frac{(1/2)^9}{9}-\cdots .
\end{aligned}'''
NEWTON_DETAIL=r'''<p>Keep each factor visible. The odd-over-even product is the binomial coefficient; the next odd denominator comes from integrating the power of x, and the power of 1/2 comes from the endpoint.</p>'''+formula(r'''\begin{aligned}\sqrt{1-x^2}=1
&-\frac12 x^2-\frac{1\cdot1}{2\cdot4}x^4\\
&-\frac{1\cdot1\cdot3}{2\cdot4\cdot6}x^6-\cdots .\end{aligned}''')+r'''<p>More precisely, put a<sub>1</sub>=1/2 and</p>'''+formula(r'a_{k+1}=a_k\frac{2k-1}{2k+2},\qquad T_k=\frac{a_k}{(2k+1)2^{2k+1}}.')+formula(r'\frac\pi{12}+\frac{\sqrt3}{8}=\frac12-\sum_{k=1}^{\infty}\frac{(2k-3)!!}{2^{3k+1}k!(2k+1)}.')+r'''<p>The convention is (−1)!!=1. The displayed terms are negative, with magnitudes T<sub>k</sub>. Their recurrence makes a tail bound immediate:</p>'''+formula(r'\frac{T_{k+1}}{T_k}=\frac{(2k-1)(2k+1)}{4(2k+2)(2k+3)}<\frac14,\qquad\sum_{k>m}T_k\le\frac43T_{m+1}.')+r'''<p>This is the same integrated binomial series as before, with its factors left unsimplified. The modern unit-circle normalization and Newton attribution are unchanged.</p><p><a href="https://www.newtonproject.ox.ac.uk/view/texts/normalized/NATP00356" target="_blank" rel="noopener">Newton’s account of his quadrature method →</a></p>'''

MACHIN_MAIN=r'\begin{aligned}\frac\pi4&=4\arctan\!\frac15-\arctan\!\frac1{239}.\end{aligned}'

def machin_card():
    # Keep the flashcard at the arctangent level; numerical details belong
    # to the logarithm comparison rather than a second expanded series here.
    body='<article class="pi-formula-card" id="pi-machin"><h3>Machin</h3>'+formula(MACHIN_MAIN)
    body+='<p>Two rational arctangent values determine π.</p>'
    body+='<a href="#pi-logarithm">The same formula as a logarithm computation →</a></article>'
    card=parse(body).article
    assert len(card.select('.formula'))==1 and not card.select('details')
    assert r'\arctan' in card.get_text() and r'\sum' not in card.get_text()
    return card

def log_methods(r):
    names={'local-taylor':'Four local series','symmetric-log':'Two symmetric series','machin':'Machin combination'}
    rows=''.join('<tr><td>'+str(x['termsPerSeries'])+'</td><td>'+names[x['method']]+'</td><td>['+', '.join(x['imaginaryDisplay'])+']</td><td>'+x['radiusDisplay']+'</td></tr>' for x in r['comparisons'] if x['termsPerSeries'] in (8,16,32))
    return r'''<p>The value is fixed by continuing from Log(1)=0 to i without winding around zero. Different local series, intermediate points and factorizations give genuinely different finite computations of this same branch.</p>
<h4>1. Four local Taylor series</h4><p>Retain the original four steps along the straight segment from 1 to i:</p>'''+formula(r'\ell(w)=w-\frac{w^2}{2}+\frac{w^3}{3}-\cdots')+formula(r'''\begin{aligned}\operatorname{Log}(i)={}&\ell\!\left(\frac{-1+i}{4}\right)+\ell\!\left(\frac{-1+2i}{5}\right)\\&+\ell\!\left(\frac i2\right)+\ell\!\left(\frac{1+2i}{5}\right).\end{aligned}''')+formula(r'|\operatorname{Log}(i)-L_N^{(1)}|\le\frac4{(N+1)2^N}.')+r'''<h4>2. Two symmetric logarithm series</h4><p>Use only the midpoint (1+i)/2. For consecutive points a,b, evaluate the symmetric local series at z=(b−a)/(b+a):</p>'''+formula(r'H(z)=2\left(z+\frac{z^3}{3}+\frac{z^5}{5}+\cdots\right)=\operatorname{Log}\frac{1+z}{1-z}\quad(|z|<1).')+formula(r'\operatorname{Log}(i)=H\!\left(\frac{-1+2i}{5}\right)+H\!\left(\frac{1+2i}{5}\right).')+r'''<p>Both inputs have squared modulus 1/5; the two real parts cancel even in the finite prefixes. For N odd-power terms in each series,</p>'''+formula(r'|\operatorname{Log}(i)-L_N^{(2)}|\le\frac5{2(2N+1)5^N}.')+r'''<h4>3. Machin as a logarithm computation</h4>'''+formula(r'\operatorname{Log}(i)=4H(i/5)-H(i/239).')+r'''<p>The finite Gaussian-rational factorization behind it is</p>'''+formula(r'\left(\frac{5+i}{5-i}\right)^4\frac{239-i}{239+i}=i.')+r'''<p>The local branches are fixed by H(0)=0. The imaginary part of their indicated combination lies between 0 and 8/5, which is less than π (already π&gt;2 geometrically), so no multiple of 2πi can have been silently added. A product identity by itself would not justify this logarithm identity.</p><p>With H<sub>N</sub> denoting the first N odd-power terms of the symmetric series above,</p>'''+formula(r'L_N^{(3)}=4H_N(i/5)-H_N(i/239)')+formula(r'|\operatorname{Log}(i)-L_N^{(3)}|\le\frac8{(2N+1)5^{2N+1}}+\frac2{(2N+1)239^{2N+1}}.')+'<div class="pi-calculation-scroll"><table class="pi-calculation-table"><caption>Independent rational enclosures of Im Log(i). Both decimal endpoints and displayed error bounds round outwards.</caption><thead><tr><th>N</th><th>Method</th><th>Imaginary part</th><th>Error at most</th></tr></thead><tbody>'+rows+'</tbody></table></div>'+r'''<p>N counts terms per series, not total work: the methods evaluate four, two and two series respectively. This is a comparison of certified mathematical tail bounds, not a runtime benchmark.</p><p>Arctangent series are a special case: H(iq)=2i arctan(q). Thus Machin-like formulas and logarithmic factorizations are two views of the same family of algorithms. Other paths or recenterings give more alternatives.</p><p class="pi-calculation-status">Exact rational numerical illustrations, not extracted Lean output. The new continuation and representation bridges remain formalization targets; no new checked proof or proof-length score is claimed.</p><a href="https://dlmf.nist.gov/4.6" target="_blank" rel="noopener">Local logarithm series →</a>'''

CSS='''
.pi-formula-card h4{font:600 12px/1.6 system-ui;margin:20px 0 10px}
#pi-segment>.formula{font-size:15px}
#pi-machin .formula{font-size:14px}
.pi-formula-card .formula{max-width:100%;overflow-x:auto}
.pi-calculation-scroll{max-width:100%;overflow-x:auto}
@media(max-width:720px){#pi-segment>.formula{font-size:14px}#pi-machin .formula{font-size:14px}}
'''

def install(site,revision):
    r=record();check_arithmetic(r)
    p=site/'ch-foundations.html';doc=parse(p.read_text());gallery=doc.select_one('#pi-computations')
    assert gallery and len(gallery.select('.pi-formula-card'))==10 and not gallery.select_one('#pi-cosine')
    protected={str(p.relative_to(site)):hashlib.sha256(p.read_bytes()).hexdigest() for p in site.rglob('*') if p.is_file() and p.name!='ch-foundations.html' and not str(p.relative_to(site)) in ['reading/analysis-edition.json','reading/catalogue-placement.json']}
    before=parse(str(doc.article));before.select_one('#pi-computations').decompose();outside=before.get_text(' ',strip=True)
    newton=gallery.select_one('#pi-segment');newton.select_one('.formula').replace_with(parse(formula(NEWTON_MAIN)).div)
    newton.select_one('.pi-formula-details').replace_with(parse('<details class="pi-formula-details"><summary>Coefficient pattern and tail bound</summary>'+NEWTON_DETAIL+'</details>').details)
    gallery.select_one('#pi-leibniz').insert_after(machin_card())
    log=gallery.select_one('#pi-logarithm');log.select_one('p').string='The imaginary part of a logarithm computes an angle.'
    log.select_one('p').insert_after(parse(formula(r'\pi=4\,\operatorname{Im}\operatorname{Log}(1+i).')).div)
    log.select_one('.pi-formula-details').replace_with(parse('<details class="pi-formula-details"><summary>Three ways to compute Log(i)</summary>'+log_methods(r)+'</details>').details)
    log.select_one('.pi-formula-details').insert_before(parse(log_one_fragment(r['logOnePlusI'])).details)
    style=doc.new_tag('style',id='pi-pattern-style');style.string=CSS;doc.head.append(style)
    assert len(gallery.select('.pi-formula-card'))==11
    assert doc.find(id='rem:sources-of-raw-reals').find_next_sibling()==gallery
    after=parse(str(doc.article));after.select_one('#pi-computations').decompose();assert after.get_text(' ',strip=True)==outside
    p.write_text(str(doc))
    for f,h in protected.items():assert hashlib.sha256((site/f).read_bytes()).hexdigest()==h,f
    for filename in ['analysis-edition.json','catalogue-placement.json']:
        p=site/'reading'/filename;a=json.loads(p.read_text());a.update(documentationRevision=revision,formulaCount=11,newtonFactored=True,machinCard=True,logarithmMethods=r['logarithmMethods'],patternRecord='reading/pi-patterns.json');p.write_text(json.dumps(a,indent=2)+'\n')
    r.update(documentationRevision=revision,protectedArtifacts=protected,originalChapterOutsideGalleryUnchanged=True)
    (site/'reading/pi-patterns.json').write_text(json.dumps(r,indent=2)+'\n')
    print('PASS: Newton factor pattern; Machin arctangent formula; three rational Log(i) computations; original proofs and worked illustrations unchanged')

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--site',type=Path,required=True);ap.add_argument('--revision',required=True);a=ap.parse_args();install(a.site,a.revision)
if __name__=='__main__':main()
