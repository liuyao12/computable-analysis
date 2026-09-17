#!/usr/bin/env python3
"""Expanded mathematical flashcards. This module adds no Lean proof claims.

The Log(i) example sums four local logarithm series along the rational path
1,(3+i)/4,(1+i)/2,(1+3i)/4,i. All numerical enclosures are exact rationals.
Newton is displayed in modern unit-circle normalization, not as a transcript.
"""
from __future__ import annotations
from fractions import Fraction as Q
from math import comb
import json
from bs4 import BeautifulSoup

NEWTON_SOURCE='https://www.newtonproject.ox.ac.uk/view/texts/normalized/NATP00356'
NEWTON_NOTEBOOK='https://www.newtonproject.ox.ac.uk/view/texts/normalized/NATP00128'
LOG_SOURCE='https://github.com/liuyao12/computable-analysis/blob/3ca1758ff07b9fa90777aae7102ef42fc935900b/blueprint/src/05-logarithm-continuation.tex'
LOG_INPUTS=((Q(-1,4),Q(1,4)),(Q(-1,5),Q(2,5)),(Q(0),Q(1,2)),(Q(1,5),Q(2,5)))
LOG_PATH=((Q(1),Q(0)),(Q(3,4),Q(1,4)),(Q(1,2),Q(1,2)),(Q(1,4),Q(3,4)),(Q(0),Q(1)))

CSS='''
.pi-formula-card details{margin:14px 0 0!important;border-top:0!important;padding:0!important}
.pi-formula-card details summary{font:11px/1.6 system-ui;color:var(--green);cursor:pointer}
.pi-formula-card details p{font-size:12px;line-height:1.65}
.pi-formula-card .formula{font-size:15px}.pi-formula-card .formula-derivation{font-size:14px}
.pi-calculation-scroll{max-width:100%;overflow-x:auto}.pi-calculation-table{font:11px/1.7 system-ui;font-variant-numeric:tabular-nums}
.pi-calculation-table td{white-space:nowrap;padding:7px}.pi-calculation-table caption{text-align:left;font:11px/1.6 system-ui;padding:10px 0}
.pi-calculation-status{font:11px/1.7 system-ui!important;color:var(--muted)}
@media(max-width:720px){.pi-formula-card .formula{font-size:16px}.pi-formula-card .formula-derivation{font-size:14px}}
'''

def parse(text):return BeautifulSoup(text,'html.parser')
def math(text,extra=''):return '<div class="formula '+extra+'">\\['+text+'\\]</div>'
def mul(a,b):return (a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0])
def outward(x,upper=False,places=12):
    scale=10**places
    k=-((-x.numerator*scale)//x.denominator) if upper else x.numerator*scale//x.denominator
    sign='-' if k<0 else '';k=abs(k)
    return f'{sign}{k//scale}.{k%scale:0{places}d}'

def log_prefix(n):
    if n<1:raise ValueError('A positive number of terms is required')
    total=(Q(0),Q(0))
    for w in LOG_INPUTS:
        power=(Q(1),Q(0))
        for k in range(1,n+1):
            power=mul(power,w);coefficient=Q((-1)**(k+1),k)
            total=tuple(total[j]+coefficient*power[j] for j in (0,1))
    radius=Q(4,(n+1)*2**n)
    return dict(termsPerStep=n,real=str(total[0]),imaginary=str(total[1]),radius=str(radius),
      realBox=[str(total[0]-radius),str(total[0]+radius)],
      imaginaryBox=[str(total[1]-radius),str(total[1]+radius)],
      realDisplay=[outward(total[0]-radius),outward(total[0]+radius,True)],
      imaginaryDisplay=[outward(total[1]-radius),outward(total[1]+radius,True)])

def integrated_binomial(positive_root=True,count=6):
    coefficient=Q(1);out=[];alpha=Q(1,2) if positive_root else Q(-1,2)
    for k in range(count):
        if k:coefficient*= (alpha-(k-1))/k
        out.append((-1)**k*coefficient/Q((2*k+1)*2**(2*k+1)))
    return out

def numerical_record():
    return dict(version=1,calculation='Four continued local logarithm series, using exact Gaussian-rational arithmetic',
      branch='Continuation from 1 with Log(1)=0 along the straight segment to i; no winding',
      path=[[str(a),str(b)] for a,b in LOG_PATH],inputs=[[str(a),str(b)] for a,b in LOG_INPUTS],
      localModulusBound='1/2',complexErrorBound='4 / ((N+1) * 2^N)',
      rows=[log_prefix(n) for n in (8,16,32,64)],
      newtonIntegratedTerms=list(map(str,integrated_binomial())),
      arcsineIntegratedTerms=list(map(str,integrated_binomial(False))),
      usesNumericalPi=False,leanStageExecution=False,newLeanProofsClaimed=False,
      formalizationStatus='Local continuation evaluator and identification theorem are not yet Lean-certified.',
      historicalSources=[NEWTON_SOURCE,NEWTON_NOTEBOOK])

def check_arithmetic(record):
    assert record==numerical_record()
    product=(Q(1),Q(0))
    for j,w in enumerate(LOG_INPUTS):
        assert w[0]*w[0]+w[1]*w[1]<=Q(1,4)
        ratio=(1+w[0],w[1]);assert mul(LOG_PATH[j],ratio)==LOG_PATH[j+1]
        product=mul(product,ratio)
    assert product==(Q(0),Q(1))
    assert integrated_binomial()==[Q(1,2),-Q(1,48),-Q(1,1280),-Q(1,14336),-Q(5,589824),-Q(7,5767168)]
    for k,term in enumerate(integrated_binomial(False)):
        assert term==Q(comb(2*k,k),4**k*(2*k+1)*2**(2*k+1))
    previous=None
    for row in record['rows']:
        radius=Q(row['radius']);n=row['termsPerStep']
        assert radius==4*Q(1,2)**(n+1)/((n+1)*(1-Q(1,2)))
        for name,key in [('real','realBox'),('imaginary','imaginaryBox')]:
            lo,hi=map(Q,row[key]);centre=Q(row[name]);assert lo==centre-radius and hi==centre+radius
            dlo,dhi=map(Q,row[name+'Display']);assert dlo<=lo<=hi<=dhi
        assert Q(row['realBox'][0])<=0<=Q(row['realBox'][1])
        if previous:
            for name in ['realBox','imaginaryBox']:
                a,b=map(Q,previous[name]);c,d=map(Q,row[name]);assert a<=c<=d<=b
        previous=row
    assert record['rows'][-1]['imaginaryDisplay']==['1.570796326794','1.570796326795']


def log_detail(record):
    rows=''.join('<tr><td>'+str(r['termsPerStep'])+'</td><td>['+', '.join(r['imaginaryDisplay'])+']</td></tr>' for r in record['rows'])
    return r'''<p>Continue the logarithm with initial value zero at 1 along the straight segment to i. Four rational steps fix the branch without supplying any value of π:</p>'''+math(r'1\to\frac{3+i}{4}\to\frac{1+i}{2}\to\frac{1+3i}{4}\to i','formula-derivation')+r'''<p>Use the local series</p>'''+math(r'\ell(w)=w-\frac{w^2}{2}+\frac{w^3}{3}-\frac{w^4}{4}+\cdots','formula-derivation')+math(r'\begin{aligned}\operatorname{Log}(i)={}&\ell\!\left(\frac{-1+i}{4}\right)+\ell\!\left(\frac{-1+2i}{5}\right)\\&+\ell\!\left(\frac i2\right)+\ell\!\left(\frac{1+2i}{5}\right).\end{aligned}','formula-derivation')+r'''<p>All four inputs have modulus at most 1/2. Let L<sub>N</sub> be the sum of their N-term prefixes. Exact rational arithmetic supplies the approximation, and the geometric tail gives</p>'''+math(r'\left|\operatorname{Log}(i)-L_N\right|\le\frac{4}{(N+1)2^N}.','formula-derivation')+'<div class="pi-calculation-scroll"><table class="pi-calculation-table"><caption>Enclosures of Im Log(i); decimal endpoints rounded outwards.</caption><thead><tr><th>Terms per step</th><th>Imaginary part</th></tr></thead><tbody>'+rows+'</tbody></table></div>'+r'''<p>The same tail bounds the real component; it converges to zero. The branch chosen by this path is the principal value at i.</p><p class="pi-calculation-status">Illustrative rational computation, not literal Lean output. The continuation and its equivalence to geometric π remain formalization targets.</p>'''+f'<a href="{LOG_SOURCE}" target="_blank" rel="noopener">Continuation construction in the chapter manuscript →</a>'


def render_cards(record):
    # The ordinary integral notation remains a teaser. The work chapters specify
    # finite evaluators and certificates; an equation here is not a proof badge.
    specs=[
      ('pi-geometry','Geometric sector area',r'\pi=4A(1)',
       'Rational polygons give the geometric starting point.',None,'ch-circle-sphere.html'),
      ('pi-arctan','Rational-kernel quadrature',r'\frac\pi4=\int_0^1\frac{dx}{1+x^2}',
       'Geometric area meets rational rectangle sums.',
       math(r'\frac1{1+x^2}=1-x^2+x^4-x^6+\cdots\quad(|x|<1)','formula-derivation')+'<p>Finite geometric-series remainders justify the integral comparison, including its endpoint.</p>', 'cosine.html#the-clock'),
      ('pi-leibniz','Leibniz series',r'\frac\pi4=1-\frac13+\frac15-\frac17+\frac19-\cdots',
       'Odd reciprocals with alternating signs.',None,'ch-infinite-series.html'),
      ('pi-brouncker','Brouncker continued fraction',r'\frac4\pi=1+\cfrac{1^2}{2+\cfrac{3^2}{2+\cfrac{5^2}{2+\cfrac{7^2}{2+\ddots}}}}',
       'Successive odd squares in a continued fraction.',
       '<p>Terminating the displayed fraction after successive odd-square numerators gives</p>'+math(r'\frac32,\quad\frac{15}{13},\quad\frac{105}{76},\quad\frac{315}{263},\quad\ldots','formula-derivation'), '#pi-computation-programme'),
      ('pi-wallis','Wallis product',r'\frac\pi2=\frac{2\cdot2}{1\cdot3}\,\frac{4\cdot4}{3\cdot5}\,\frac{6\cdot6}{5\cdot7}\cdots',
       'A rational product, with checked geometric-π bounds.',None,'integral-families.html#thm:wallis-product'),
      ('pi-basel','Euler–Basel series',r'\frac{\pi^2}{6}=1+\frac1{2^2}+\frac1{3^2}+\frac1{4^2}+\cdots',
       'Reciprocal squares and a separate geometric identification.',None,'#pi-computation-programme'),
      ('pi-arcsine','Reciprocal-square-root quadrature',r'\begin{aligned}\frac\pi6&=\int_0^{1/2}\frac{dx}{\sqrt{1-x^2}}\\&=\frac12+\frac1{48}+\frac3{1280}\\&\quad+\frac5{14336}+\cdots\end{aligned}',
       'The positive binomial coefficients, integrated term by term.',
       math(r'(1-x^2)^{-1/2}=1+\frac{x^2}{2}+\frac{3x^4}{8}+\frac{5x^6}{16}+\cdots','formula-derivation'), '#pi-computation-programme'),
      ('pi-segment','Newton',r'\begin{aligned}\frac\pi{12}+\frac{\sqrt3}{8}&=\frac12-\frac1{48}-\frac1{1280}\\&\quad-\frac1{14336}-\frac5{589824}-\cdots\end{aligned}',
       'Binomial series for a circle segment.',
       math(r'\sqrt{1-x^2}=1-\frac{x^2}{2}-\frac{x^4}{8}-\frac{x^6}{16}-\frac{5x^8}{128}-\cdots','formula-derivation')+math(r'\int_0^{1/2}\sqrt{1-x^2}\,dx=\frac\pi{12}+\frac{\sqrt3}{8}','formula-derivation')+r'''<p>Expand the ordinate by the generalized binomial theorem, integrate the powers, and evaluate at 1/2. The rational terms then decrease rapidly. This is a modern unit-circle normalization of Newton's circle-quadrature method.</p>'''+f'<p>A landmark use of infinite series for quadrature. See Newton’s <a href="{NEWTON_SOURCE}" target="_blank" rel="noopener">account of the method</a> and <a href="{NEWTON_NOTEBOOK}" target="_blank" rel="noopener">mathematical notebook</a>.</p>', '#pi-computation-programme'),
      ('pi-gaussian','Gaussian quadrature',r'\sqrt{2\pi}=\int_{-\infty}^{\infty}e^{-x^2/2}\,dx',
       'Exponential evaluation and an explicit improper tail.',
       math(r'e^{-x^2/2}=1-\frac{x^2}{2}+\frac{x^4}{8}-\frac{x^6}{48}+\cdots','formula-derivation')+math(r'\int_{-R}^{R}e^{-x^2/2}\,dx=2R-\frac{R^3}{3}+\frac{R^5}{20}-\frac{R^7}{168}+\cdots','formula-derivation')+'<p>The integrated expansion is for a fixed finite R. It is not integrated term by term over the whole real line; the remaining tails require a separate bound.</p>', '#pi-computation-programme'),
      ('pi-logarithm','Complex logarithm',r'\frac{i\pi}{2}=\operatorname{Log}(i)',
       'Continue from Log(1)=0 along the straight segment to i.',log_detail(record),None)
    ]
    cards=[]
    for key,title,formula,description,detail,link in specs:
        body=f'<article class="pi-formula-card" id="{key}"><h3>{title}</h3>'+math(formula)+f'<p>{description}</p>'
        if detail:body+='<details class="pi-formula-details"><summary>'+('A specific calculation of Log(i)' if key=='pi-logarithm' else 'Expansion and context')+'</summary>'+detail+'</details>'
        if link:body+=f'<a href="{link}">Construction and context →</a>'
        cards.append(body+'</article>')
    return ''.join(cards)


def install(chapter,site,revision):
    record=numerical_record();check_arithmetic(record)
    gallery=chapter.select_one('#pi-computations');grid=gallery.select_one('.pi-gallery-grid')
    assert grid
    grid.clear()
    for card in list(parse(render_cards(record)).contents):grid.append(card)
    style=chapter.find(id='pi-expanded-cards-style')
    if not style:
        style=chapter.new_tag('style',id='pi-expanded-cards-style');chapter.head.append(style)
    style.string=CSS
    assert len(grid.select('.pi-formula-card'))==10 and not grid.select('#pi-cosine')
    (site/'reading/pi-flashcards-calculation.json').write_text(json.dumps(dict(documentationRevision=revision,**record),indent=2)+'\n')
    return dict(formulaCount=10,expandedSeries=True,newtonBinomialCard=True,logContinuationCard=True,
                logarithmCalculation='reading/pi-flashcards-calculation.json',newLeanProofsClaimed=False)
