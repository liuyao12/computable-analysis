"""Independent rational illustrations, not executions of the Lean stage programs.

The area clock uses inner/outer rational polygons only. Its inverse uses a
finite table and geometric bounds on sector increments, never sin/cos/pi from
a floating-point library. Integral rectangles never call the endpoint formula.
"""
from __future__ import annotations
from bisect import bisect_left, bisect_right
from fractions import Fraction as Q
from functools import lru_cache

BITS = 60

def point(u):
    return ((1-u*u)/(1+u*u), 2*u/(1+u*u))

def sector_bounds(a, b):
    return ((b-a)*(1+a*b)/((1+a*a)*(1+b*b)), (b-a)/(1+a*b))

def directed(q, places=7, upper=False):
    """Decimal endpoint rounded outwards, without converting to float."""
    q=Q(q); scale=10**places
    k=(-((-q.numerator*scale)//q.denominator) if upper else
       (q.numerator*scale)//q.denominator)
    sign='−' if k<0 else ''; k=abs(k)
    return f'{sign}{k//scale}.{k%scale:0{places}d}'

def dyadic(q, upper=False):
    scale=1<<BITS
    k=-((-q.numerator*scale)//q.denominator) if upper else (q.numerator*scale)//q.denominator
    return Q(k,scale)

class Clock:
    def __init__(self, cells):
        if cells<1: raise ValueError('A positive clock mesh is required')
        self.cells=cells; self.lower=[Q(0)]; self.upper=[Q(0)]
        scale=1<<BITS; lo=hi=0
        for i in range(cells):
            a,b=Q(i,cells),Q(i+1,cells); l,u=sector_bounds(a,b)
            lo+=(l.numerator*scale)//l.denominator
            hi+=-((-u.numerator*scale)//u.denominator)
            self.lower.append(Q(lo,scale)); self.upper.append(Q(hi,scale))
        self.pi=(4*self.lower[-1],4*self.upper[-1])

    def inverse(self, x):
        x=Q(x)
        if not 0<=x<=Q(1,2): raise ValueError('Use the certified quarter-circle chart')
        if x==0:return Q(0),Q(0)
        if x==Q(1,2):return Q(1),Q(1)
        tl,tu=2*x*self.lower[-1],2*x*self.upper[-1]
        j=max(0,bisect_right(self.upper,tl)-1)
        k=min(self.cells,bisect_left(self.lower,tu))
        a,b=Q(j,self.cells),Q(k,self.cells)
        # On [a,b], geometric polygon comparisons give
        # (v-a)/(1+b²) <= A(v)-A(a) <= (v-a)/(1+a²).
        lo=max(a,a+(tl-self.upper[j])*(1+a*a))
        hi=min(b,a+(tu-self.lower[j])*(1+b*b))
        assert 0<=lo<=hi<=1
        return lo,hi

    def cosine(self,x):
        lo,hi=self.inverse(x);return dyadic(point(hi)[0]),dyadic(point(lo)[0],upper=True)

    def sine(self,x):
        lo,hi=self.inverse(x);return point(lo)[1],point(hi)[1]


def rectangle_bounds(cosine,t,n):
    """The numerical integral side: right lower / left upper rectangles."""
    h=t/n; samples=[cosine(j*h) for j in range(n+1)]
    lower=h*sum((v[0] for v in samples[1:]),Q(0))
    upper=h*sum((v[1] for v in samples[:-1]),Q(0))
    return lower,upper,samples


def endpoint_bounds(clock,t):
    """Separate endpoint side. Does not call the quadrature routine."""
    s0,s1=clock.sine(t);p0,p1=clock.pi
    return s0/p1,s1/p0

@lru_cache(maxsize=None)
def example(n,t=Q(1,3)):
    t=Q(t); clock=Clock(32*n)
    lo,hi,samples=rectangle_bounds(clock.cosine,t,n)
    e0,e1=endpoint_bounds(clock,t)
    assert lo<=hi and e0<=e1 and max(lo,e0)<=min(hi,e1)
    row={'cells':n,'t':str(t),'clockCells':clock.cells,
         'lower':str(lo),'upper':str(hi),'gap':str(hi-lo),
         'endpointLower':str(e0),'endpointUpper':str(e1),
         'piLower':str(clock.pi[0]),'piUpper':str(clock.pi[1]),
         'lowerDisplay':directed(lo),'upperDisplay':directed(hi,upper=True),
         'endpointLowerDisplay':directed(e0),
         'endpointUpperDisplay':directed(e1,upper=True)}
    return row,samples


def table_html(rows):
    body=''.join('<tr><td>'+str(r['cells'])+'</td><td>['+r['lowerDisplay']+', '+r['upperDisplay']+']</td><td>['+r['endpointLowerDisplay']+', '+r['endpointUpperDisplay']+']</td></tr>' for r in rows)
    return '<div class="numeric-scroll"><table class="numerical-bounds"><caption>Independent bounds at t = 1/3. Decimal endpoints are rounded outwards.</caption><thead><tr><th>Cells</th><th>Rectangle bounds for ∫ C</th><th>Independent bounds for S(t)/π</th></tr></thead><tbody>'+body+'</tbody></table></div>'
