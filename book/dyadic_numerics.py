"""Pi from rational polygons; cosine samples from nested square roots.

Only illustration coordinates use floats. Certified endpoints use exact
Fractions, integer square roots and outward rounding. This driver is not
claimed to be extracted Lean code or the literal Lean stage schedule.
"""
from fractions import Fraction as Q
from math import isqrt
from functools import lru_cache
from numerical_examples import sector_bounds, directed

PRECISION = 72

def sqrt_box(lo: Q, hi: Q, bits: int = PRECISION):
    if not 0 <= lo <= hi:
        raise ValueError('An ordered nonnegative interval is required')
    scale = 1 << bits
    a = isqrt((lo.numerator * scale * scale) // lo.denominator)
    b = isqrt((hi.numerator * scale * scale) // hi.denominator)
    if b*b*hi.denominator < hi.numerator * scale * scale:
        b += 1
    out = Q(a, scale), Q(b, scale)
    assert out[0]**2 <= lo and hi <= out[1]**2
    return out

@lru_cache(maxsize=20)
def radical_grid(depth: int, bits: int = PRECISION):
    """C(j/(2*2^depth)), 0<=j<=2^depth. No pi or arctangent input.

Even positions reuse the previous grid. Odd positions apply positive
half-angle roots; reflection supplies the second half of the quadrant.
"""
    if depth < 0 or bits < 4:
        raise ValueError('Nonnegative depth and at least four root bits required')
    if depth == 0:
        return ((Q(1),Q(1)), (Q(0),Q(0)))
    previous=radical_grid(depth-1,bits); n=len(previous)-1
    values=[]
    for k in range(2*n+1):
        if k%2==0:
            values.append(previous[k//2]);continue
        if k<=n:
            lo,hi=previous[k]
            rad_lo,rad_hi=(1+lo)/2,(1+hi)/2
        else:
            lo,hi=previous[2*n-k]
            rad_lo,rad_hi=(1-hi)/2,(1-lo)/2
        a,b=sqrt_box(max(Q(0),rad_lo),min(Q(1),rad_hi),bits)
        values.append((max(Q(0),a),min(Q(1),b)))
    return tuple(values)

@lru_cache(maxsize=20)
def geometric_pi(cells: int, bits: int = PRECISION):
    """Four times the polygon enclosure for A(1); no trigonometry."""
    if cells<1:raise ValueError('Positive subdivision required')
    scale=1<<bits; lower=upper=0
    for j in range(cells):
        lo,hi=sector_bounds(Q(j,cells),Q(j+1,cells))
        lower+=(lo.numerator*scale)//lo.denominator
        upper+=-((-hi.numerator*scale)//hi.denominator)
    return 4*Q(lower,scale),4*Q(upper,scale)

def integral_box(depth: int, bits: int = PRECISION):
    c=radical_grid(depth,bits);n=1<<depth;h=Q(1,2*n)
    return h*sum((p[0] for p in c[1:]),Q(0)), h*sum((p[1] for p in c[:-1]),Q(0))

def product_row(depth: int):
    n=1<<depth
    lo,hi=integral_box(depth);pl,pu=geometric_pi(n)
    lower,upper=pl*lo,pu*hi
    def pair(a,b):return [str(a),str(b)]
    return {'depth':depth,'cells':n,'integral':pair(lo,hi),'pi':pair(pl,pu),
        'product':pair(lower,upper),
        'integralDisplay':[directed(lo,9),directed(hi,9,upper=True)],
        'piDisplay':[directed(pl,9),directed(pu,9,upper=True)],
        'productDisplay':[directed(lower,9),directed(upper,9,upper=True)]}

def table_html(rows):
    def interval(s):return '['+', '.join(s)+']'
    body=''.join('<tr><td>'+str(r['cells'])+'</td><td>'+interval(r['piDisplay'])+
       '</td><td>'+interval(r['integralDisplay'])+'</td><td>'+interval(r['productDisplay'])+'</td></tr>' for r in rows)
    return '<div class="numeric-scroll"><table class="numerical-bounds"><caption>Independent polygon and radical-rectangle bounds; outward-rounded decimals.</caption><thead><tr><th>Cells</th><th>Geometric π</th><th>Radical cosine integral</th><th>Product</th></tr></thead><tbody>'+body+'</tbody></table></div>'

if __name__=='__main__':
    for d in [3,5,7,9,11,13]:
        print(product_row(d))
