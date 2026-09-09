#!/usr/bin/env python3
"""Exact finite checks for the new blueprint chapters; no third-party dependencies.

These regression checks exercise formulas used by the manuscript. They are not
substitutes for its uniform bounds or proofs about all orders and inputs.
Run: python blueprint/checks/check_special_function_identities.py
"""
from fractions import Fraction as F
from math import comb, factorial
import json


def trim(p):
    p = list(p)
    while len(p) > 1 and not p[-1]:
        p.pop()
    return p or [F(0)]


def add(p, q):
    return trim([(p[i] if i < len(p) else 0) +
                 (q[i] if i < len(q) else 0) for i in range(max(len(p),len(q)))])


def scale(p, a):
    return trim([a*x for x in p])


def mul(p, q):
    r = [F(0)] * (len(p)+len(q)-1)
    for i,x in enumerate(p):
        for j,y in enumerate(q):
            r[i+j] += x*y
    return trim(r)


def deriv(p, k=1):
    for _ in range(k):
        p = [F(i)*p[i] for i in range(1,len(p))] or [F(0)]
    return trim(p)


def val(p, x):
    r = F(0)
    for a in reversed(p):
        r = r*x+a
    return r


def shift(p, c):
    return trim([sum((F(comb(n,k))*p[n]*c**(n-k) for n in range(k,len(p))),F(0))
                 for k in range(len(p))])


def integrate(p, a, b):
    return sum((x*F(b**(k+1)-a**(k+1),k+1) for k,x in enumerate(p)),F(0))


def bernoulli_polynomials(n):
    result = [[F(1)]]
    for k in range(1,n+1):
        p = [F(0)] + [F(k)*a/F(j+1) for j,a in enumerate(result[-1])]
        p[0] = -integrate(p,F(0),F(1))
        result.append(trim(p))
    return result


def j0_box(x, n):
    """Alternating enclosure after n>=1 terms beyond the constant, for |x|<=3."""
    assert abs(x) <= 3 and n >= 1
    term = F(1)
    total = term
    z = x*x/4
    for k in range(1,n+1):
        term *= -z/F(k*k)
        total += term
    next_term = -term*z/F((n+1)**2)
    return min(total,total+next_term), max(total,total+next_term)


def first_bessel_zero(bits=30):
    lo,hi = F(2),F(3)
    while hi-lo > F(1,2**bits):
        u,v = (2*lo+hi)/3,(lo+2*hi)/3
        for n in range(2,256):
            lu,_ = j0_box(u,n)
            _,hv = j0_box(v,n)
            if lu > 0:
                lo = u
                break
            if hv < 0:
                hi = v
                break
        else:
            raise AssertionError('Precision search did not terminate in this check')
    return lo,hi


def main():
    counts = {}
    cases = 0
    for n in range(1,13):
        p = [F((-1)**j,j+1) for j in range(n+1)]
        for c in [F(-2,3),F(0),F(1,3)]:
            for w in [F(-1,5),F(2,7)]:
                assert val(shift(p,c),w)==val(p,c+w)
                cases += 1
    for k in range(9):
        # The infinite majorant bounds every tested finite recentering sum.
        lhs=sum((3*F(comb(n,k))*F(1,3)**(n-k)*F(1,2)**n
                 for n in range(k,80)),F(0))
        assert lhs <= F(6)/F(2-F(1,3))**(k+1)
        cases += 1
    counts['recentring_and_majorants'] = cases

    cases=0
    for m in range(6):
        coef=[F((-1)**k,2**(2*k+m)*factorial(k)*factorial(k+m)) for k in range(21)]
        for k in range(1,len(coef)):
            assert 4*k*(k+m)*coef[k]+coef[k-1] == 0
            cases+=1
    p=[F(1),-F(1,8),F(1,192),-F(1,9216)]
    assert val(p,F(9))==F(223,1024)
    assert sum(F((-1)**k, factorial(k)**2) for k in range(4))==F(2,9)
    assert sum((-F(9,4))**k/F(factorial(k)**2) for k in range(5))==-F(4199,16384)
    lo,hi=first_bessel_zero()
    assert j0_box(lo,20)[0]>0 and j0_box(hi,20)[1]<0
    counts['bessel_coefficients_signs_and_root'] = cases+4

    cases=0
    for a,b,c in [(F(1,2),F(1,2),F(1)),(F(-3),F(2,3),F(5,4)),
                  (F(3,2),F(-2,3),F(-1,2)),(F(2),F(3),F(4))]:
        h=[F(1)]
        for n in range(20):
            h.append(h[-1]*(n+a)*(n+b)/((n+1)*(n+c)))
        p=h
        res=add(add(mul([F(0),F(1),F(-1)],deriv(p,2)),
                    mul([c,-(a+b+1)],deriv(p))),scale(p,-a*b))
        assert all(x==0 for x in res[:20])
        cases+=20
        if a == -3:
            assert all(x==0 for x in h[4:])
    counts['hypergeometric_equations']=cases

    polys=bernoulli_polynomials(10)
    assert polys[2]==[F(1,6),F(-1),F(1)]
    assert polys[4]==[-F(1,30),F(0),F(1),F(-2),F(1)]
    cases=0
    for p in range(1,5):
        for d in range(15):
            f=[F(0)]*d+[F(1)]
            N,M=2,7
            lhs=sum((val(f,F(n)) for n in range(N,M)),F(0))
            rhs=integrate(f,F(N),F(M))+(val(f,F(N))-val(f,F(M)))/2
            for k in range(1,p+1):
                g=deriv(f,2*k-1)
                rhs+=polys[2*k][0]/factorial(2*k)*(val(g,F(M))-val(g,F(N)))
            g=deriv(f,2*p)
            remainder=sum((integrate(mul(polys[2*p],shift(g,F(n))),F(0),F(1))
                           for n in range(N,M)),F(0))
            rhs-=remainder/factorial(2*p)
            assert lhs==rhs,(p,d,lhs,rhs)
            cases+=1
    counts['exact_euler_maclaurin_identities']=cases

    for s,p,expected in [(0,1,-F(1,2)),(-1,2,-F(1,12)),(-2,2,F(0))]:
        N=5
        rising=lambda k: __import__('functools').reduce(lambda a,j:a*(s+j),range(k),F(1))
        assert rising(2*p)==0 and s+2*p>1
        z=sum((F(n)**(-s) for n in range(1,N)),F(0))+F(N)**(1-s)/(s-1)+F(N)**(-s)/2
        z+=sum((polys[2*k][0]/factorial(2*k)*rising(2*k-1)*F(N)**(-s-2*k+1)
                for k in range(1,p+1)),F(0))
        assert z==expected
    counts['zeta_special_values']=3

    # Flat-function derivative recurrence and erfc coefficients are finite identities.
    P=[F(1)]
    for n in range(8):
        Q=add(mul([F(0),F(0),F(0),F(2)],P),scale(mul([F(0),F(0),F(1)],deriv(P)),-1))
        assert len(Q)-1==3*(n+1)
        P=Q
    a=F(1)
    for k in range(1,10):
        a *= -F(2*k-1,2)
        assert a==F((-1)**k*factorial(2*k),4**k*factorial(k))
    counts['flat_derivative_and_asymptotic_coefficients']=17

    print(json.dumps({'checks':counts,'total_finite_checks':sum(counts.values()),
       'bessel_zero_enclosure':{'lower':str(lo),'upper':str(hi),
       'lower_decimal':float(lo),'upper_decimal':float(hi),'width_at_most':'2^-30'},
       'note':'Finite exact regression checks; the manuscript supplies the general proofs.'},indent=2))

if __name__=='__main__':
    main()
