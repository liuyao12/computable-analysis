# Computing first: geometric arctangent and pi

The definition is a rational computation: start with an interval, then raise
its lower endpoint and lower its upper endpoint by successive small amounts.
The proof explains those amounts as signed triangle areas. Neither the
computation nor its validity requires evaluating a pre-existing angle function.

## The computation

For a rational input $0\leq x\leq1$, start with

$$
[a,b]=\left[\frac{x}{1+x^2},x\right].
$$

Keep a list of parameter intervals, initially just $[0,x]$. At each stage,
split every current interval at its midpoint. For $p\leq q\leq r$, put

$$
I(p,q,r)=
\frac{2(r-p)(q-p)(r-q)}{(1+p^2)(1+q^2)(1+r^2)},
\qquad
D(p,q,r)=
\frac{(r-p)(q-p)(r-q)}{(1+pr)(1+pq)(1+qr)}.
$$

Here is the definition in Python-style pseudocode. Arithmetic is exact
rational arithmetic throughout; in an executable Python translation, the
inputs and initial endpoints use `Fraction` so that division stays rational.
The input `n` is the stage number.

```python
def arctan_bounds(x, n):
    a, b = x / (1 + x*x), x
    cells = [(0, x)]

    for _ in range(n):
        next_cells = []
        for p, r in cells:
            q = (p + r) / 2
            increment = (2*(r-p)*(q-p)*(r-q)
                         / ((1+p*p)*(1+q*q)*(1+r*r)))
            decrement = ((r-p)*(q-p)*(r-q)
                         / ((1+p*r)*(1+p*q)*(1+q*r)))
            a += increment
            b -= decrement
            next_cells.extend([(p, q), (q, r)])
        cells = next_cells

    return [a, b]


def pi_bounds(n):
    a, b = arctan_bounds(1, n)
    return [4*a, 4*b]
```

For $\pi$, stage zero returns $[2,4]$; stage one returns
$[14/5,10/3]$. The arctangent and pi implementations in Lean keep their own
states; the shared pseudocode displays their common recurrence. Agreement
of the implementations is a separate checked statement, rather than an
assumption built into either definition. At zero the arctangent returns
$[0,0]$; negative inputs can use $[-b,-a]$ from the positive computation.
The exposition and validity claims here concern the branch $[-1,1]$.

## Why the intervals are valid

The proof may introduce the following two rational cell quantities:

$$
L(p,r)=\frac{(r-p)(1+pr)}{(1+p^2)(1+r^2)},
\qquad U(p,r)=\frac{r-p}{1+pr}.
$$

Direct rational algebra gives

$$
L(p,q)+L(q,r)=L(p,r)+I(p,q,r),
$$
$$
U(p,q)+U(q,r)=U(p,r)-D(p,q,r).
$$

Thus the updated endpoints equal the sums of the current lower and upper
cell quantities. The increments and decrements are nonnegative. Moreover,

$$
U(p,r)-L(p,r)=
\frac{(r-p)^3}{(1+pr)(1+p^2)(1+r^2)}\geq0.
$$

After stage $n$ there are $2^n$ equal cells, each of width $x/2^n$.
All denominator factors are at least one, so

$$
0\leq b_n-a_n\leq \frac{x^3}{4^n}.
$$

The intervals remain nested, and their widths shrink to zero. The pi
intervals consequently have width at most $4/4^n$. This is a validity
argument for the computation; the geometric interpretation supplies its name.

## Why this computes the advertised object

Only in the proof do we introduce the rational circle points

$$
P(t)=\left(\frac{1-t^2}{1+t^2},\frac{2t}{1+t^2}\right),
\qquad O=(0,0).
$$

Use signed triangle area throughout:

$$
A(P,Q,R)=\frac12\det(Q-P,R-P).
$$

With the vertices in the displayed counterclockwise order, the relevant
areas are nonnegative. The lower cell quantity is exactly
$L(p,r)=A(O,P(p),P(r))$. Inserting $P(q)$ adds the signed triangle
$A(P(p),P(q),P(r))=I(p,q,r)$.

For $p<r$, the two rational lines $P(p)\mathbin{\cdot}X=1$ and
$P(r)\mathbin{\cdot}X=1$ meet at the rational point

$$
T(p,r)=\left(\frac{1-pr}{1+pr},\frac{p+r}{1+pr}\right).
$$

The upper cell quantity is the sum
$A(O,P(p),T(p,r))+A(O,T(p,r),P(r))$. On inserting the midpoint, the
removed triangle has signed area
$A(T(p,q),T(p,r),T(q,r))=D(p,q,r)$. The zero-width cell needs no line
intersection and contributes zero.

These inner chord fans and outer tangent fans enclose the directed unit
sector. Their vanishing area gap supplies its area by rational exhaustion.
At $x=1$ the endpoints are $(1,0)$ and $(0,1)$, so four such quarter-disk
areas give the unit-disk area, $\pi$. For general $x$, twice the sector area
is the radian angle of $P(x)$; its half-angle slope is $x$. This identifies
the computed sector area with $\arctan x$, with the normalization made explicit.
No trigonometric addition law or derivative is part of the definition.

The finite signed-area interpretation uses rational determinants and dot
products. It does not require introducing the broader geometric axioms
that have been deferred. Agreement with a separately axiomatized area or
angle theory would require its own comparison theorem.

## Source and proof scope

The existing constructors are `piCircleAreaState` and `piCircleAreaCompute`
in `ComputableAnalysis/Pi.lean`, and `arctanAreaLoopState`,
`positiveLoopComputeAtStage`, and `arctanGeom` in
`ComputableAnalysis/ArctanGeometry.lean`. The latter module proves
`geometricLowerStep_refine`, `geometricUpperStep_refine`,
`arctanAreaLoopState_lo_eq_geometricLowerSum`, and
`arctanAreaLoopState_hi_eq_geometricUpperSum`. Its validity and pi comparison
are checked in the [published inverse-circle proof snapshot](../book/trigonometry-audit/proof/README.md).

This note changes the exposition, not those algorithms. The displayed
triangle interpretation and cubic gap estimate are explained above; this
note does not claim a new Lean theorem for every displayed identity. The
snapshot's recorded checks retain their original scope.
