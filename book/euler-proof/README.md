# Euler’s sine-product proof of all positive even zeta values

This isolated Mathlib companion proves
$\zeta(2m)=(-1)^{m+1}B_{2m}(2\pi)^{2m}/(2(2m)!)$ for every $m\ge1$.
It also retains the earlier independent Basel coefficient argument with
explicit remainder bounds.
It does **not** import the native interval foundation or change its dependencies.

For finite factors $0\le a_k\le1$, `product_remainder` proves
$0\le\prod(1-a_k)-(1-\sum a_k)\le(\sum a_k)^2/2$.
A telescoping comparison gives $\sum_{k=1}^N k^{-2}\le2$ and hence
$0\le P_N(x)-(1-x^2S_N)\le2x^4$ for $0\le x\le1$.
The bound is uniform in $N$. Taking the product limit and using the cubic sine
approximation yields
$|S-\pi^2/6|\le(2+\pi^4/100)x^2$ for $0<x\le1$ and $\pi x\le1$.
Letting $x$ tend to zero proves `EulerBasel.hasSum_reciprocal_squares`.

The analytic input is Mathlib’s `Real.tendsto_euler_sin_prod`, whose proof uses
weighted cosine integrals and concentration, independently of its
Bernoulli–Fourier evaluation of zeta. General Weierstrass factorization is not
used. The zero set alone is not assumed to imply the sine-product identity.

## General coefficient argument

`EulerSeries.lean` supplies an absolute scalar power-series representation on
the unit disk, its algebra, and coefficient uniqueness.
`EulerCotangent.lean` uses Mathlib's justified logarithmic derivative of the
sine product. The double-series majorant
$|(1+(-1)^r)z^r/k^{r+2}|\le2|z|^r/k^2$ justifies exchanging the sums.
The result identifies the regularized cotangent series, whose coefficient at
$2m$ is $-2\zeta(2m)$.

`EulerEvenZeta.lean` transports the exponential cotangent identity to formal
power series. The purely algebraic Bernoulli generating identity and
cancellation identify every coefficient. The public theorem is
`EulerEven.hasSum_even_zeta`, with the sole hypothesis `0 < m`.
`hasSum_four`, `hasSum_six`, and `hasSum_eight` check concrete specializations.
No previous zeta evaluation or Fourier theorem is used.

## Reproduce

Install the toolchain in `lean-toolchain`, put `lake` on `PATH`, and run from
the repository root:

```sh
python3 book/euler-proof/verify.py --work-dir /tmp/euler-mathlib --report /tmp/euler-reports
```

The script downloads and hash-verifies Mathlib source at
`51e6992efd06126df61a496bebf8f49482a4e129`, fetches its compiled cache, builds
any missing imports, then compiles the proof and executes the dependency audit.
The source archive hash is pinned in `verify.py`; the complete dependency
manifest is supplied by that pinned archive. Existing work directories must
carry the matching revision marker. No global Mathlib installation is needed.

`CheckEuler.lean` traverses elaborated types and proof terms for both the
Basel proof and the general theorem. The latter must use the sine product,
locally uniform logarithmic derivative, double-series summability, coefficient
uniqueness and Bernoulli generating identity. It rejects Fourier dependencies,
pre-existing zeta evaluations, the earlier Basel evaluation, and all axioms
except `propext`, `Classical.choice`, and `Quot.sound`.
The report records theorem statements, axioms, source hashes, and separate
transitive dependency lists. It is a dependency audit, not a proof-size ranking.

## Scope

All positive even Dirichlet-series values are checked in Mathlib's real
numbers. The native project has an independent Basel theorem by finite
Leibniz-square rearrangements. A native Euler route still needs a quantitative
interval sine-product theorem and a bridge to geometric $\pi$; this companion
does not provide that bridge. General Weierstrass factorization is not claimed.
