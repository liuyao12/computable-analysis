# Euler’s sine-product proof of Basel

This isolated Mathlib companion proves
$\sum_{k=1}^{\infty} k^{-2}=\pi^2/6$ by Euler’s sine-product route.
It supplies the missing coefficient argument with explicit remainder bounds.
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

`CheckEuler.lean` traverses elaborated types and proof terms. It requires the
finite-product, sine-product, and coefficient-error theorems in the final
proof; it rejects pre-existing zeta evaluations, the native Basel proof, and
all axioms except `propext`, `Classical.choice`, and `Quot.sound`.
The report records theorem statements, axioms, source hashes, and the full
transitive dependency list. It is a dependency audit, not a proof-size ranking.

## Scope

The checked result is the Basel case in Mathlib’s real numbers. The native
project already has an independent Basel theorem by finite Leibniz-square
rearrangements. A native Euler route still needs a quantitative interval
sine-product theorem and a bridge to geometric $\pi$; this companion does not
provide that bridge. Higher coefficients, all $\zeta(2m)$, and a general
Weierstrass factorization theorem are not claimed here.
