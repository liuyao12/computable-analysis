# Function-specific improper power integrals

This is a checked integer-exponent milestone, **not completion of the requested
arbitrary represented-real exponent theorem**. No Mathlib real numbers, custom
axioms, native-decision axioms, or abstract completion are used in the new roots.

## The finite computation comes first

For \(p=k+2\), with \(k\in\mathbb N\), independently specify
\(f_p(x)=1/x^p\). On every rational segment \(0<a\le b\), finite power
factorization proves

\[
(b-a)f_p(b)\le
\frac{a^{1-p}-b^{1-p}}{p-1}
\le(b-a)f_p(a).
\]

Summing these cell inequalities telescopes. Uniform endpoint rectangles have
exact gap \((b-a)(f_p(a)-f_p(b))/N\), so they can be made arbitrarily tight.
`compact_hasIntegral` constructs the rectangle-specification witness;
`compact_exact` identifies **any** supplied witness with the closed form using
`RealRaw.Equiv`. The positive segment hypothesis excludes the pole throughout.

`IntegralRectangleSpecification` ports the checked, sufficient rectangle route
without the unrelated in-progress API migration. It does not make rectangles
the mandatory meaning of all future integrals. Conditional uniqueness is proved;
it is not a field supplied by the caller.

## The improper computation

Take \(R_n=n+1\). The actual computed box is

\[
L_n=\frac{1-R_n^{1-p}}{p-1},\qquad
U_n=\frac1{p-1},\qquad
U_n-L_n=\frac{R_n^{1-p}}{p-1}\le\frac1{n+1}.
\]

Every later rational truncation lies in this box. The boxes nest and their
widths shrink. `infinity_hasIntegralLimit` supplies a certified compact integral
at every stage and convergence against **all** compact-integral witnesses.
`infinity_exact_of_hasIntegralLimit` gives the exact represented-value identity

\[
\int_1^\infty x^{-p}\,dx\simeq\frac1{p-1}
\qquad(p=2,3,4,\ldots).
\]

For \(p=-k\), \(k\in\mathbb N\), a separate monomial cell proof constructs the
compact integrals of \(x^k\). With \(a_n=1/(n+1)\), its truncation value agrees
with the same rational box computation. This proves

\[
\int_0^1 x^k\,dx\simeq\frac1{k+1}.
\]

The cutoff tends to zero and the upper endpoint tends to infinity by checked
exhaustion lemmas. These are chosen exhaustions; agreement with arbitrary
alternative exhaustions is not asserted without comparison evidence.

## Divergence means finite lower bounds

For reciprocal powers \(p=k+2\), the compact integral from \(1/(n+1)\) to one
is at least \(n/(k+1)\). For monomials \(x^k\), the integral from one to
\(n+1\) is at least \(n\). Explicit schedules therefore rule out every finite
represented exhaustion limit on the divergent sides.

At \(p=1\), use the actual geometric cells
\([a2^j,a2^{j+1}]\). Each lower rectangle has area \(1/2\), and each upper
rectangle has area one, at every positive rational scale \(a\). Thus the sums
are \(N/2\) and \(N\). Scaling gives divergence at zero as well as infinity.
These lower-area proofs do not require constructing a compact logarithm
algorithm; no such new construction is claimed here.

## The series follows from the integrals

Writing \(S_N=\sum_{j=1}^N j^{-p}\), summing the same compact cell theorem gives

\[
\int_{N+1}^{M+1}x^{-p}\,dx
\le S_M-S_N\le\int_N^M x^{-p}\,dx.
\]

The series computation returns

\[
\left[S_N,\;S_N+\frac{N^{1-p}}{p-1}\right],\qquad N=n+1.
\]

Its validity, convergence of the independently defined partial sums, uniqueness,
and invariance under replacing the represented sum are proved. At the boundary,
\(S_{2^{2T}}\ge T\); at \(p=0\), \(S_N=N\).
`natural_series_converges_iff` proves

\[
\bigl(\exists I\text{ represented},\ S_N\longrightarrow I\bigr)
\quad\Longleftrightarrow\quad p\ge2,
\qquad p\in\mathbb N.
\]

This module's series has not yet been identified with the separate `ZetaReal`
implementation. Its power terms are proved literally equal to reciprocal
natural powers.

## Still required for the full request

Construct positive-base powers for arbitrary valid represented-real exponents,
prove their compact integration law and representation invariance, and extend
these estimates to the full thresholds \(p<1\), \(p=1\), and \(p>1\).
In particular the noninteger range \(0<p<1\) is **not covered** here. The earlier
binomial `ZetaReal` evaluator does not substitute for that integration bridge.
Gaussian normalization, the Gamma integral, and geometric ball-volume
identification remain separate open bridges.

## Verification

```sh
lake build ComputableAnalysis
lake env lean scripts/check_power_improper.lean
python3 scripts/audit_construction_first.py
python3 scripts/audit_integral_enclosures.py
python3 blueprint/checks/check_foundation_imports.py
```

The audit prints dependencies for 28 theorem roots and runs 34 executable
regression groups. Only Lean's standard logical axioms occur in these roots.
Runtime checks supplement the proofs; they do not prove the formulas.
