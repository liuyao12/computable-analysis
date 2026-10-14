# Real differentiability from shrinking secant boxes

The real specialization is `RealSecantDerivative.HasDerivativeAt` in
`ComputableAnalysis/RealSecantDerivative.lean`. The primary function remains
\(f:\mathbb Q\to\texttt{RealRaw}\). The input \(x\) and derivative \(d\)
are arbitrary valid represented real values, including irrational ones.

For distinct rational endpoints, the actual slope computation is
\[
 S_f(a,b)=\frac{f(b)-f(a)}{b-a}.
\]
The quotient scales the two represented endpoint values by an exact nonzero
rational. Each slope is valid when its endpoint values are valid.
`secant_swap_compute` proves that reversing the endpoints gives the same
literal output intervals, so it suffices to cover \(a<b\).

For each admissible input bracket computation \(A\) representing \(x\), the
observations at stage \(n\) contain **every** slope with
\[
 (A_n)_{\mathrm{lo}}\le a<b\le(A_n)_{\mathrm{hi}}.
\]
Both endpoints lie in the whole domain-contained bracket. They may lie on the
same side of \(x\), and their separation may be arbitrarily small.
`RawLimit.HasEnclosureValue` supplies a two-index rational interval family
\(Q_{n,m}\), cofinal maps \(n(k),m(k)\), and a selected diagonal that is a
valid represented value equal to \(d\) and covers all slopes at the selected
input resolution. A single favorable pair or subsequence does not suffice.
The admissible family is explicitly inhabited, preventing a vacuous derivative
claim and preserving relative derivatives at closed-domain endpoints.

## Literally zero-height boxes

The complex-box view of a real interval is
\[
 [L,U]\times\{0\}.
\]
`flatBox_height` proves that its imaginary height is exactly zero.
`flat_compute` identifies each embedded real output interval with this
rectangle. The imaginary coordinate is the exact constant zero computation;
there is no positive imaginary padding.

`hasDerivative_iff_flatBoxes` proves that the real interval condition is exactly
this covered zero-height rectangle condition, using the same two refinement
indices and cofinal schedules. Validity and value equality are transported
through the actual `ComplexRaw.ofRealRaw` computation. Real input pairs remain
on the real axis; no complex open-domain hypothesis is imposed.

## Meaning and compatibility

This is the real two-point, or strict, differentiability condition. It is
stronger at one point than ordinary anchored real differentiability. We do
not assert an unconditional equivalence with the older endpoint-bracket
relation. `HasDerivativeAt.bracket` proves the implication to
`BracketDerivative.HasDerivativeAt`, so checked laws accepting the older
relation remain usable. Those older definitions and theorems are retained.

The shrinking-box derivative is unique. Exact agreement of primary rational
function computations, equivalent input names, and equivalent derivative
names preserve the condition. Domain restriction preserves it once an
admissible bracket family on the smaller domain is justified. Negation
reverses each slope interval and preserves its mathematical derivative role.

## Convex and concave constructions

The existing literal outer-secant computation is unchanged. At stage \(m\),
choose rational points \(l_m<u_m<x<v_m<r_m\) with the middle neighborhood
justified by a stage of the represented input. For a convex function, exact
secant order gives
\[
 S_f(l_m,u_m)\le S_f(a,b)\le S_f(v_m,r_m)
 \qquad(u_m<a<b<v_m).
\]
For a concave function, the inequalities reverse:
\[
 S_f(v_m,r_m)\le S_f(a,b)\le S_f(l_m,u_m).
\]
The actual evaluated outer-secant intervals therefore enclose every inner
slope, including independently refined represented endpoint values.
`outerDerivative_hasDerivative` and `concave_outerDerivative_hasDerivative`
prove the shrinking-box condition from these order laws and validity of the
literal hull computation. They do not assume a derivative identity,
derivative continuity, or a minimum pair separation. Convexity or concavity
supplies containment; the shrinking slope gap remains necessary evidence.

The checked concrete bridges in `RealSecantDerivativeExamples.lean` include:

- the existing convex square outer computation at every valid represented
  input, with restriction to any nondegenerate closed rational interval,
  including both endpoints;
- affine functions with arbitrary valid represented slope coefficients;
- the original convex centered square and represented-coefficient affine
  computations, retaining their exact existing output values;
- an actual concave negative-square outer computation with exact derivative
  value \(d\simeq-(2x)\) at every valid represented input, and a nonlinear instance of the existing `ConcaveDerivative.Pointwise`
  centered computation.

`HasDerivativeOnInterval.toShrinkingSecantDerivative` in
`RealSecantCalculus.lean` proves that existing finite secant estimates also
supply the condition when their radii are positive and their proposed
rational derivative values have the supplied continuous extension. Its
precision may depend on the particular pair; every pair is still covered.
A concrete affine finite certificate instantiates the bridge at arbitrary
represented inputs. Existing independently proved FTC cell laws remain in force.

## Verification

```sh
lake build ComputableAnalysis
lake env lean scripts/check_real_secant_derivative.lean
lake env lean scripts/check_bracket_derivative.lean
lake env lean scripts/check_parametrized_foundation.lean
lake env lean scripts/check_enclosure_holomorphic.lean
lake env .lake/packages/checkdecls/.lake/build/bin/checkdecls blueprint/lean_decls
```

The real audit rejects nonstandard axioms and transitive Mathlib imports.
The full library build checks downstream clients. The source bundle includes
all imported modules and the audit scripts, and has its own build and audit
receipts. Existential selection of schedules is logical existence, not an
executable selector; supplied concrete interval algorithms remain executable.
