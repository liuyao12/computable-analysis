# Function theory audit and the zeta/Gamma programme

This audit distinguishes computations, analytic witnesses, and exact identification.
A supplied record containing a desired conclusion is not a proof of that conclusion.
All checked results below use the repository's rational interval foundation.

## Current foundation

`FunctionTheory.HolomorphicOn` is the primary contract: an open domain and a
continuous divided difference at each valid represented point. It does **not**
require continuity of the derivative across points. `HolomorphicFoundation`
constructs continuity of the function, sums, products, composition on the
inverse-image domain, and exact derivative uniqueness. Every polynomial with
arbitrary represented coefficients supplies this contract.

The older `Holomorphic` record includes separate derivative-continuity data.
Existing continuation and differential-equation clients keep using that stronger
interface. `HolomorphicOn.toLegacy` accepts the extra evidence explicitly. There
is no automatic promotion of every legacy remainder witness into a computed
quotient, nor a theorem that bare derivative values already certify continuity.

| Component | Checked scope | Remaining bridge |
| --- | --- | --- |
| Continuity and derivatives | Exact arithmetic/order laws; quotient continuity; real and complex polynomial calculus | Quotient construction from an arbitrary old remainder witness |
| Holomorphicity | Open-domain quotient derivatives; algebra and composition; arbitrary represented polynomial inputs and coefficients | Reciprocal and general represented complex-series constructors |
| Contours and Taylor series | Quantitative polygonal cancellation; supplied Cauchy data; rational-input Taylor comparison | Function-specific contour identities and full represented-input reconstruction; a general Cauchy constructor is optional |
| Continuation and ODEs | Supplied local germs and overlap laws; affine identity theorem; finite transport; polynomial residuals | General identity theorem and path-to-chart subdivision; analytic Frobenius factors |
| Argument principle | No general zero-count theorem yet | Constructive isolated zeros, multiplicities, contour identity, and equality with actual zero counts |

No imported completed real or complex number system closes these gaps.
General Cauchy–Goursat is not a required bridge for these applications. Skills
select concrete series estimates, factorization, local logarithms, finite
cancellation, or justified deformations; the selected proof must establish
the actual requested identity or count. General-purpose constructors remain
optional directions rather than prerequisites.

The reader's [zeta-zero exposition](../book/classics/zeta-zeros.html) explains
how rigorous approximate evaluations can prove an exact integer count, and how
reflection plus unique isolation forces a zero exactly onto the critical line.
It also separates critical-line sign certificates from uniqueness and global
completeness. It does not add a certificate for an actual zeta zero.

## First exact zeta results

`ZetaReal.zeta` already computes valid represented **real** values for every
valid represented argument \(s>1\), with explicit chart and series error bounds.
The checked Dirichlet convergence bridge currently uses rational parameters.
Compatibility with the integer Dirichlet computation is exact.

`ZetaIntegerBounds` now proves, for every integer \(p\ge2\),
\[
 1+2^{-p}\le\zeta(p)\le2,\qquad \zeta(p)\ne0,
 \qquad p\le q\Longrightarrow\zeta(q)\le\zeta(p).
\]
These are `RealRaw.Le` and `RealRaw.Equiv` statements about the infinite
computations, not inequalities on an arbitrarily truncated sum. The bounds
transfer to any equivalent valid computation, including the public real-zeta
evaluator at integer arguments. No complex continuation or critical-strip
nonvanishing is asserted.

For the next complex construction, start with the Dirichlet series on
\(\Re s>1\), construct its complex derivative and local uniform tails, then
justify a particular continuation across the strip. Gamma factors, powers,
branch conventions, and the completed function's symmetry each need their own
proof. A functional equation without a constructed overlapping function does
not supply those obligations.

## First actual Gamma limit

`GammaInteger` constructs positive-integer values using Gauss's finite products:
\[
 G_{m,n}=\frac{n!\,n^{m+1}}{(m+1)(m+2)\cdots(m+n+1)}
 =m!\prod_{j=1}^{m+1}\frac{n}{n+j},\qquad m,n\ge0.
\]
The right-hand product is the executable evaluator. Its shorter length follows
from a proved cancellation identity. For every stage,
\[
 G_{m,n}\le m!\le G_{m,n}+\frac{m!(m+1)^2}{n+1}.
\]
Finite intersections of these enclosures give valid nested intervals;
an explicit rational tolerance schedule proves convergence and the exact
identity \(\Gamma(m+1)\simeq m!\) for this Gauss-limit construction.
The factorial is a proof anchor for the shrinking intervals, not a replacement
of the Gauss sequence by a constant output interval.

This is a positive-integer result. It does not construct Gamma at arbitrary
real or complex parameters, identify it with Euler's improper integral, or
prove the reflection formula. Those remain separate tasks. The existing
half-integer coefficients in the ball-volume chapter are still coefficients,
not an Euler-integral Gamma construction. Gauss's general classical formula
is recorded in [NIST DLMF](https://dlmf.nist.gov/5.8.E1).

## Exact zeros on the critical line

The proposed proof has two parts: count every zero, then prove exact location.
For the completed zeta function, reflection preserves the ordinate:
\[
 R(\rho)=1-\overline\rho.
\]
If an isolating region is stable under this reflection, contains a zero, and
contains no inequivalent second zero, the completed function's symmetry makes
\(R(\rho)\) another zero in the same region. Uniqueness forces
\(\rho\simeq R(\rho)\), hence \(\Re\rho\simeq1/2\).

`ZeroIsolation.unique_zero_on_line` proves this implication for arbitrary
valid represented roots and supplied function/region evidence. It assumes
neither the critical-line conclusion nor an argument-principle identity. It
**does not prove that a particular zeta isolating region exists**.

A complete finite-height theorem must construct the complex function and its
symmetry, certify nonvanishing on entire contour segments, prove the argument-principle count for the selected function and region,
isolate each root, and equate the sum of local counts with the global
count. Boundary heights and multiplicities must be explicit. A floating-point
list of roots cannot establish completeness or exact equality. Rigorous interval
computation with proved analytic bounds can be part of a proof: the work of
[Platt and Trudgian](https://arxiv.org/abs/2004.09765) combines certified critical-line
root information with a completeness argument using Turing's method. Our proposed
skill uses the argument principle instead; neither method is presently implemented
for complex zeta here.

Read the [certified zero-counting guide](../skills/analytic-continuation/references/certified-zero-counting.md)
for the construction obligations. No finite-height Riemann-hypothesis theorem is
claimed by this audit.

## Zero-certificate benchmark

The [reader benchmark](../book/classics/zeta-zeros.html#benchmark) targets
complete certificates for the first and second positive-height nontrivial
zeros. Ordinal claims require a justified global count excluding omitted
lower zeros; line-root existence alone does not establish their rank.
Both targets remain unimplemented, with no code-size or timing score.

Run `.github/reader-edition/zeta_zero_benchmark.py` to inventory the current
shared conditional reflection module and its project-local import closure.
The reader generates the same report at its source revision. It counts
nonblank physical Lean lines after stripping nested comments, retaining
imports and namespace commands, and records source hashes. The closure
includes every declaration in imported project files, not a minimized
elaborated proof dependency slice. External library sources are listed but
not counted. This inventory is not a replacement for the Lean axiom audit.

Report the full shared certification setup separately; its size is still pending.
The existing conditional module is only a measured component, not the full setup.
Compare only additional proof code for each zero, excluding shared machinery
for every ordinal, including the first. Zero-specific parameters, proof
applications and ordinal-completeness evidence belong to that zero's score.
Move reusable lemmas into the shared baseline and recompute all rows against
the same baseline. Keep uncompressed rational certificate bytes and kernel-check
time separate, with machine and toolchain metadata.
The actual constructed zeta and root theorems, convergence/contour evidence,
ordinal completeness and axiom audits must pass before a row is scored.

## Validation

Build `ComputableAnalysis`, then run
`lake env lean scripts/check_holomorphic.lean` and
`lake env lean scripts/check_zeta_gamma.lean`.
The latter checks actual finite Gauss products and error enclosures, the integer
zeta comparison theorems, and the exact reflected-root argument. Both audits
reject Mathlib imports, `sorryAx`, and unapproved proof axioms. Existing inherited
native-decision facts from `Basic` remain explicitly allowlisted. Four finite
native-decision facts in the audited zeta dependency chain have been replaced by
kernel-checked proofs. No new axiom is
introduced. The continuation audit and blueprint declaration check remain required.
