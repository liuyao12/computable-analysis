# Examples to highlight

The identity-theorem example is now \(\sin(1/z)\), with zeros accumulating
at an excluded boundary point. For continuation, the presentation order is
arctangent, logarithm, then square root. The first
explains why continuation matters even for real-variable functions; the next
two distinguish additive and finite branch changes. Bessel's equation is a
later differential-equation application. These are proposed continuation
theorems, not claims that the full constructions are already checked. The source links below identify
the published baseline at this revision; inspect the working checkout for
subsequent proofs before reporting current coverage.

## Arctangent: one Taylor series is not the whole function

Start with the germ \(A(0)=0\), \(A'(z)=1/(1+z^2)\). Highlight moving from
the origin along the real axis to \(2\): the original Taylor series fails
there, while overlapping local functions can continue the same branch.
The expansion centered at \(1\) has classical radius \(\sqrt{2}\), determined
by the branch points \(\pm i\). This radius claim still needs its analytic
bridges in our development; do not infer it from a formal recurrence alone.

Use the rational function \(1/(1+z^2)\) as a short comparison: its poles
are genuine singularities, but its value has no branch change on returning
along a loop. For arctangent, the derivative is single-valued but the function
can change. The normalized logarithmic relation to prove is
\[
 A(z)=\frac{L_+(z)-L_-(z)}{2i},
 \qquad L_\pm(z)=\operatorname{Log}(1\pm iz),\quad L_\pm(0)=0,
\]
where both logarithms are continued from those initial germs. An equivalent
principal-branch formula is recorded in [DLMF 4.23.26](https://dlmf.nist.gov/4.23.E26).
Tracking the two logarithms predicts a change of \(\pi\) after a positive
loop about \(i\) alone, and \(-\pi\) after a positive loop about \(-i\)
alone. These signs follow from the displayed relation and must be established
for the chosen loop in Lean. Do not identify branch points of arctangent with
poles of arctangent itself.

**Existing pieces:** [ArctanTaylorConvergence](https://github.com/liuyao12/computable-analysis/blob/5a8fab9ebdd68f0bf72913cf9c74683dc84038bc/ComputableAnalysis/ArctanTaylorConvergence.lean)
proves the real Taylor convergence classification at rational inputs and
identifies the limit inside that domain. [CauchyTaylorDisk](https://github.com/liuyao12/computable-analysis/blob/5a8fab9ebdd68f0bf72913cf9c74683dc84038bc/ComputableAnalysis/CauchyTaylorDisk.lean)
is conditional reconstruction at rational complex inputs, not a general
Taylor theorem from holomorphicity. See [the arctangent ledger](https://github.com/liuyao12/computable-analysis/blob/5a8fab9ebdd68f0bf72913cf9c74683dc84038bc/docs/ARCTAN_TAYLOR.md).
The represented-input local charts, their overlap identities, the exact
centered radius, and the loop branch changes remain construction tasks.

## Logarithm: the period computed by arctangent

Start with \(L(1)=0\), \(L'(z)=1/z\). A first route is the vertical segment
from \(1\) to \(1+i\), with target
\[
 L(1+i)=\frac12\log 2+\frac{\pi i}{4}.
\]
Then continue once counterclockwise around a specified square enclosing
\(0\), with a route from and back to the initial neighborhood if needed.
The target terminal germ is \(L+2\pi i\), not the original principal branch.
This connects local continuation to our rational-box reciprocal computation
and arctangent normalization. [DLMF 4.2](https://dlmf.nist.gov/4.2#i) gives
the classical branches and logarithm normalization.

**Existing pieces:** [VerticalReciprocalIntegral](https://github.com/liuyao12/computable-analysis/blob/5a8fab9ebdd68f0bf72913cf9c74683dc84038bc/ComputableAnalysis/VerticalReciprocalIntegral.lean)
constructs valid whole-chunk enclosures on the specified vertical segment;
[SquarePole](https://github.com/liuyao12/computable-analysis/blob/5a8fab9ebdd68f0bf72913cf9c74683dc84038bc/ComputableAnalysis/ComplexAnalysis/SquarePole.lean)
proves the sampled square-pole period. These computations do not alone
provide a chain of logarithm germs. The local logarithm series and jet files
need their adapters to `FunctionTheory.Holomorphic`, overlap proofs, and
connections to the chosen edge-integral construction before we claim the
continuation theorem. Do not turn a theorem about an integral into a theorem
about a branch without that identification.

## Square root: the algebraic branch that returns with the opposite sign

Start near \(1\) with \(S(1)=1\), \(S(z)^2=z\). Continue around the origin
on a specified rational square route: the target after one positive loop is
\(-S\), and after two loops it is \(S\). Follow separated roots on overlapping
neighborhoods. Prove their local holomorphicity and root uniqueness in the
chosen enclosures, then use uniqueness to establish overlap equality.

Do not assume the sheet switch from the name of a branch or from a picture.
It is the terminal comparison to prove. The classical relation
\(S=\exp(L/2)\) also predicts the sign change from the logarithm period;
using it requires constructing those functions and proving their relation.
See [DLMF 4.2, powers](https://dlmf.nist.gov/4.2#iv).

**Existing pieces:** [HolomorphicExamples](https://github.com/liuyao12/computable-analysis/blob/5a8fab9ebdd68f0bf72913cf9c74683dc84038bc/ComputableAnalysis/HolomorphicExamples.lean)
proves that squaring is holomorphic. This is not yet a holomorphic local
inverse theorem or a square-root continuation theorem. Do not import an
unpublished draft as though it were part of the checked public foundation.

## Later: Bessel's equation and a changing basis of solutions

Use the existing motivating equation
\[
 z^2y''+zy'+z^2y=0.
\]
The regular solution \(J_0\) returns to itself. A logarithmic companion
normalized as \(Y_*=J_0\operatorname{Log}z+H(z)\), with \(H\) entire,
returns as \(Y_*+2\pi iJ_0\). Thus continuation acts on a pair of solutions.
This is a direct bridge to the Fuchs presentation; it need not wait for a
classification theorem. The normalization is not the standard \(Y_0\);
compare [DLMF 10.8.2](https://dlmf.nist.gov/10.8.E2).

**Existing scope:** the reader's Bessel continuation is a floating-point
illustration. The complex solution branches, overlap comparisons, and basis
change have not been certified by the currently published Lean modules.
Keep it a later showcase, after the elementary functions above.

## Adjacent checks, not continuation proofs

After building their matching modules, the existing audit commands are:

- `lake env lean scripts/check_holomorphic.lean`
- `lake env lean scripts/check_arctan_taylor.lean`
- `lake env lean scripts/check_cauchy_taylor.lean`
- `lake env lean scripts/check_polygonal_cauchy.lean`
- `lake env lean scripts/check_integral_enclosures.lean`

A new continuation example needs its own proof audit covering the local
holomorphicity, overlap, coverage, and terminal comparison theorems. Passing
these adjacent checks does not supply that missing theorem.

## Accumulation and natural boundaries

Use \(\sin(1/z)\) primarily to explain why the accumulation point in the
identity theorem must belong to the holomorphic domain. Its zeros
\(z_n=1/(n\pi)\) approach the excluded origin. The function is not
identically zero. Its trivial monodromy and essential singularity are a
secondary comparison, not the main reason for the example.

The lacunary series \(\sum_{k\ge0}z^{2^k}\) illustrates an entire natural
boundary. Prove radial unboundedness at dyadic roots of unity, then use their
density; mere divergence of the defining series on the boundary does not
suffice. Neither example yet has its full Lean proof in this foundation.
See [the method guide](methods.md) for the quantitative obligations and
Gamma recurrence and Schwarz-reflection examples.
