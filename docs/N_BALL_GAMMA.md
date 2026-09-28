# Ball volume, Gaussian normalization, and Gamma

The reader is published separately at `n-ball-volume.html`. Throughout,
\(n\) is the ambient dimension and \(V_n(R)\) denotes enclosed ball volume;
the boundary sphere has dimension \(n-1\).

## Exact computation and checked theorem contracts

The finite evaluator is
\[
 M_n(p,R)=c_n p^{\lfloor n/2\rfloor}R^n,\qquad
 c_0=1,\quad c_1=2,\quad c_{n+2}=\frac2{n+2}c_n.
\]
`FiniteNBallVolume` already proves its recurrence, scaling, nonnegativity,
monotonicity, and endpoint enclosure. `NBallGaussian` adds:

- `gammaHalfCoeff`: \(g_0=1\), \(g_1=1/2\),
  \(g_{n+2}=(n+2)g_n/2\).
- `nBallCoeff_mul_gammaHalfCoeff`: \(c_ng_n=1\), proved by induction.
- `nBallVolumeModel_gamma`: \(M_n(p,R)g_n=p^{\lfloor n/2\rfloor}R^n\).
- `NBallRaw.volume`: literal endpoint evaluation at each input stage.
- `NBallRaw.volume_valid`: valid supplied inputs with nonnegative lower
  endpoints give a valid output, in every dimension. This includes irrational
  inputs. The proof infers upper bounds internally from stage zero and uses
  the existing constructive multiplication width estimate. No caller-supplied
  precision schedule or bound is required.
- `NBallRaw.volume_equiv`: equivalent valid nonnegative input presentations
  give equivalent outputs, using `RealRaw.Equiv`.

The public `NBallRaw.value` wrapper removes the internal nonnegative-box
restriction. `nonnegativePart` clips each endpoint below at zero;
`nonnegativePart_valid` proves validity for every valid input, and
`nonnegativePart_equiv_self` proves exact agreement with the input whenever
its represented value is nonnegative, using `RealRaw.Le`. Early intervals
may cross zero. `value_valid` and `value_equiv` now quantify over arbitrary
valid presentations. `value_compute_of_nonnegative` identifies the public
evaluator with the original endpoint computation on already nonnegative boxes.
Negative inputs are totalized by their nonnegative parts; the physical radius
domain remains nonnegative. These theorems establish the formula's value,
not its role as a geometric volume.

The browser uses exact integer fractions and the literal `piMachin.compute`
recursion. It chooses a refinement stage adaptively and rounds lower decimal
endpoints down and upper endpoints up. Its dimension and radius limits are
interface limits; the Lean theorems quantify over every natural dimension.
`check_n_ball.lean` emits 213 exact fixtures for the browser regression test.
The JavaScript is independently implemented, not extracted or formally verified.
Tests also check refinement, all supported coefficient identities, zero radius,
invalid inputs, large dimensions, and outward rounding.

General coefficient, enclosure, representation-invariance, and triangle proofs
use only the standard logical axioms. `NBallRaw.volume_valid` and `NBallRaw.value_valid` also inherit
`RealRaw.mul_valid_of_nonneg_bounded`'s existing `native_decide` proof of the
fixed rational fact \(0<2\) in `Basic.lean`. Its exact axiom name is recorded
in the publication report. Runtime examples use `native_decide`; no `sorryAx`
or Mathlib dependency is accepted by the publication audit.

## Gaussian progress

For an arbitrary finite list of rational cell masses, the new theorems prove
\[
 \left(\sum_i a_i\right)^2
 =2\sum_{i<j}a_ia_j+\sum_i a_i^2,
 \qquad
 0\le a_i\le\delta\Longrightarrow
 \sum_i a_i^2\le\delta\sum_i a_i.
\]
`gaussian_square_split` retains the diagonal exactly;
`gaussian_diagonal_bound` controls it as cell masses shrink. These are concrete
finite lemmas for the square-to-triangle Gaussian route, not a proof of the
slope substitution or a compact/full-line Gaussian integral.

## Analytic identities still to construct

The intended Gamma computation, for positive represented \(s\), is
\[
 \Gamma(s)=\int_0^\infty t^{s-1}e^{-t}\,dt.
\]
Each particular construction must justify compact integrals, endpoint control
near zero, and an effective tail. General powers also need their represented
logarithm/exponential construction. Integration by parts should then establish
\(\Gamma(s+1)\simeq s\Gamma(s)\); substitution should prove
\(\Gamma(1/2)\simeq\sqrt\pi\) from an independently normalized Gaussian.
Consequently \(g_n\) should be identified with \(\Gamma(n/2+1)\) in even
dimensions and with \(\Gamma(n/2+1)/\sqrt\pi\) in odd dimensions.

For positive dimensions, compare Cartesian and radial computations:
\[
 \int_{\mathbb R^n}e^{-\sum_i x_i^2}\,dx
 \simeq\pi^{n/2}
 \simeq nV_n(1)\int_0^\infty e^{-r^2}r^{n-1}\,dr
 \simeq V_n(1)\Gamma(n/2+1).
\]
The product and radial-shell comparisons need finite enclosure and tail proofs.
Only after those bridges does the formula become the geometric volume theorem
\[
 V_n(R)\simeq\frac{\pi^{n/2}R^n}{\Gamma(n/2+1)}.
\]
Do not assume that identity in a certificate. The Gaussian normalization should
use the independent geometric circle-area value of \(\pi\), via the bounded
slope route in `GAUSSIAN_CONVOLUTION.md`, to avoid circular reasoning.
The corresponding weighted Gaussian target is
\[
 \int_0^\infty r^m e^{-ar^2}\,dr
 \simeq\frac{\Gamma((m+1)/2)}{2a^{(m+1)/2}},\qquad a>0,\quad m>-1.
\]
Boundary area requires its own geometric/derivative bridge; the calculator
displays the classical formula \(A_{n-1}(R)=nV_n(R)/R\) only for \(n\ge1\)
and \(R>0\). The zero-dimensional volume convention is \(V_0(R)=1\).

References for the analytic targets, not imported foundations:
[DLMF Gamma integral](https://dlmf.nist.gov/5.2#E1),
[recurrence](https://dlmf.nist.gov/5.5#E1), and
[half-integer value](https://dlmf.nist.gov/5.4#E6).
