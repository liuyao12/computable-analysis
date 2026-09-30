# Certifying zeros by the argument principle

Use this guide for a finite-region theorem about **all** zeros of a specific
constructed complex function. A plotted root list, small residual, or numerical
proximity to a line does not establish completeness or exact location.
Read the [current zeta/Gamma audit](../../../docs/FUNCTION_THEORY_ZETA_GAMMA.md)
before using a claimed repository bridge.

## Fix the analytic function and the counted region

Construct the actual represented function and local holomorphic witnesses on
an open neighborhood of the closed region and its boundary. Prove overlap
agreement for every continuation formula. For zeta, working with the entire
completed function can remove pole bookkeeping, but first prove its
construction, its relation to zeta, and that any prefactors introduce no
unwanted zeros in the chosen region. Do not assume the functional equation
as a substitute for constructing these functions.

Use a simple positively oriented polygon or another justified boundary.
Specify the height, boundary exclusions, disjoint isolating regions, and
whether zeros are counted with multiplicity. For meromorphic functions,
account for poles explicitly.

## Choose a proof for this function and region

Do not require a general Cauchy–Goursat theorem before starting. The skill
selects simpler checked laws and proves the bridges for the supplied function
and contour. Useful routes include explicit local factorizations with
nonvanishing regular factors, constructed logarithms on local patches, and
finite contour cancellation with certified coverage.

A polynomial comparison is another route: construct a polynomial with an
actual root count, certify the entire comparison boundary, and justify a
zero-free boundary deformation. Prove that this particular deformation
preserves the actual interior multiplicity count. Boundary winding invariance
alone does not establish that interior interpretation. Do not invoke an
unproved general Rouché theorem, or assume count equality in a comparison
record. A direct factorization route must also exclude omitted roots.

The method is skill guidance; its analytic and counting identities are
mathematical obligations, not projections of assumed certificates.

## Certify the whole contour

On every complete segment, compute value enclosures with an explicit error
and a positive lower bound separating the image from zero. If sampling is
used, prove between-sample control from derivative or interval bounds.
Endpoint values alone do not certify nonvanishing. Refine until every edge
has justified separation; a search needs a termination proof at its claimed
scope. Construct the reciprocal and the particular logarithmic-derivative
integral with the evidence required by the complex-integral skill.

Compute the winding integer with a certified argument lift, or compute a
contour integral and prove it equals an integer before isolating that integer:
\[
 \frac{1}{2\pi i}\oint_C\frac{f'(s)}{f(s)}\,ds=N-P.
\]
A tight interval around an integer does not by itself prove this formula or
integrality. Prove that the result is the **actual** count of interior zeros
minus poles, with multiplicities. Do not store that equality as an assumed
certificate field and present its projection as the argument principle.

## Prove existence, uniqueness, and exact location

Repeat the genuine count theorem on each isolating region. A count of one
for a holomorphic function proves one simple root only after the counting
semantics and root-existence bridge have been established. Construct a valid
represented root with a shrinking isolation schedule when the theorem is to
return a computation; nonconstructive existence alone does not provide it.

For the completed zeta function, prove
\[
 \xi(1-\overline s)\simeq\overline{\xi(s)}.
\]
Choose isolating rectangles preserved by \(s\mapsto1-\overline s\).
Uniqueness then forces the represented root to equal its reflection and hence
\(\Re s\simeq1/2\) **exactly**. The conditional algebra and root implication
are checked in `ZeroIsolation.fixed_realPart` and `unique_zero_on_line`.
The complex zeta construction, symmetry, count theorem, and actual isolating
rectangles remain open. An interval of small width around \(1/2\) is not equality.

Alternatively, critical-line sign changes of a constructed Hardy function can
prove roots there, provided its real-valuedness, continuous root construction,
and the comparison with the completed function are proved. A total count still
has to show that no zeros were omitted. Choose the route whose evidence is
available; do not assume the desired location in a root record.

## Prove completeness and publish the proof scope

Show the isolating regions are disjoint, lie inside the global region, and
that their multiplicity counts sum to the global count. Deal with roots on
excluded edges and the stated upper-height convention. Provide the exact
represented-input theorem, executable certificates, error schedules, and an
axiom/import audit. Mark numerical demonstrations separately from proved
claims. No root list can fill a missing complex-analysis lemma.

Rigorous computation is compatible with a proof. A primary example is
[Platt and Trudgian's finite-height result](https://arxiv.org/abs/2004.09765),
which uses interval arithmetic, critical-line root information, and Turing's
method for completeness. It is a reference for certification, not an imported
argument-principle theorem or an assertion that our repository has proved the
same result.

## Proof sources and checks

The exact reflection and uniqueness implication is in
[ZeroIsolation](../../../ComputableAnalysis/ZeroIsolation.lean). Run
`lake env lean scripts/check_zeta_gamma.lean` to check its dependency audit
and the initial zeta/Gamma constructions. The
[function-theory ledger](../../../docs/FUNCTION_THEORY_ZETA_GAMMA.md) records
the remaining analytic and counting bridges. These checks do not certify
any specific zeta-zero region yet.
