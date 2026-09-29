# Continuation methods and their proof obligations

Choose a route from the function's available construction. Several methods
can describe the same continued germ; agreement is a theorem to prove, not
part of the choice of method. The common output is actual local holomorphic
charts, coverage of each path piece, and neighborhood agreement at transitions.

## Chains of Taylor expansions

Start from a certified local series, not merely a jet or a value at its center.
Choose the next center strictly inside its convergence disk, retaining a
rational safety margin. For a displacement \(h\), construct
\[
b_k=\sum_{n\ge k}\binom nk a_nh^{n-k}.
\]
Prove coefficient-tail bounds and equality of the two sums on a smaller
open overlap, using finite binomial identities and controlled tails. Budgets
must cover both coefficient truncation and subsequent evaluation. Repeating
this finite construction continues the germ along a supplied covered route.
Never infer a convergence radius just from formal coefficient transport.

Use arctangent beyond its original disk as a first example. A chain of disks
can avoid \(i\) and \(-i\) while reaching real arguments outside the original
Taylor radius. A different path can change the branch. For general
holomorphic maps, deriving the initial series and its quantitative bounds
is still part of the missing Cauchy–Taylor bridge.

## Functional equations

A proved relation can evaluate a new chart from an old one. State exactly
which transformed arguments lie in the known domain, and certify all newly
introduced denominators on the whole neighborhood. Prove agreement on an
open overlap by the relation, then compare alternative transformation chains.

For Gamma, after constructing its holomorphic right-half-plane integral and
proving its recurrence, use
\[
\Gamma(z)=\frac{\Gamma(z+m)}{z(z+1)\cdots(z+m-1)},
\qquad \Re(z+m)>0.
\]
Avoid the nonpositive integers and show independence of the chosen shift by
iterating the recurrence. The result is meromorphic on the plane and
holomorphic off those poles. The recurrence alone does not select Gamma:
multiplication by a nonconstant one-periodic factor can preserve it. Retain
the original local function. Complex Gamma charts and these comparisons
are examples to construct, not current checked continuation theorems.

A functional equation need not cross a natural boundary. For
\[
F(z)=\sum_{k\ge0}z^{2^k}=z+F(z^2),\qquad |z|<1,
\]
points outside the circle still map outside it. The equation supplies no
known chart there. At dyadic roots of unity the radial values are unbounded;
their density prevents extension through any open boundary arc.

## Schwarz reflection

Take an upper-half neighborhood of an **open interval** of the real axis.
Construct continuous boundary values that are real on that interval and
holomorphic values above it. The reflected candidate below is
\[
F(z)=\overline{f(\overline z)}.
\]
`Holomorphic.reflect` checks the reflected open chart and `AgreeAt.reflect`
checks reflected overlap comparisons. To claim extension **across** the
interval, also prove holomorphicity at the seam. Boundary continuity and
real-valuedness are the classical sufficient conditions; their quantitative
adapter is not yet checked here. Do not claim the off-seam theorem proves it.
One function-specific route is a convergent real-coefficient series centered
on the interval, proving that both sides agree with that series.

Logarithm near a positive real interval illustrates reflection. A circle or
analytic boundary curve first needs justified local coordinate maps; the
real-axis formula is not automatically valid across an arbitrary curve.

## Algebraic branches and local equations

For \(P(z,w)=0\), use separated root boxes and a nonzero \(P_w\) bound
on each chart. Construct the root computation, derivative, and continuity;
prove uniqueness in that box to obtain overlap equality. Continue the
selected root, without choosing the principal root anew at each step.
Square root is the first test: one positive loop about zero exchanges the
two germs; a second returns to the initial one. Generic implicit-function
and branch constructors are not yet available in this interface.

For a local ODE solution, use a proved local uniqueness result on each overlap
and certify the finite path cover. A solution-space dimension or monodromy
matrix does not follow merely from the order of the displayed equation.

## Diagnose the obstruction

- A branch cut describes a chosen branch, not automatically a singularity.
- A pole prevents holomorphic extension through its location even when
  returning along a loop restores the germ.
- An essential singularity can also have trivial monodromy. For
  \(\sin(1/z)\), the principal lesson is the identity theorem's interior
  accumulation-point hypothesis: its zeros approach an excluded point.
- A natural boundary consists entirely of obstructions to direct extension;
  shrinking the step size cannot carry a Taylor chain across it.
- Agreement on one component of a disconnected overlap does not imply
  agreement on every component. Track the component used by the route.

The reader's examples have mathematical explanations and illustrations;
use the linked theorem ledger to determine which statements have Lean proofs.

## Proof sources and checks

Use [actual chart chains](../../../ComputableAnalysis/Continuation/Chain.lean),
[reflected overlaps](../../../ComputableAnalysis/Continuation/Reflection.lean),
and [realization](../../../ComputableAnalysis/Continuation/Realization.lean).
Build `ComputableAnalysis.Continuation` and run
`lake env lean scripts/check_continuation.lean`. These check the current
foundation, not all the function-specific examples above. See
[the ledger](../../../docs/ANALYTIC_CONTINUATION.md).
