---
name: analytic-continuation
description: Formalize analytic continuation of a specific represented function along a specified route in this repository, proving local holomorphicity, overlap agreement, and any claimed endpoint or branch change. Use for logarithm, arctangent, algebraic branches, or local ODE solutions; not for an automatic continuation oracle or numerical plots alone.
---

# Analytic continuation of a specific function

Use the [formalization policy](../../FORMALIZATION_GUIDE.md#computable-foundations-exact-mathematical-theorems)
and [holomorphic-functions skill](../holomorphic-functions/SKILL.md). Keep
numerical constructions on rational intervals and boxes, with validity,
explicit error bounds, and representation invariance. Analytic continuation
is a proof strategy here, not a new universal operation or mandatory record.

Read [examples and current proof boundaries](references/examples.md) when
choosing the function or reporting what has been formalized. A strategy in
this skill is not an implemented theorem. For a requested example, construct
its local evidence; do not ask the caller to supply the desired continuation
or final monodromy identity.

## General monodromy tasks

When the request is a general monodromy theorem, use the checked
[continuation foundation](../../ComputableAnalysis/Continuation.lean) and
[precise scope ledger](../../docs/ANALYTIC_CONTINUATION.md). The earlier advice
to avoid a general path theory for one example does not restrict such a request.
Germs, derivative uniqueness, local gluing, finite chart chains, and the
finite transport theorem are now available. The affine client proves its own
local identity theorem and realizes every transport by actual charts.

Do not identify `FiniteSimplyConnected` with arbitrary continuous simple
connectedness without a subdivision bridge. Do not supply the local transport
laws for general holomorphic germs without proving analytic uniqueness and
chain comparison. Pathwise continuation is a genuine hypothesis; for a
specific function, construct it. The checked gluing theorem requires an
actual represented map with local models, not merely an abstract germ section.

## Specify the continuation problem

Fix an initial **local function**, its domain, and its branch normalization.
A value at one point alone does not specify a holomorphic germ. For example,
start a logarithm near \(1\) with value \(0\), a square root with value \(1\),
or arctangent near \(0\) with value \(0\), together with the respective local
function construction.

State the route and the singularities it must avoid. A chosen horizontal and
vertical route with rational vertices is often enough for the first example.
Such a choice is proof data, not a reason to restrict a requested theorem
about arbitrary valid represented endpoints or coefficients to rational ones.
If the endpoint moves, prove coverage and all estimates on its stated domain.

Distinguish the requested conclusions:

- Construct a continuation along this route and identify its terminal local
  function, with an exact represented endpoint identity when requested.
- Prove agreement of two constructions or refinements along the same route.
- Compare different routes or compute a change after a closed loop.

The last two require additional proofs. Local agreement does not by itself
prove path independence or trivial monodromy.

## Construct and connect the local functions

For a fixed route, provide a finite sequence of local domains that covers
the whole route in order, with a neighborhood of each transition point in
both adjacent domains. Prove explicit separation from poles and branch
points throughout each piece. Endpoint checks alone do not certify a path.
Do not invoke compactness or an unproved search to obtain a finite cover.
A supplied cover with proved coverage is sufficient; for a concrete example,
construct it. If using a search, prove its termination from the available
quantitative data. If a next chart cannot be justified, report the obstruction
or missing lemma; do not assume every germ continues along every proposed route.

Construct valid local evaluators, derivatives, and derivative-continuity
moduli as required by `FunctionTheory.Holomorphic`. Choose the method for the
function: an algebraic branch with root separation, a local series with tail
bounds, a normalized definite-integral computation, or a proved local ODE
solution. A finite jet or a continuous root-tracking picture is insufficient.
Local holomorphicity need not be proved by first producing a Taylor series;
if Taylor re-expansion is the chosen method, justify its reconstruction and
coefficient transport rather than assuming the missing Cauchy–Taylor bridge.

At each transition prove **equality of local values on an open overlap
neighborhood**, using `ComplexRaw.Equiv` for arbitrary valid represented
inputs there. Prove a function-specific identity, or a uniqueness theorem
whose hypotheses have been established. Equality at a single point is not
overlap agreement. Equal derivatives plus a common value require a proved
comparison theorem on the chosen connected neighborhood. Do not invoke an
unproved identity theorem as an automatic tactic.

Intersections can have several components. Specify the component or smaller
connected neighborhood through which the route passes; agreement on every
component is not necessary and can be false for different branches. Never
reset to a principal-branch evaluator at each step. Preserve the initial
normalization through the proved transitions.

## Prove the requested consequence

Compose the established transitions along the finite route. Track validity
and representation invariance at represented endpoints. When approximations
are propagated numerically, provide error budgets and a precision schedule
for the finite chain; do not silently replace an approximate seed by exact
initial data. Prove the comparison results needed to hide internal chart,
mesh, and precision choices in the public theorem.

If integrating a derivative, construct the particular oriented edge integrals
from whole-chunk value enclosures and add their certified values. State a
base-point-normalized definite-integral identity. Do not add a separate
primitive notion or require a universal contour-integral operator. The
[integral strategy reference](../computable-analysis-formalization/references/integral-computation-strategies.md)
applies to each edge; reverse orientation and refinement need justified
agreement lemmas.

For a loop, compare the terminal germ with the initial germ near the same
base point. A change in value is a conclusion to prove, not a branch-index
field to assume. Check orientation and normalization explicitly. A branch
cut is a choice of one displayed branch; crossing that cut need not cross a
singularity of the continued germ. Separate continuation along the chosen
route from extension across a genuine pole or branch point.

Do not add Riemann surfaces, a universal path type, or a general monodromy
theorem merely to complete one example. Retain useful finite concatenation,
reversal, and equivalence lemmas when there is actual reuse. A broader theorem
may later express laws about these supplied constructions.

## Monodromy for differential equations

Use the [chapter definition](../../book/classics/monodromy-section.html):
monodromy sends an initial solution germ to the terminal germ at the same
base point. A germ is defined by agreement on a neighborhood, not by a
single value. For a homogeneous linear system, prove continuation preserves
linear combinations and that reversing the route gives the inverse.
Do not assume local existence, uniqueness, or the solution-space dimension
merely from the equation's order.

Fix the ordered basis and use solution vectors as columns of \(\Phi\).
Identify the constant matrix by proving \(\Phi^\gamma\simeq\Phi M_\gamma\)
throughout a base-point neighborhood. Changing basis to \(\Phi C\) changes
the matrix to \(C^{-1}M_\gamma C\). With \(\eta\star\gamma\) meaning
\(\gamma\) first and \(\eta\) second, composition has order
\(M_{\eta\star\gamma}=M_\eta M_\gamma\); check this convention before
multiplying computed transitions. Prove these laws when claimed.

A supplied loop computation is enough for its own terminal comparison.
Claim a representation of the fundamental group only after constructing
continuation for its stated class of loops and proving independence of
charts and homotopy invariance. Regular singularity need not mean trivial
monodromy, and trivial monodromy need not make a singularity removable.
Keep this operator distinct from the monodromy theorem about single-valued
continuation on a simply connected domain.

## Validation and reporting

Build the new Lean module and its concrete client. Audit the elaborated
proof/import dependencies for unfinished proofs and forbidden foundations.
Existing adjacent checks are listed in the example reference; they are not
a continuation test suite. Exercise the constructed numerical schedules,
and verify the actual overlap and endpoint theorems at their full scope.

Report separately: checked local functions, checked overlap comparisons,
checked route coverage, and checked terminal or loop identity. A final
endpoint formula without a chain of local holomorphic functions is not yet
a formal analytic-continuation theorem. Label illustrations and proposed
showcases as such in the reader.
