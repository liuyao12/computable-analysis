# Purpose, scope, and mathematical contract

## A foundation others can use

The purpose is a reusable real and complex analysis library whose numerical
content remains visible as rational algorithms. A downstream project should
be able to import the foundation, construct its own objects, and prove exact
mathematical laws without adopting Mathlib's real or complex number types.
This is an alternative collection of objects and APIs, not an automatic
substitution for every theorem written against those other types.

The foundation includes representations, arithmetic, equality and order,
functions with explicit domains, limits, function-specific continuity,
differentiation and integration constructions, series, elementary functions,
and reusable complex and ODE constructions. The calculus course develops
these tools through particular functions and their proved monotone or
convex/concave pieces; it does not depend on first building universal
continuity or derivative theories.

## Construct, identify, compare

A construction has three distinct obligations. First give its algorithm and
prove validity. Then prove the mathematical property advertised by its name.
Finally prove uniqueness or comparison whenever interchangeability is claimed.
Validity alone does not identify an integral, derivative, or solution.

For valid represented values, exact equality is written

$$
x\simeq y.
$$

For real values this means `RealCompute.Equiv`; the analogous complex relation is
`ComplexCompute.Equiv`. Equality of values does not require equality of programs,
finite-stage intervals, or precision schedules.

The mathematical number types are the quotients of valid names by these
relations: `ComputableAnalysis.Real` and `ComputableAnalysis.Complex`. Raw equivalence is exactly
equality of their quotient values. Keep particular computations available for
execution rather than choosing a preferred algorithm as part of a number's
mathematical identity.

A raw function is one computation on its declared domain. Its justified
extension gives the usual mathematical map $f:U\to\mathbb C$, with $U$ open
for holomorphicity. Different domains are related by compatibility and
extension; equality of partial functions also includes their domains.
Nonempty-overlap agreement is not a global equivalence relation. Use germs
at a fixed point when local agreement is to define an equivalence class.
It can generate a broader equivalence by finite chains. For analytic
continuation, admissible presentations are connected holomorphic local
functions; their continuation class can retain different branches. Direct
overlap is then sufficient, not necessary, for chain equivalence.

Public statements allow arbitrary valid represented inputs and coefficients,
including irrational ones. `RealCompute.compute` has a function type; that type
alone is not a certificate that every supplied function is executable.
Concrete executable constructions and operations preserving their
executability remain part of the foundation.

## Mathematical laws and particular existence

An agent works function by function: it chooses a method from the actual
structure, proves the construction's evidence, and checks its exact
mathematical role. For integration, split at proved monotonicity or
curvature pieces when available; use explicit finite range bounds on the
remaining pieces. For derivatives, construct the needed local secant or
quotient bounds for that function. The book and skills guide this work; no
universal continuity or derivative construction is a prerequisite, and the
choice of method need not itself be a single formal algorithm.

Common integral laws normalize constants, add over adjacent intervals, and
preserve lower and upper bounds supplied by finite step functions. They do
not by themselves guarantee universal existence or uniqueness. General
continuity and derivative interfaces may help compare supplied
constructions, but are supporting tools rather than prerequisites for the
course's function-specific arguments. Each construction states the local
validity, bounds, and agreement evidence it actually uses.

A law about supplied, justified objects can be complete without a theorem
that all objects of some broad class exist. A particular construction must
still supply its validity, domain, convergence, derivative, or solution
evidence. A record field assuming the desired result is not its proof.

Precision schedules, partitions, local charts, and turning-point brackets
belong below the public statement. Agreement results justify hiding those
choices. Genuine domain, branch, pole-avoidance, and constructive-existence
hypotheses remain visible when needed.

## Repository boundary

The root Lake package contains the independently buildable foundation.
`subprojects/special-topics` is a downstream package in the same repository.
It contains specialized theories, worked examples, teaching catalogues, and
support modules that still need decoupling before promotion. That last group
is not being declared mathematically specialized: its present location records
a software dependency, not a judgment about its eventual role.

Riemann–Roch and Riemann–Hilbert developments, Fuchs and Painlevé theory,
modular-function applications, and concrete physical applications are outside
this textbook. General lemmas needed by those projects can be promoted once
they have an independent import closure and their scope is documented.

The opening circle, solid-sphere, and arctangent constructions are deliberate
reference cases, as are the compact agent examples. They expose proof patterns
without importing the broader pedagogical catalogue into the foundation.
