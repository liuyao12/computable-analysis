# Identify the mathematical object

A valid rational-interval computation supplies a represented value. Naming it
does not prove what it is. For every named number, function, derivative,
integral, or solution, distinguish the following obligations.

1. **Construct and validate.** Supply the algorithm, prove ordered and nested
   intervals, and prove that their widths shrink to zero. No prescribed rate
   is part of the definition. Preserve executability for executable inputs.
2. **Identify.** State the mathematical property being claimed independently
   of the algorithm's stages, then prove that this computation satisfies it.
   Give the full domain, normalization, sign, initial data, or branch needed
   by the claim. A name, numerical agreement, or validity theorem is not this
   identification.
3. **Compare when needed.** If the claim identifies a unique object or makes
   two implementations interchangeable, prove a suitable uniqueness or direct
   comparison theorem. Preserve each theorem's stated scope. Do not require a
   universal classification or existence theorem before a useful conditional
   law or a particular identification.

The public mathematical statement should be usable without inspecting the
implementation. Its proof may inspect and unfold the algorithm to derive the
rational inequalities. Hide precision schedules and recurrence details below
that statement, retaining the estimates for computational use. This is a
discipline for concrete theorems, not a request for a new universal record of
"identified objects."

## The square-root example

Prefer the function-level inverse law when it is available. The main library
already states `sqrtRaw_mul_self_equiv_of_domain` for every nonnegative
rational input in `ComputableAnalysis/AlgebraicFunctions.lean`; it includes
all nonnegative integers. `sqrtRaw_valid` proves validity separately.
`squareOnUnit_forward_sqrtRaw_equiv_rat` and `sqrtOnUnitBisectionSearch` are
particular inverse adapters on \([0,1]\), not the scope of the general
rational square-root law. Do not infer a global represented-input theorem
from this adapter; check the separate extension and its actual hypotheses.

First define a computation with a neutral local name, say \(s\), and prove its
validity. To identify the positive square root of \(2\), establish
\[
s\ge0,\qquad s\cdot s\simeq2.
\]
The square identity alone also admits the negative root. Nonnegativity and
the square identity are mathematical properties of the value, not conditions
on how its program is written. A comparison with another nonnegative root
can then use nonnegative-root uniqueness or a direct interval argument.

`SquareRootSecantNewton.sqrtTwo_valid`,
`sqrtTwo_mul_self_equiv_two`, and `sqrtTwo_equiv_bisection` illustrate the
separate jobs. In the current publication they are in the foundation proof
bundle; do not silently advertise them as exports of the main Lean library.
Check the actual source and build boundary when moving or citing them.

For the function on nonnegative inputs, the public contract is
\[
S(x)\ge0,\qquad S(x)\cdot S(x)\simeq x.
\]
Prove it on the claimed domain, with validity and representation invariance.
An evaluation at a rational input is an intermediate result if the request
is for arbitrary valid represented inputs. Irrational evaluation remains a
derived construction from the primary rational-input function.

The agent's work is to derive the interval inequalities and prove the bridge,
with Lean checking the proof. Do not replace the bridge by a field assuming
the requested identity, or inspect a long decimal output as evidence of it.
Reader-facing introductions may leave these proofs as optional exercises.

## Choose properties that support the name

| Claimed object | Appropriate mathematical evidence | Insufficient by itself |
| --- | --- | --- |
| Positive square root | Square identity and nonnegative range, with comparison when needed. | Valid intervals or the square identity without a sign. |
| A computation of \(\pi\) | A justified geometric normalization, or exact comparison with an independently identified geometric computation. | Many matching digits, or an equation with multiple solutions and no normalization. |
| Exponential | Actual derivative/initial-value or other justified characterizing laws on the stated domain; construct the evidence for the supplied evaluator. | A coefficient recurrence, a formal derivative, or agreement of two candidates without an established mathematical role. |
| Logarithm or inverse | A forward/inverse identity, the proper range or branch, and domain evidence; uniqueness or comparison where claimed. | Naming an inverse, local agreement without branch control, or a root equation alone. |
| Sine and cosine | A justified geometric comparison or coupled analytic laws with normalization and appropriate uniqueness. | The identity \(S^2+C^2\simeq1\) alone. |
| A definite integral | The justified integral relation for the supplied integrand and segment, or proved comparison with a justified construction. Keep existence and conditional laws separate. | A valid candidate, a sampled sum without range/tail evidence, or an endpoint agreement assumed in a record. |
| A series value | A finite-prefix/tail comparison to the independently stated summation claim; an additional identification for any further name. | Shrinking widths or a coefficient recurrence alone. |
| An ODE solution | Actual analytic equation and initial/boundary conditions for the evaluated function; comparison or uniqueness on the stated domain when claimed. | A formal power-series equation or a record storing the desired solution equality. |
| Volume, Gamma, Gaussian, or kernel | The claimed geometric, integral, normalization, or analytic relation, proved for that supplied construction. | A valid polynomial formula, coefficient algebra, or a suggestive name. |

These are examples of sufficient proof routes, not mandatory universal
definitions. In particular, retain the project's method-independent integral
policy and its exact conditional laws. Do not impose one preselected class
of integrands, one convergence schedule, or an unproved uniqueness field.

## Audit exposition and formalization together

For each mathematical claim record:

- The advertised object, mathematical statement, domain, and representation.
- The actual constructor and validity theorem, or the precise supplied
  validity hypothesis of a conditional theorem.
- The identification statement and proof, distinguishing proved inequalities
  from assumptions carrying the intended conclusion.
- Sign, normalization, branch, endpoint, or initial/boundary data that remove
  ambiguity. Add uniqueness or a direct comparison when the claim uses it.
- Representation invariance and the exact equality relation, normally
  `RealRaw.Equiv` between valid representations, with analogous complex laws.
- The source/build boundary: main library, pinned companion, historical file,
  or unpublished working tree; record any checker and its actual result.
- The public exposition that makes the claim. Correct an overstatement or
  label the missing bridge; keep valid checked laws at their current scope.

Use statuses such as *candidate*, *valid construction*, *identified on the
stated domain*, *conditional law*, *comparison*, and *open bridge*. A source
scanner can inventory hashes and find declarations for review. It cannot
establish identification, noncircularity, uniqueness, or kernel correctness.
Do not report every scanned file as mathematically audited.

Prioritize a concrete missing bridge that unlocks an actual application.
Repair clear false claims immediately. Retain working algorithms and checked
theorems; no wholesale rewrite is needed just to enforce the distinction.
