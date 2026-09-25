# Theorems about constructed objects

Consult this reference when choosing a theorem's scope or reviewing whether
a certificate has the right mathematical content. The project's preferred
general result derives a useful law about supplied constructions. Finding the
weakest possible existence hypotheses is a separate objective.

## Identify the task

- **Construction:** define the particular evaluator and prove its mathematical
  properties. An existence proof of a valid name and an executable constructor
  are different claims; inspect how numerical witnesses are selected.
- **Conditional law:** take specified objects and their genuine mathematical
  properties, and derive a new conclusion. Constructing all possible inputs
  is not part of this task unless requested.
- **Comparison:** prove that independently specified computations agree.
  Keep the finite comparison or overlap argument visible beneath exact value
  equality. If agreement is itself an input, describe the result as transport.

Do not create a new hierarchy of certificate types to enforce this list.
These are questions for the formalizer, not mathematical definitions.

## Separate data, evidence, and conclusion

Write the intended statement in natural language before choosing Lean types.
Identify each supplied object and what makes it meaningful: validity of boxes,
domain membership, representation invariance, derivative estimates, whole-chunk
ranges, finite tail bounds, a root equation, or a differential equation.
Then identify the claim the proof must add.

For example, a supplied solution and a local differential-equation residual
estimate can imply a growth bound without a universal solver. A supplied root
can support a deflation theorem without a root-existence theorem. A Cauchy
representation can imply a power-series representation without proving the
Cauchy formula from the most general differentiability hypothesis first.

Conversely, merely naming a root, derivative, integral, or solution does not
prove the role its name suggests. A record containing the desired value
equality or existence assertion is a convenient interface to that assertion,
not its independent derivation. Look through the record fields, not only the
public theorem signature. Test the contract conceptually against a wrong
value: identify the hypothesis that rules it out.

## Choose useful hypotheses

Prefer evidence that supports a short, inspectable finite proof and can be
supplied in a concrete example. Hypotheses can be stronger than classical
minimal conditions; state their actual strength. Do not impose the same
precision schedule, partition, chart, tail pattern, or proof record on every
example merely because it was convenient once.

Prove independence of internal construction choices before hiding them.
Keep genuine pole, branch, domain, and constructive existence hypotheses.
Do not call a rational-input or finite-model theorem a theorem about arbitrary
represented inputs or analytic functions without the connecting proof.

For a requested concrete identity, the user is asking for an application:
construct its hypotheses and prove the conclusion. A general conditional
theorem alone does not finish that request. For a requested general law,
an unrequested universal constructor need not be developed.

## Review and reuse

Read the nearest concrete example and the fields of every certificate used
by the proposed theorem. Reuse finite arithmetic and comparison lemmas.
Introduce a shared record only when it reduces actual repeated proof work.
Keep existing stronger theorems; do not weaken their statements to fit this
methodology. Record the distinction between constructor, law, comparison,
and interface in the relevant theorem ledger and presentation.

The [project-wide audit](../../../docs/CONSTRUCTION_FIRST_AUDIT.md) gives
concrete examples of sound conditional laws and comparison interfaces whose
supplied assumptions must remain visible. Integration and series methods
are in their own references; this contract review applies equally to other
families, including geometry, algebra, ODEs, and PDEs.
