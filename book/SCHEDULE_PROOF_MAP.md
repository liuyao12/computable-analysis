# A supplied construction, not an integrability predicate

The integral is presented by data and correctness for a particular evaluator:
a chosen subdivision/evaluation plan, finite rational boxes, compatibility,
and shrinking widths. No `Integrable` predicate or existential selection of
a schedule is added to the public narrative or to the new Lean module.

`IntegralSchedules.lean` proves a small generic fact about a supplied sequence
of pairs: finite-prefix intersection gives a valid computation when the selected
bounds are compatible and shrink. Two such supplied constructions agree when
they have cross-compatible bounds for the same quantity. That latter hypothesis
must be proved; validity of arbitrary raw programs does not imply equality.
The module has no Mathlib or native noncomputable dependencies. It does not
supply a monotonicity certificate or a successful schedule for arbitrary inputs.

## The cosine proofs still concern the existing program

The actual common program is retained-mesh quadrature: at output k, intersect
all widened meshes r<=k, each evaluated at stage k. The new supplied-pair API is
shown as context, not inserted as a false dependency of old proof terms. The
numerical output, theorem signatures and old proof bodies remain unchanged.
The benchmark roots are unchanged as well; display-only declarations do not
inflate their measured dependency costs.

The graph now has a separate convergence node containing all three independently
proved validity certificates for that SAME program. The direct and concave-FTC
endpoint proofs explicitly reference their respective validity lemmas. The
Mathlib endpoint proof uses representation-to-overlap without referencing its
separate integral validity lemma. Therefore only the first two routes have an
arrow from validity to the endpoint conclusion. The Mathlib validity certificate
is still shown and checked, rather than quietly omitted.

The Mathlib route separately shows its endpoint representation: sine and pi
bridges plus the library primitive identity identify S(t)/pi with the same
real integral as the independent quadrature bridge. That distinction prevents
the map from implying that the primitive identity was used to prove the
quadrature correspondence. Native finite estimates and concave supporting
secants remain on their actual routes.

The target node is simply **Cosine primitive**. Proof-count labels are not part
of its name. The UI route selector remains, with one common proposition node,
solid black definition arrows, colored proof use, and Mathlib-real backgrounds.
The integral panel explicitly includes both finite indices and the conditional
schedule-independence result, without asserting universal diagonal convergence.

## Verification

The statement exporter obtains new declaration cards from Lean. The map builder
and tests verify every new edge's stored-reference witness, with entry through
the consumer's proof body; inspect definition-only statement paths separately.
They reject accidental reuse of the new context lemmas by the old roots, and
an invented Mathlib validity-to-conclusion edge. Existing cards are retained.
Browser checks compare exact code text, route roles, mathematical typesetting
and mobile rendering. The original public three-proof benchmark is unchanged.
