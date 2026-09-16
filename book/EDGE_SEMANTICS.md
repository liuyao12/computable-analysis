# Statement definitions and proof use

The mathematical bundle is **Computable number**. Its checked declarations
begin with rational intervals, then the evaluator and validity conditions,
then equality, order and refinement. The reader regroups the same declarations;
it does not alter their exported Lean text or create a new mathematical object.

Solid black arrows from the sine/cosine bundle, pi, and the integral definition
point directly to the common statement in every proof route. S and C have
separate reference witnesses inside their shared visible bundle. The C path
reaches the actual cosine evaluator used by the integral, rather than pretending
that the convenience name C is literally spelled in the integral definition.

`proof_semantics.py` checks these paths by unfolding definition bodies only:
no theorem proof is allowed on a statement-definition path. These direct arrows
are deliberately not removed by transitive reduction. Solid black arrows show
construction/type prerequisites. Colored arrows require a path entered through
a stored proof/certificate body, not only its declaration type. These references
record actual use by that derivation, not logical indispensability. Node fills
remain an independent indication of dependence on Mathlib reals.

The typed edge data is exported in `reading/maps.json`. The older technical
reference graph remains its combined-dependency snapshot. The tests compare the
new views with the same verified declaration export; algorithms, theorem terms,
and proof-size reports are unchanged. Both original chapters remain untouched.

```sh
python3 book/checks/test_edge_semantics.py
python3 book/checks/test_graph_roles_browser.py
```

## General integration, separate from the cosine example

The **Integrals** node contains the shared enclosure construction and its
refinement, validity, and identification theorems. These five exact exported
cards were moved out of the cosine-specific bundle, not copied or rewritten.
A black arrow to the native FTC is checked from the FTC declaration's type;
a black arrow to the common conclusion unfolds definitions only. The
cosine-specific sum remains a separate instantiation. No universal integrability
assertion or new mathematical hypothesis is introduced.

All edges now participate in the ordinary rank layout. Statement edges are
solid black, not dashed and not excluded using `constraint=false`. The reader
avoids large cluster obstacles so these arrows do not take perimeter detours.
Proof use remains colored; shared node backgrounds still identify Mathlib-real
use. The edge inspector preserves the distinction between a definition's role
in a statement and a theorem's role in a proof even though both definitions
and other construction arrows are black.
