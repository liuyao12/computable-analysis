# Statement definitions and proof use

The mathematical bundle is **Computable number**. Its checked declarations
begin with rational intervals, then the evaluator and validity conditions,
then equality, order and refinement. The reader regroups the same declarations;
it does not alter their exported Lean text or create a new mathematical object.

Gray dashed arrows from the sine/cosine bundle, pi, and the integral definition
point directly to the common statement in every proof route. S and C have
separate reference witnesses inside their shared visible bundle. The C path
reaches the actual cosine evaluator used by the integral, rather than pretending
that the convenience name C is literally spelled in the integral definition.

`proof_semantics.py` checks these paths by unfolding definition bodies only:
no theorem proof is allowed on a statement-definition path. These direct arrows
are deliberately not removed by transitive reduction. Gray solid arrows show
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
