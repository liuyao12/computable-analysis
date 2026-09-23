# The cosine-square showcase

The checked target is
$$
\int_0^{1/2}\cos^2(\pi x)\,dx=\frac14.
$$

`CosineSquareData.lean` defines one rational rectangle computation and proves
its validity independently of the answer. The internal coordinate is
$t=2x$. A stage squares the closed geometric cosine samples at a dyadic
mesh, adds the certified uncertainty radius, takes prefix intersections,
and clips to the known range. Scaling by $1/2$ gives the public integral.
Its width is at most $225\,2^{-n}$. This conservative bound is a theorem
about the literal program; the page's finer nested-radical rectangle pictures
are independently computed illustrations, not literal Lean output stages.

`CosineSquareSymmetry.lean` pairs reflected left/right sums, uses the circle
identity, and controls the remaining endpoint and sample errors. It proves
`integral_via_symmetry` without using the finite FTC.

`CosineSquareFTC.lean` constructs the primitive's derivative model by the
product rule, proves a local finite-difference bound on every rational cell
of the half interval, applies the finite-sample FTC to the same chosen sums,
and evaluates the endpoints. It proves `integral_via_FTC` without importing
or using the symmetry integral evaluation. The cosine derivative itself
uses the already established complementary-angle identity; independence of
the value proofs does not mean disjoint trigonometric foundations.

Both theorems conclude:

```lean
CosineSquare.integral.Equiv (RealRaw.ofRat (1 / 4))
```

## Verified foundation and reproduction

This is a checked extension of the published proof snapshot
`f630241adeae35fc06a5fd4921a4df6396e291d0`. Its closed inverse, trigonometric
identities, and finite-sample calculus are retained at that exact revision.
The new modules are kept together here because the current root library and
the published reader use different source snapshots. They are not assumed
exports of the current root `ComputableAnalysis` import.

From the repository root, choose an empty build directory and run:

```sh
proof_base=$(mktemp -d)
git archive f630241adeae35fc06a5fd4921a4df6396e291d0 | tar -x -C "$proof_base"
cp book/cosine-square/ComputableAnalysis/*.lean "$proof_base/ComputableAnalysis/"
cp book/cosine-square/Check.lean "$proof_base/CosineSquareCheck.lean"
(cd "$proof_base" && lake build ComputableAnalysis.CosineSquareSymmetry ComputableAnalysis.CosineSquareFTC)
(cd "$proof_base" && lake env lean CosineSquareCheck.lean)
```

`Check.lean` exports the theorem types, complete inherited axiom lists, and
both elaborated project dependency closures to
`cosine-square-reports/proofs.json`. It fails for unfinished proofs, Mathlib
imports, a missing finite-reflection dependency, a missing FTC dependency,
or reuse of either value proof by the other. The inherited foundation uses
native computation certificates; their axioms remain visible in the audit.
The new proof files use kernel reduction for their rational constant checks.

The publication workflow builds and audits this package before replacing the
reader page. It tests both GIFs and paused images, typeset mathematics,
responsive layout, route switching, pinned source links, and preservation
of unrelated artifacts. The earlier cosine theorem and its proof map remain
available from `cosine-primitive.html`.

The RMS application is explanatory context. The exported theorem is the
squared-cosine integral, not a new formal signal-processing library.
