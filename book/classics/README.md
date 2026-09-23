# Classical proof pages

The publication pass adds sidebar entries for the already checked Cartwright
irrationality theorem, the Leibniz series, the Basel problem, and Euler’s sine-product proof. It preserves
the Cartwright declaration graph, audit, and size comparison, and the existing
four-route Leibniz viewer.

The Basel comparison is a mathematical outline with pinned source links.
The native theorem is checked by the existing Basel audit. The Mathlib column
is inspected against `Mathlib/NumberTheory/ZetaValues.lean` at
`338b8c00bd151fa07a0350cc17442e6eeda734e8`; the publisher verifies the complete
source hash and its cited declarations. The Euler page is additionally backed by the separately compiled and audited
[Mathlib companion](../euler-proof/README.md), which uses its own compatible
pin. No cross-foundation bridge or proof-size measurement is claimed.

Irrationality of $\pi^2$ is already proved in the published Cartwright snapshot
`f630241adeae35fc06a5fd4921a4df6396e291d0`. The newer Basel/Euler-sieve source
still has an explicit irrationality hypothesis. Its integration with the
earlier Cartwright theorem is a separate obligation. The reader and roadmap
must distinguish that integration gap from the existence of the proof.

Run `classic_proofs.py` after the cosine-square publication pass, followed by
`test_classic_proofs.py`, as specified in the publication workflow. The tests
check every sidebar entry, active navigation, mathematical rendering, mobile
layout, route controls, old proof viewers, and preservation of prior audits.

Every sidebar showcase begins with the minimum setup, followed immediately by
an explicit theorem statement in natural language. State domains, quantifiers,
hypotheses, and conclusions; use LaTeX for mathematical notation. Proof routes,
formalization status, implementation details, and measurements follow the
statement. In particular, distinguish the classical Fuchs and Painlevé theorems
from the parts currently checked in this project.

The page sources here follow this structure directly. Introductions for the
pinned cosine, Cartwright, and integral-family pages are maintained in
`statements/` and installed by the final publication pass, preserving their
existing proof anchors and audit artifacts. The browser checks cover all nine
showcases at desktop and mobile widths.

The polygonal complex-analysis page carries a persistent Bessel example beside
the narrative on desktop and after the first theorem on narrow screens. Its
four views illustrate coefficient scaling, triangle cancellation, a square
pole contour, and a logarithmic solution branch. The browser calculations are
illustrations; the page states the exact scope of the checked Lean results.
The publication pass requires `--cauchy-audit`, produced by
`lake env lean scripts/check_polygonal_cauchy.lean`, and publishes that audit.
