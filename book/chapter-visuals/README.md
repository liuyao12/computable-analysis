# Visual chapter edition

A presentation pass on the fifteen main-reader chapters after Chapter 2.
Each chapter has a concise opening, one adjustable worked diagram and a link
to its detailed construction. Existing mathematical statements, proof bodies,
formalization status, proof maps, anchors and other illustrations are preserved.

The diagrams use rounded coordinates to sketch geometry. The finite arithmetic
readouts use exact `BigInt` fractions. They are explanatory examples, not new
Lean proofs or replacements for the constructions stated in the chapters.
The trigonometric examples retain the manuscript's period of two. The elliptic
example uses the manuscript's rational circle substitution; its two curves
have different sampling coordinates and are not compared by drawn area.

`build_visuals.py BASE_SITE` regenerates the reviewed HTML and manifest.
`apply_visuals.py SITE` checks the base chapter hashes and source hashes before
applying the edition. Its preservation check covers every other existing file.
The checked publication base is Pages run `38054353598`.

The current public main reader ends at Chapter 17. Later technical reference
chapters remain unchanged; their existing figures and proof comparisons are
not converted into demonstrations that could imply additional checked results.
