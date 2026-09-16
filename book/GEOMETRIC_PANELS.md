# Geometric panels and animations

`illustrations.py` builds reproducible GIFs and static reduced-motion posters.
The sector uses the rational circle chart at u=2/3, with exact inner and outer
polygon bounds. Pi remains **4 A(1)**: A(1) is the quarter-disk area. The inverse
provider and all its checked declaration cards are folded into Sine and cosine;
no dependency is discarded simply because it has become internal to a bundle.

The integral panel now introduces a concave integrand with a supplied Lipschitz
bound, using chord lower sums and midpoint upper sums. This is a restricted
mathematical exposition, **not** a claim that the existing general Lean engine
has acquired a concavity parameter. The chord/midpoint constructor and its
representation edge to the existing cosine quadrature are not yet formalized.
The panel discloses that status. In the existing FTC, the concavity hypothesis
belongs to the primitive, not necessarily to its derivative/integrand. None of
the three checked proof terms or definitions is changed to conceal this gap.

The quadratic in the animation is g(x)=1−x²/2 on [0,1]. Its upper supporting
segments have the same areas as midpoint rectangles. They are a visual aid,
not a derivative oracle required by the proposed midpoint construction. Exact
fraction tests check the gaps and nested bounds; CI separately tests GIF loading,
pause/play, reduced motion and the preserved declaration text.
