# Chapter 1 continuation: two classifications of circle-area pi

The circle-area computation of $\pi$ has two established number-theoretic
properties in this project:

$$
\operatorname{Irrational}(\pi_{\rm circle}^{2}),
\qquad
\operatorname{Transcendental}(\pi_{\rm circle}).
$$

These belong with the first chapter's definitions of rational, irrational,
algebraic, and transcendental values. The irrationality theorem says that
$\pi_{\rm circle}^{2}$ is not equivalent to any rational value. The
transcendence theorem says that no nonzero polynomial with rational
coefficients vanishes at $\pi_{\rm circle}$. Their raw-name statements use
`RealCompute.Equiv`; they do not use Mathlib's real-number type.

The project contains Lean proof developments for these results in the
companion source `subprojects/special-topics/ComputableAnalysis`. The
transcendence development proceeds through Hermite–Lindemann and the
geometric half-turn values of sine and cosine. These proofs should be
presented as foundation results, while their Lean dependency graph is
promoted into the independent root package. The root package must remain
free of imports from its companion. Until that promotion is complete, the
textbook records the theorem statements and proof route without implying
that the independent root build already contains those declarations.

Although transcendence of $\pi$ implies irrationality of $\pi^2$, the direct
irrationality proof is still worth retaining. It gives a separate, more
elementary argument and lets readers see what can be proved without the full
transcendence machinery.

## Transcendence of $e$

Classically, proving that $e$ is transcendental is substantially simpler than
proving that $\pi$ is transcendental. Hermite–Lindemann gives the result by
applying its theorem to the nonzero algebraic input $1$, since
$e=\exp(1)$. In our foundation this becomes a short corollary once the
Hermite–Lindemann theorem and the equivalence between its exponential and
our constructed `exp` are available at the required real value. The proof
still needs that exact bridge; the classical shortcut does not by itself
establish a theorem about our represented number.

## Package boundary

The [value-predicate API](01c-real-classification-api.md) is available in
the root package. The separate $\pi$ proof developments are in the
companion package. Promoting either proof requires reviewing its
dependencies.
