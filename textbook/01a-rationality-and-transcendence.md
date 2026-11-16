# Chapter 1 supplement: Rationality and transcendence

## Properties belong to values, not to their names

A valid `RealCompute` is a computation naming a real value. Different valid
computations can name the same value, so rationality and algebraicity must be
unchanged when the computation is replaced by an equivalent one. We state
these properties on the quotient `ComputableAnalysis.Real` of valid raw names, and pull
them back to any `RealCompute` representative. Equality here is equality in our
own quotient, equivalently `RealCompute.Equiv`; it does not use Mathlib's real
numbers.

For $x\in\mathbb{R}_{\rm CA}$, define

$$
\operatorname{Rational}(x)\;\Longleftrightarrow\;
\exists q\in\mathbb{Q},\;x=q,
\qquad
\operatorname{Irrational}(x)\;\Longleftrightarrow\;
\neg\operatorname{Rational}(x).
$$

A real is algebraic if it is a root of a nonzero polynomial with rational
coefficients:

$$
\operatorname{Algebraic}(x)\;\Longleftrightarrow\;
\exists P\in\mathbb{Q}[X],\;P\ne0\;\land\;P(x)=0.
$$

Define transcendental to mean not algebraic:

$$
\operatorname{Transcendental}(x)\;\Longleftrightarrow\;
\neg\operatorname{Algebraic}(x).
$$

These are propositions about represented values; they are not expected to be
decidable from an arbitrary interval computation. A proof can use the
computation, algebra, and explicit separation bounds appropriate to that
number. For instance, $\sqrt{2}$ is irrational but algebraic, whereas $\pi$
is transcendental. The definitions state the intended predicates; the
formalization status below records which example results are already proved
and which remain targets.

The corresponding predicates on a valid raw name $x$ are value predicates:
$x$ is irrational when no rational number is equivalent to $x$, and it is
transcendental when no nonzero rational polynomial evaluates to a value
equivalent to zero at $x$. Thus replacing $x$ by any $y$ with
$\operatorname{RealCompute.Equiv}(x,y)$ preserves both predicates. In Lean, these
can be exposed as predicates on `RealCompute` while being defined through its
quotient value; they do not depend on a choice of interval algorithm.

## Why irrationality matters for continued fractions

For a rational input, repeated integer-part and reciprocal steps eventually
reach remainder zero, so the continued fraction terminates. For an irrational
input, no remainder is zero and the expansion continues indefinitely. To
compute any particular finite prefix from a `RealCompute`, refine its rational
intervals until the next integer part and nonzero remainder are forced.
Irrationality ensures that each such finite search terminates, while the
specific interval computation supplies the algorithm and error bounds.

## Formalization status

The irrationality predicate already exists as `RealCompute.Irrational`, and the
foundation proves the exact criterion that the rational square root of $q$ is
irrational exactly when $q$ is not a rational square. This covers $\sqrt{2}$.
The proposition can also be read on the quotient `ComputableAnalysis.Real`; its raw-name
formulation uses `RealCompute.Equiv` directly.

The quotient carries rationality, irrationality, algebraicity, and
transcendence predicates. The raw-name versions agree with the quotient
predicates and are invariant under `RealCompute.Equiv`. See the
[value-predicate API note](01c-real-classification-api.md) for the distinction
between the representative and the quotient, and the
[circle-area chapter supplement](01b-pi-classification-theorems.md) for the
status of the two examples involving $\pi$.

The continued-fraction approximation target is in
[Chapter 8](06b-continued-fractions.md): convergents are best approximations
of the second kind. Its statement quantifies over all integer numerators and
positive denominators below the next convergent's denominator.
