# Chapter 1. Computable numbers and functions

## Real names and real numbers

**Definition.** A real name is a sequence of rational intervals

$$
n\longmapsto [a_n,b_n],\qquad a_n,b_n\in\mathbb Q.
$$

It is **valid** if the intervals are nonempty and nested, and \(b_n-a_n\to0\). The stage \(n\) has no prescribed rate of refinement. In Lean, the data are a `RealCompute` and the three conditions are `RealCompute.Valid`. We call a name computable when an algorithm gives its intervals.

**Definition.** Two valid names are equivalent if their intervals overlap at every stage. A real number is an equivalence class of valid names. A rational \(r\) has the constant name \([r,r]\).

## Arithmetic and order

For \(I=[a,b]\) and \(J=[c,d]\), set

$$
I+J=[a+c,b+d],\qquad -I=[-b,-a].
$$

For the product take the minimum and maximum of \(ac,ad,bc,bd\). On a bracket separated from zero, the reciprocal interval is \([1/b,1/a]\). To invert a nonzero real, start at a stage whose interval is separated from zero.

**Definition.** \(x<y\) if, at some stage, the upper endpoint of the name for \(x\) is strictly below the lower endpoint of the name for \(y\). These operations and this order respect equivalence. The quotient is `ComputableAnalysis.Real`.

## Kinds of computation

The same number can be given by several formulas. Here is a list of the constructions we will use, with \(\pi\) as a running example.

- **Geometric bounds.** \(\pi=\operatorname{area}\{(x,y):x^2+y^2\le1\}\). Inscribed and circumscribed rational polygons give finite area bounds.
- **Series.** \(\displaystyle \frac{\pi}{4}=\sum_{k=0}^{\infty}\frac{(-1)^k}{2k+1}\). An alternating remainder bounds the error of each prefix.
- **Products.** \(\displaystyle \frac{\pi}{2}=\prod_{k=1}^{\infty}\frac{(2k)^2}{(2k-1)(2k+1)}\). This is Wallis's product.
- **Continued fractions.** \(\displaystyle \frac4\pi=1+\cfrac{1^2}{2+\cfrac{3^2}{2+\cfrac{5^2}{2+\cdots}}}\). Brouncker's fraction gives rational convergents.
- **Definite integrals.** \(\displaystyle \frac{\pi}{4}=\int_0^1\frac{dx}{1+x^2}\). Upper and lower dyadic sums enclose the value.
- **Complex functions.** \(\displaystyle \frac{\pi}{2}=\operatorname{Im}\operatorname{Log}(i)\), with the principal logarithm. The imaginary part recovers the angle.

Two formulas for \(\pi\) can call for different error estimates. Proving their equivalence lets us use either computation for the same value.

## Complex numbers

A complex name gives a rational box at every stage. Equivalently it gives two real names, one for each coordinate of $z=x+iy$. Lean calls these names `ComplexCompute` and their quotient `ComputableAnalysis.Complex`.

## Functions and inverses

Numbers lead to functions. In the square-root example from the preface, the target $2$ can be replaced by a rational $q\ge0$. The construction then gives a rule on rational inputs with values that are real names. Complex rules begin on rational complex inputs or on a stated rational chart.

If a rational rule $f$ is increasing on an interval and the brackets $[a_n,b_n]$ eventually lie there, use lower bounds for $f(a_n)$ and upper bounds for $f(b_n)$. For a decreasing rule, swap the roles of the endpoints. Choose the evaluation stages so that these output bounds shrink, and prove that equivalent input names give equivalent outputs. This is the interval construction of continuity. On monotonicity intervals, polynomials and rational functions provide examples, with the denominator kept away from zero.

For a strictly increasing continuous rule, a target strictly between two values can be enclosed in the image of increasingly short rational brackets. Search for endpoints with strict inequalities on either side of the target. The resulting name computes the inverse without deciding whether two real names are equal.

The [value-predicate note](01c-real-classification-api.md) covers rationality and algebraicity. The [continued-fractions chapter](06b-continued-fractions.md) gives another way to read an interval computation.
