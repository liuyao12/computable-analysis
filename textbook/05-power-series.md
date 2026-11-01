# Chapter 5. Power series and uniform tail bounds

## Coefficients, finite polynomials, and convergence

A coefficient stream first gives finite polynomials:

$$
P_N(x)=\sum_{k=0}^{N-1}a_kx^k.
$$

A formal coefficient recurrence does not establish that these polynomials
converge, that their limit has an advertised derivative, or that it equals an
independently defined function. To evaluate a power series, supply tail bounds
on the intended input region and compile them through Chapter 4's construction.
Uniform bounds on a bounded input region also support represented-input
evaluation, once the finite polynomial evaluation error is accounted for.

## A factorial majorant

The checked `ErrorPowerSeries.factorialData` construction applies when the
rational terms satisfy

$$
|u_k|\le A_k,\qquad A_k=\frac{C^k}{k!},\qquad C\ge0.
$$

Choose an explicit starting index beyond which consecutive majorant terms
contract by at least a factor of one half:

$$
C\le\frac{N_0+1}{2},\qquad
A_{k+1}=A_k\frac{C}{k+1}\le\frac{A_k}{2}\quad(k\ge N_0).
$$

Finite geometric summation then bounds every finite tail:

$$
\left|\sum_{k=N}^{M-1}u_k\right|\le2A_N
\quad(M\ge N\ge N_0).
$$

The actual error in the represented computation is twice the first omitted
factorial majorant. The construction proves that it shrinks, using the
explicit geometric decay after the starting index. The precision stage and
the truncation degree are different indices; the former selects a justified
degree internally.

`factorialSum_valid` proves validity. `factorialSum_identify` turns an
independently proved finite remainder for a supplied function value into exact
equality with this represented sum. The function value need not be rational.

## Applying the majorant to power series

For rational coefficients and input, a bound of the form

$$
|a_n|\le\frac1{n!}
$$

gives the termwise estimate

$$
|a_nx^n|\le\frac{|x|^n}{n!}.
$$

The preceding constructor then supplies finite tail bounds and a represented
sum. A coefficient bound is convergence data. The mathematical role of any
particular function still comes from its own construction and laws.

For represented coefficients or inputs, finite polynomial evaluation has
its own error. Include it together with the omitted-tail bound. This matters
when coefficients or arguments involve the geometric circle constant.
`RepresentedSeries` supplies the represented-term convergence specification
and the finite-error sum construction used in Chapter 6.

We derive the trigonometric coefficients in that chapter by repeatedly
applying FTC to geometric sine and cosine. The successive initial values and
monomial integrations produce the coefficients; the iterated-integral
remainder supplies the convergence proof.

## Before differentiating or integrating a series

First prove finite polynomial identities. Then bound the actual omitted tails
for the operation being claimed. A derivative series needs control of the
quotient remainder, and an integral comparison needs whole-interval bounds.
Pointwise convergence alone is insufficient for either operation.

The next chapter uses finite FTC identities and a remainder estimate to
identify the geometric functions with their power series. It does not define
the geometric functions anew by those series.
