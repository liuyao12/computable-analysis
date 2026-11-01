# Chapter 4. Infinite series with certified errors

## The error belongs to the construction

An infinite series is evaluated through its finite sums together with a
proved bound on the omitted tail. For rational terms, write

$$
S_N=\sum_{k=0}^{N-1}u_k.
$$

Supply nonnegative rational errors with the finite-tail property

$$
|S_M-S_N|\le e_N\quad(M\ge N),\qquad e_N\longrightarrow0.
$$

The error is part of the data defining the represented sum. The finite-tail
property is a theorem about arbitrary later finite sums. It does not assume
that an infinite sum already exists. Signs and absolute convergence need not
be built into the general definition; particular constructions supply the
tail estimate they can prove.

At each stage form the error box, then intersect its finite prefix:

$$
J_N=[S_N-e_N,S_N+e_N],\qquad
I_N=\bigcap_{j=0}^{N}J_j.
$$

Every later finite sum belongs to every earlier box. Consequently each finite
intersection is nonempty. The intersections are nested, and their widths
are at most twice the current error, so they define a valid represented real.
No abstract completion, supremum, or independently assumed sum is needed.
Literal error boxes need not themselves be nested.

`ErrorSeries.Series` implements rational terms with these actual finite sums
and certified errors. `Series.sum` is the resulting `RealRaw` computation;
`Series.sum_valid` and `Series.sum_bounds` prove validity and the value bounds.
The lower-level `ErrorSeries.Data` accepts rational approximants more generally.
When approximants include rounding or represented-coefficient evaluation,
their certified error must account for those contributions as well as the tail.
Calling an arbitrary approximant stream a series still requires a bridge to
the advertised finite sums.

## Equality is stronger than computing digits

An independently constructed value is equal to this sum if it obeys the same
shrinking prefix bounds:

$$
S_N-e_N\le v\le S_N+e_N\quad\text{for every }N.
$$

`ErrorSeries.Data.identify` derives exact `RealRaw.Equiv` from these finite
inequalities. `Data.compare` compares two justified constructions through
a common valid value. These are comparison laws, not definitions that store
the desired equality in a record.

For a named function, there are two separate tasks: construct a valid series
sum, then prove that the function has the required finite-prefix remainder.
The second task is what makes its series expansion a theorem about that
function. Agreement of coefficient recurrences or many computed digits does
not replace it.

## Represented terms and evaluation errors

For represented terms, a finite prefix also needs finite evaluator accuracy.
One may choose rational approximants to those prefixes with a proved combined
budget. The required error has the shape

$$
e_N\ge e_N^{\mathrm{tail}}+e_N^{\mathrm{evaluation}}.
$$

Both contributions must shrink under the actual selected schedule. General
linear, rearrangement, and termwise-operation theorems need their appropriate
tail evidence; they are not licensed by notation alone. `RepresentedSeries.finiteSum` now forms finite sums of represented terms.
`RepresentedSeries.HasSum` specifies their convergence to a valid represented
value and has a proved uniqueness law. For a supplied represented value, proved shrinking finite-prefix errors
justify the interval constructor `RepresentedSeries.sum`; width searches and
finite prefix intersections are internal. `sum_valid` and `sum_identify`
prove its validity and exact value at that stated scope. The geometric Taylor
derivation in Chapter 6 supplies the value and proves those finite errors by
repeated FTC. The rational constructor above remains useful for rational
terms and their function-specific tails.

Power series next specialize the finite sums and organize uniform tail
estimates. Taylor's theorem follows only after that discussion.
