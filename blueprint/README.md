# Computable Analysis: mathematical blueprint

This directory contains the informal mathematical manuscript. Its definitions,
algorithms, estimates, and proofs are meant to be read without Lean declarations
or implementation notes. The existing formal sources elsewhere in the repository
are separate; statements in this manuscript are not labels of formalization status.

## Reading order

`src/content.tex` determines the order; historical filename numbers do not.
The sequence is interval foundations; circle and sphere geometry; trigonometry;
integrals and the convex FTC; series, exponential/logarithm, and algebraic
branches; local calculations and nonlinear constructions; complex paths;
improper parameter integrals and gamma; Fourier; explicit impulses; linear
ODEs; Bessel and hypergeometric constructions; transforms and zeta; and an
elliptic-integral synthesis.

The organizing principle is a specific computation with the estimates needed
for its operations, not a general space of all continuous, smooth, holomorphic,
or square-integrable functions. In particular, recentering does not by itself
extend a domain, a value algorithm does not automatically compute derivatives,
and a finite asymptotic remainder is not a convergent-series tail.

## Build

From the repository root, with the system TeX and Graphviz dependencies installed:

```bash
python -m pip install -r blueprint/requirements.txt
leanblueprint pdf
leanblueprint web
```

The print and web entry points are `src/print.tex` and `src/web.tex`. Both include
`src/content.tex`. These manuscript builds do not require a Lean build or a
declaration check. The Pages workflow builds the web edition from these sources.

## Finite mathematical checks

```bash
python blueprint/checks/check_special_function_identities.py
```

The check uses only Python's standard library and exact rational arithmetic.
It exercises recentering, special-function recurrences, Bessel sign and zero
bounds, Bernoulli polynomials, finite Euler--Maclaurin identities, and selected
continued zeta values. These finite checks supplement, not replace, the proofs
and error estimates in the text. See `checks/README.md`.

## Illustrations

Existing geometry and finite-stage illustrations are retained. The web edition
may use a looping GIF and the print edition a static frame. Each picture belongs
beside the finite construction it depicts; its mathematical claims come from
the accompanying proof, not from visual agreement or implementation status.
Rational state, appropriate domain labels, and equal geometric unit scales
should remain visible. A diagram should explain a construction, not stand in
for its convergence argument.
