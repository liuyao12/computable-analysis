# Rational-circle rotation equation

`ComputableAnalysis/GeometricRotationODE.lean` is the exact finite hand-off
between the rational circle construction and the ODE/Euler route.  It imports
only project modules: rational arithmetic, the rational circle chart, and the
finite rotation/Peano--Baker algebra.

For a rational chart parameter `t`, it names

```text
P(t) = ((1 - t*t)/(1 + t*t), 2*t/(1 + t*t))
```

as `GeometricRotationODE.pointComplex t`.  The checked endpoint identities
are:

```lean
GeometricRotationODE.pointComplex_zero  -- P(0) = 1
GeometricRotationODE.pointComplex_one   -- P(1) = i
```

The exact rational velocity is already present in the circle module.  This
new module gives it the complex rotation form:

```lean
GeometricRotationODE.pointComplexDerivative_eq_angularVelocity_mul_point
```

which states

```text
P'(t) = (2 i / (1 + t*t)) * P(t).
```

The coefficient is not an arbitrary change of variables: it is exactly the
geometric sector-area speed certified by the arctangent construction:

```lean
GeometricRotationODE.angularVelocity_eq_imaginaryAxis_sectorAreaSpeed
GeometricRotationODE.pointComplexDerivative_eq_sectorAreaSpeed_rotation
```

Thus sector-area time has the constant rotation generator used by
`RotationPeanoBakerBridge.rotationCenter_eq_constantPeanoBakerPartial`.

## What this proves, and what it does not

All declarations above are identities of rational functions.  They prove no
limit statement and use no completed real or complex numbers.  In particular,
`pointComplexDerivative` is the exact rational derivative formula, not yet a
`FunctionRaw` derivative certificate.

The first finite-difference step is now checked with portable rational
denominator clearing:

```lean
GeometricRotationODE.pointRe_differenceQuotient
GeometricRotationODE.pointIm_differenceQuotient
```

They give the two coordinate secants exactly, for every nonzero rational
step.  Subtracting the named rational velocity is also checked:

```lean
GeometricRotationODE.pointRe_differenceQuotient_sub_derivative
GeometricRotationODE.pointIm_differenceQuotient_sub_derivative
```

Each error is literally a rational fraction with an explicit factor of the
step.  On the unit chart the remaining factors are now bounded directly:

```lean
GeometricRotationODE.pointRe_secant_error_le_twelve
GeometricRotationODE.pointIm_secant_error_le_twelve
```

Both estimates are `<= 12 * qabs h` whenever the two rational endpoints lie
in `[0,1]`.  They are now packaged as exact singleton-evaluator certificates:

```lean
GeometricRotationODE.pointRe_hasDerivativeOnUnit
GeometricRotationODE.pointIm_hasDerivativeOnUnit
```

At requested precision `n`, the explicit step budget is `1/(12*n)` (and
`1/12` at stage zero).  A complex/vector wrapper and sector-area
reparametrization are the next requirements for ODE uniqueness.

A complex/vector derivative wrapper and the sector-area reparametrization then
lead to Peano--Baker/Volterra uniqueness.  That comparison would identify the
geometric endpoint `P(1) = i` with the factorial rotation raw; only after it,
and a separately certified exponential/logarithm branch, can the project
state the Euler row as formally complete.

## Focused check

```bash
lake build ComputableAnalysis.GeometricRotationODE
```
