# Geometric cosine FTC: two proofs

This earlier proof note is superseded by
[Two checked proofs of the geometric cosine integral](two-cosine-proofs.md).

The public statement now has two independently audited proofs:

```lean
ComputableAnalysis.CosineFTC.integral_cosPi_viaInequalities
ComputableAnalysis.CosineFTC.integral_cosPi_viaFTC
```

The direct proof no longer invokes the normalized derivative theorem.
The FTC proof first establishes geometric concavity and a valid
concavity-based secant derivative, then instantiates the general concave FTC.
Both prove the same `IntegralCosineStatement` for the same unchanged
fixed-schedule cosine-sum computation, with the required `1/pi` factor.
The original `integral_cosPi_equiv_sinPi_endpoints` name remains available.
