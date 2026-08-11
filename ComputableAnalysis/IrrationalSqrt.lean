import ComputableAnalysis.Algebraic

/-!
# Irrationality criterion for rational square roots

This is the public comparison surface for rational square roots.  It packages
the executable square-root certificate internally, so downstream projects can
compare this statement with other analytic foundations without retracing a
special corollary such as `√2`.
-/

namespace ComputableAnalysis

/-- For a nonnegative rational input, the computable real square root is
irrational precisely when the input is not a rational square. -/
theorem irrational_sqrt_rat_iff_not_square
    (q : Rat) (hq : sqrtDomain q) :
    Real.Irrational (sqrtReal q hq (sqrtRaw_spec q hq).1) ↔ Rat.NotSquare q := by
  exact sqrt_irrational_iff_not_square q hq (sqrtRaw_spec q hq)

end ComputableAnalysis
