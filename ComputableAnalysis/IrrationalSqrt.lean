import ComputableAnalysis.Algebraic

/-!
# Irrationality criterion for rational square roots

This is the public comparison surface for rational square roots.  It packages
the executable square-root certificate internally, so downstream projects can
compare this statement with other analytic foundations without retracing a
special corollary such as `√2`.
-/

namespace ComputableAnalysis

/-- The canonical computable square root of a nonnegative rational.

The proof argument records the domain certificate needed by the executable
interval algorithm; it is not a coercion into Mathlib's completed real line.
-/
def sqrtRat (q : Rat) (hq : 0 <= q) : RealRaw :=
  let hdom : sqrtDomain q := by
    unfold sqrtDomain
    exact (Rat.not_lt).2 hq
  sqrtRaw q hdom

/-- A rational square root is irrational exactly when its rational input is
not a rational square.  This is the project-facing, real-free analogue of
Mathlib's `irrational_sqrt_ratCast_iff_of_nonneg`.
-/
theorem irrational_sqrt_ratCast_iff_of_nonneg {q : Rat} (hq : 0 <= q) :
    RealRaw.Irrational (sqrtRat q hq) ↔ ¬ Rat.IsSquare q := by
  let hdom : sqrtDomain q := by
    unfold sqrtDomain
    exact (Rat.not_lt).2 hq
  simpa [sqrtRat, sqrtReal, Real.Irrational, Real.Equiv, Real.ofRaw,
    Real.ofRat, RealRaw.ofRat, RealRaw.Irrational, Rat.NotSquare] using
    (sqrt_irrational_iff_not_square q hdom (sqrtRaw_spec q hdom))

/-- For a nonnegative rational input, the computable real square root is
irrational precisely when the input is not a rational square. -/
theorem irrational_sqrt_rat_iff_not_square
    (q : Rat) (hq : sqrtDomain q) :
    RealRaw.Irrational (sqrtRaw q hq) ↔ Rat.NotSquare q := by
  simpa [sqrtReal, Real.Irrational, Real.Equiv, Real.ofRaw, Real.ofRat,
    RealRaw.ofRat, RealRaw.Irrational, Rat.NotSquare] using
    (sqrt_irrational_iff_not_square q hq (sqrtRaw_spec q hq))

end ComputableAnalysis
