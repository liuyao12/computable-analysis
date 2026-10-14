import ComputableAnalysis.RiemannHilbert.CenteredIteratedSeries
import ComputableAnalysis.RiemannHilbert.IteratedDerivativeOverlap

/-! The constructed contour moments are the factorial-normalized actual
derivatives, at every finite order and every supplied represented point.
The estimates and shrinking series neighborhoods are internal proof data. -/
namespace ComputableAnalysis.RiemannHilbert.RectangularContour
open ComplexRaw FunctionTheory DomainFunctions RadialLogarithmChains
set_option autoImplicit false

/-- The actual higher derivative equals the factorial-scaled constructed moment. -/
theorem localCauchyMoment_derivative_formula (f : DomainFunctions.Map) (hf : Holomorphic f)
    (b : Scalar) (hb : f.domain b) (n : Nat) :
    (iteratedDerivativeMap f hf n).eval b ((iteratedDerivative_domain f hf n b).2 hb)≈
      scale (factorialRat n) (localCauchyMoment f hf b hb n) := by
  exact CenteredSeries.profile_factorial_derivative b (localCauchyTaylorCoefficients f hf b hb)
    (localCauchyTaylorCoefficients_valid f hf b hb)
    (localCauchyCoefficientBound f b hb).val (localCauchyCoefficientRate f hf b hb).val
    (localCauchyTaylorRadius f hf b hb)
    (Rat.le_of_lt (localCauchyCoefficientBound f b hb).property)
    (Rat.le_of_lt (localCauchyCoefficientRate f hf b hb).property)
    (localCauchyMoment_majorant f hf b hb) (localCauchyTaylor_series_budget f hf b hb) f hf
    (localCauchyTaylor_domain f hf b hb)
    (fun z hz => localCauchyTaylor_agrees f hf b hb z hz (localCauchyTaylor_domain f hf b hb z hz)) n hb

/-- Exact normalization, without a caller-chosen series radius or precision schedule. -/
theorem localCauchyMoment_higher_derivative (f : DomainFunctions.Map) (hf : Holomorphic f)
    (b : Scalar) (hb : f.domain b) (n : Nat) :
    localCauchyMoment f hf b hb n≈scale (factorialRat n)⁻¹
      ((iteratedDerivativeMap f hf n).eval b ((iteratedDerivative_domain f hf n b).2 hb)) := by
  exact Setoid.trans (equiv_symm (RationalDilation.undo (factorialRat n)
    (RationalMajorant.factorialRat_pos n) (localCauchyMoment f hf b hb n)))
    (scaleRat_equiv (equiv_symm (localCauchyMoment_derivative_formula f hf b hb n)))

theorem localCauchyHigherDerivative_bound (f : DomainFunctions.Map) (hf : Holomorphic f)
    (b : Scalar) (hb : f.domain b) (n : Nat) :
    Small ((iteratedDerivativeMap f hf n).eval b ((iteratedDerivative_domain f hf n b).2 hb)).val
      (factorialRat n*((localCauchyCoefficientBound f b hb).val*(localCauchyCoefficientRate f hf b hb).val^n)) :=
  Small.congr (scaleRat_valid (localCauchyMoment f hf b hb n).property)
    ((iteratedDerivativeMap f hf n).eval b ((iteratedDerivative_domain f hf n b).2 hb)).property
    (equiv_symm (localCauchyMoment_derivative_formula f hf b hb n))
    (LocalODE.small_scale (Rat.le_of_lt (RationalMajorant.factorialRat_pos n))
      (localCauchyMoment_majorant f hf b hb n))

/-- Any enclosing certified rectangle computes the normalized higher derivative. -/
theorem normalizedFixedRectangleMomentContour_higher_derivative (f : DomainFunctions.Map) (hf : Holomorphic f)
    (J : QInterval × QInterval) (hJ : ∀ z, representedRectangleContains J z → f.domain z)
    (b : Scalar) (hb : RectanglePoleInterior J b) (ha : f.domain b) (n : Nat) :
    Converges (normalizedFixedRectangleMomentContour f J hJ b hb n)
      (scale (factorialRat n)⁻¹ ((iteratedDerivativeMap f hf n).eval b ((iteratedDerivative_domain f hf n b).2 ha))) := by
  exact converge_limit_congr _ _ _ (normalizedFixedRectangleMomentContour_converges f hf J hJ b hb ha n)
    (localCauchyMoment_higher_derivative f hf b ha n)

end ComputableAnalysis.RiemannHilbert.RectangularContour
