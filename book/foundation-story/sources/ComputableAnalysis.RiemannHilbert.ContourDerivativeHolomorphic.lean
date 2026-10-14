import ComputableAnalysis.RiemannHilbert.ContourConstructedTaylor
import ComputableAnalysis.RiemannHilbert.GeneralSeriesDerivativeSeries
import ComputableAnalysis.RiemannHilbert.DomainHolomorphicLocality

/-! Holomorphy of the actual derivative of every supplied holomorphic map.
The proof constructs derivative series locally from actual Cauchy moments,
proves agreement by derivative uniqueness, and glues their actual witnesses. -/
namespace ComputableAnalysis.RiemannHilbert.RectangularContour
open ComplexRaw FunctionTheory DomainFunctions
set_option autoImplicit false

theorem localCauchyTaylor_derivative_agrees (f : DomainFunctions.Map) (hf : Holomorphic f) (b : Scalar) (hb : f.domain b)
    (z : Scalar) (hz : (localCauchyTaylor f hf b hb).domain z) (hza : f.domain z) :
    (localCauchyTaylor_holomorphic f hf b hb).derivative z hz≈hf.derivative z hza := by
  let hs := localCauchyTaylor_holomorphic f hf b hb
  let ht := hf.transfer (localCauchyTaylor f hf b hb) (localCauchyTaylor_domain f hf b hb) hs.openDomain
    (fun w hw => equiv_symm (localCauchyTaylor_agrees f hf b hb w hw (localCauchyTaylor_domain f hf b hb w hw)))
  exact hs.derivative_unique ht z hz

def localCauchyDerivativeRadius (f : DomainFunctions.Map) (hf : Holomorphic f) (b : Scalar) (hb : f.domain b) : QPos :=
  divideRadius (localCauchyTaylorRadius f hf b hb) ⟨2,by decide +kernel⟩

theorem localCauchyDerivativeRadius_identity (f : DomainFunctions.Map) (hf : Holomorphic f) (b : Scalar) (hb : f.domain b) :
    2*(localCauchyDerivativeRadius f hf b hb).val=(localCauchyTaylorRadius f hf b hb).val :=
  divideRadius_identity (localCauchyTaylorRadius f hf b hb) (⟨2,by decide +kernel⟩ : QPos)

theorem localCauchyDerivative_series_budget (f : DomainFunctions.Map) (hf : Holomorphic f) (b : Scalar) (hb : f.domain b) :
    8*(2*(localCauchyCoefficientRate f hf b hb).val)*(localCauchyDerivativeRadius f hf b hb).val≤(1:Rat)/2 := by
  have hs := localCauchyTaylor_series_budget f hf b hb
  have hr := localCauchyDerivativeRadius_identity f hf b hb
  rw [show 8*(2*(localCauchyCoefficientRate f hf b hb).val)*(localCauchyDerivativeRadius f hf b hb).val=
    8*(localCauchyCoefficientRate f hf b hb).val*(2*(localCauchyDerivativeRadius f hf b hb).val) by grind only,hr]
  exact hs

def localCauchyDerivativeSeries (f : DomainFunctions.Map) (hf : Holomorphic f) (b : Scalar) (hb : f.domain b) : DomainFunctions.Map :=
  CenteredSeries.function b (BoundedSeries.derivativeCoefficients (localCauchyTaylorCoefficients f hf b hb))
    (BoundedSeries.derivativeCoefficients_valid _ (localCauchyTaylorCoefficients_valid f hf b hb))
    ((localCauchyCoefficientBound f b hb).val*(localCauchyCoefficientRate f hf b hb).val)
    (2*(localCauchyCoefficientRate f hf b hb).val) (localCauchyDerivativeRadius f hf b hb).val
    (Rat.le_of_lt (Rat.mul_pos (localCauchyCoefficientBound f b hb).property (localCauchyCoefficientRate f hf b hb).property))
    (Rat.le_of_lt (Rat.mul_pos (by decide +kernel) (localCauchyCoefficientRate f hf b hb).property))
    (Rat.le_of_lt (localCauchyDerivativeRadius f hf b hb).property)
    (BoundedSeries.derivativeCoefficients_majorant _ (localCauchyTaylorCoefficients_valid f hf b hb)
      _ _ (Rat.le_of_lt (localCauchyCoefficientBound f b hb).property) (Rat.le_of_lt (localCauchyCoefficientRate f hf b hb).property)
      (localCauchyMoment_majorant f hf b hb)) (localCauchyDerivative_series_budget f hf b hb)

def localCauchyDerivativeSeries_holomorphic (f : DomainFunctions.Map) (hf : Holomorphic f) (b : Scalar) (hb : f.domain b) :
    Holomorphic (localCauchyDerivativeSeries f hf b hb) :=
  CenteredSeries.holomorphic b (BoundedSeries.derivativeCoefficients (localCauchyTaylorCoefficients f hf b hb))
    (BoundedSeries.derivativeCoefficients_valid _ (localCauchyTaylorCoefficients_valid f hf b hb))
    ((localCauchyCoefficientBound f b hb).val*(localCauchyCoefficientRate f hf b hb).val)
    (2*(localCauchyCoefficientRate f hf b hb).val) (localCauchyDerivativeRadius f hf b hb).val
    (Rat.le_of_lt (Rat.mul_pos (localCauchyCoefficientBound f b hb).property (localCauchyCoefficientRate f hf b hb).property))
    (Rat.le_of_lt (Rat.mul_pos (by decide +kernel) (localCauchyCoefficientRate f hf b hb).property))
    (Rat.le_of_lt (localCauchyDerivativeRadius f hf b hb).property)
    (BoundedSeries.derivativeCoefficients_majorant _ (localCauchyTaylorCoefficients_valid f hf b hb)
      _ _ (Rat.le_of_lt (localCauchyCoefficientBound f b hb).property) (Rat.le_of_lt (localCauchyCoefficientRate f hf b hb).property)
      (localCauchyMoment_majorant f hf b hb)) (localCauchyDerivative_series_budget f hf b hb)

theorem localCauchyDerivativeSeries_include (f : DomainFunctions.Map) (hf : Holomorphic f) (b : Scalar) (hb : f.domain b)
    (z : Scalar) (hz : (localCauchyDerivativeSeries f hf b hb).domain z) : (localCauchyTaylor f hf b hb).domain z := by
  obtain ⟨r,hr,hrS,hsmall⟩ := hz
  have hR := localCauchyDerivativeRadius_identity f hf b hb
  have hp := (localCauchyDerivativeRadius f hf b hb).property
  exact ⟨r,hr,by grind only,hsmall⟩

theorem localCauchyDerivativeSeries_agrees (f : DomainFunctions.Map) (hf : Holomorphic f) (b : Scalar) (hb : f.domain b)
    (z : Scalar) (hz : (localCauchyDerivativeSeries f hf b hb).domain z) (hza : f.domain z) :
    (localCauchyDerivativeSeries f hf b hb).eval z hz≈hf.derivative z hza := by
  let hzT := localCauchyDerivativeSeries_include f hf b hb z hz
  have hR := localCauchyDerivativeRadius_identity f hf b hb
  have hq : 0≤(localCauchyCoefficientRate f hf b hb).val*(localCauchyTaylorRadius f hf b hb).val :=
    Rat.mul_nonneg (Rat.le_of_lt (localCauchyCoefficientRate f hf b hb).property) (Rat.le_of_lt (localCauchyTaylorRadius f hf b hb).property)
  have hqS : 0≤(localCauchyCoefficientRate f hf b hb).val*(localCauchyDerivativeRadius f hf b hb).val :=
    Rat.mul_nonneg (Rat.le_of_lt (localCauchyCoefficientRate f hf b hb).property) (Rat.le_of_lt (localCauchyDerivativeRadius f hf b hb).property)
  have hl := localCauchyTaylor_series_budget f hf b hb
  have hs := localCauchyDerivative_series_budget f hf b hb
  have he := BoundedSeries.derivativeCoefficients_sum (localCauchyTaylorCoefficients f hf b hb)
    (localCauchyTaylorCoefficients_valid f hf b hb) (Centered.offset b z).val (Centered.offset b z).property
    (localCauchyCoefficientBound f b hb).val (localCauchyCoefficientRate f hf b hb).val
    (localCauchyTaylorRadius f hf b hb).val (localCauchyDerivativeRadius f hf b hb).val
    (Rat.le_of_lt (localCauchyCoefficientBound f b hb).property) (Rat.le_of_lt (localCauchyCoefficientRate f hf b hb).property)
    (Rat.le_of_lt (localCauchyTaylorRadius f hf b hb).property) (Rat.le_of_lt (localCauchyDerivativeRadius f hf b hb).property)
    (localCauchyMoment_majorant f hf b hb) (LocalODE.interior_bound _ _ hzT) (LocalODE.interior_bound _ _ hz)
    (by grind only) (by grind only)
  exact Setoid.trans (b := (localCauchyTaylor_holomorphic f hf b hb).derivative z hzT) he
    (localCauchyTaylor_derivative_agrees f hf b hb z hzT hza)

theorem localCauchyDerivativeSeries_center (f : DomainFunctions.Map) (hf : Holomorphic f) (b : Scalar) (hb : f.domain b) :
    (localCauchyDerivativeSeries f hf b hb).domain b := by
  refine ⟨0,Rat.le_refl,(localCauchyDerivativeRadius f hf b hb).property,?_⟩
  exact Small.congr (ofQComplex_valid _) (Centered.offset b b).property
    (equiv_symm (add_neg_equiv b.val b.property)) (Small.zero Rat.le_refl)

end ComputableAnalysis.RiemannHilbert.RectangularContour

namespace ComputableAnalysis.RiemannHilbert.DomainFunctions
open ComplexRaw FunctionTheory RectangularContour
set_option autoImplicit false

/-- The actual derivative of an arbitrary supplied holomorphic map is holomorphic
on its entire original domain. Local series data are constructed internally. -/
def Holomorphic.derivative_holomorphic {f : Map} (hf : Holomorphic f) : Holomorphic (derivativeMap f hf) :=
  holomorphic_of_local (derivativeMap f hf) (localCauchyDerivativeSeries f hf)
    (localCauchyDerivativeSeries_holomorphic f hf) (localCauchyDerivativeSeries_center f hf)
    (fun b hb z hz => localCauchyTaylor_domain f hf b hb z (localCauchyDerivativeSeries_include f hf b hb z hz))
    (fun b hb z hz => localCauchyDerivativeSeries_agrees f hf b hb z hz _)

end ComputableAnalysis.RiemannHilbert.DomainFunctions
