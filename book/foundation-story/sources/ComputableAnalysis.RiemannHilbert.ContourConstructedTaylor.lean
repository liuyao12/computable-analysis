import ComputableAnalysis.RiemannHilbert.ContourTaylorNeighborhood
import ComputableAnalysis.RiemannHilbert.CenteredSeriesEstimates

/-! Taylor reconstruction from the actual constructed Cauchy moments.
For every supplied holomorphic map and arbitrary represented base point,
its computed local series is proved equal to the original function. -/
namespace ComputableAnalysis.RiemannHilbert.RectangularContour
open ComplexRaw FunctionTheory DomainFunctions
set_option autoImplicit false

def localCauchyTaylorCoefficients (f : DomainFunctions.Map) (hf : Holomorphic f) (b : Scalar) (hb : f.domain b) : Nat → ComplexRaw :=
  fun k => (localCauchyMoment f hf b hb k).val

theorem localCauchyTaylorCoefficients_valid (f : DomainFunctions.Map) (hf : Holomorphic f) (b : Scalar) (hb : f.domain b) (k : Nat) :
    (localCauchyTaylorCoefficients f hf b hb k).Valid := (localCauchyMoment f hf b hb k).property

theorem localCauchyTaylor_series_budget (f : DomainFunctions.Map) (hf : Holomorphic f) (b : Scalar) (hb : f.domain b) :
    8*(localCauchyCoefficientRate f hf b hb).val*(localCauchyTaylorRadius f hf b hb).val≤(1:Rat)/2 := by
  rw [show 8*(localCauchyCoefficientRate f hf b hb).val*(localCauchyTaylorRadius f hf b hb).val=
      8*((localCauchyCoefficientRate f hf b hb).val*(localCauchyTaylorRadius f hf b hb).val) by grind only,
    localCauchyTaylorRadius_rate]
  decide +kernel

def localCauchyTaylor (f : DomainFunctions.Map) (hf : Holomorphic f) (b : Scalar) (hb : f.domain b) : DomainFunctions.Map :=
  CenteredSeries.function b (localCauchyTaylorCoefficients f hf b hb) (localCauchyTaylorCoefficients_valid f hf b hb)
    (localCauchyCoefficientBound f b hb).val (localCauchyCoefficientRate f hf b hb).val (localCauchyTaylorRadius f hf b hb).val
    (Rat.le_of_lt (localCauchyCoefficientBound f b hb).property) (Rat.le_of_lt (localCauchyCoefficientRate f hf b hb).property)
    (Rat.le_of_lt (localCauchyTaylorRadius f hf b hb).property) (localCauchyMoment_majorant f hf b hb)
    (localCauchyTaylor_series_budget f hf b hb)

def localCauchyTaylor_holomorphic (f : DomainFunctions.Map) (hf : Holomorphic f) (b : Scalar) (hb : f.domain b) :
    Holomorphic (localCauchyTaylor f hf b hb) :=
  CenteredSeries.holomorphic b (localCauchyTaylorCoefficients f hf b hb) (localCauchyTaylorCoefficients_valid f hf b hb)
    (localCauchyCoefficientBound f b hb).val (localCauchyCoefficientRate f hf b hb).val (localCauchyTaylorRadius f hf b hb).val
    (Rat.le_of_lt (localCauchyCoefficientBound f b hb).property) (Rat.le_of_lt (localCauchyCoefficientRate f hf b hb).property)
    (Rat.le_of_lt (localCauchyTaylorRadius f hf b hb).property) (localCauchyMoment_majorant f hf b hb)
    (localCauchyTaylor_series_budget f hf b hb)

theorem localCauchyTaylor_domain (f : DomainFunctions.Map) (hf : Holomorphic f) (b : Scalar) (hb : f.domain b)
    (z : Scalar) (hz : (localCauchyTaylor f hf b hb).domain z) : f.domain z :=
  localCauchyTaylorRadius_domain f hf b hb z (LocalODE.interior_bound _ _ hz)

theorem cauchyMomentPrefix_series_prefix (f : DomainFunctions.Map) (hf : Holomorphic f) (b : Scalar) (hb : f.domain b)
    (z : Scalar) (N : Nat) :
    cauchyMomentPrefix f hf b hb z N≈
      ⟨BoundedSeries.valueBlock (localCauchyTaylorCoefficients f hf b hb) (Centered.offset b z).val 0 N,
        BoundedSeries.valueBlock_valid _ _ (localCauchyTaylorCoefficients_valid f hf b hb) (Centered.offset b z).property 0 N⟩ := by
  induction N with
  | zero => exact equiv_refl _ (ofQComplex_valid _)
  | succ N ih =>
    apply add_equiv ih
    simp only [Nat.zero_add]
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := (scalarProduct (taylorDisplacementPower b z N) (localCauchyMoment f hf b hb N)).property)
      (hright := mul_valid (localCauchyTaylorCoefficients_valid f hf b hb N) (LocalODE.power_valid _ (Centered.offset b z).property N))
    change gridScalarValue (taylorDisplacementPower b z N)*gridScalarValue (localCauchyMoment f hf b hb N)=
      gridScalarValue (localCauchyMoment f hf b hb N)*gridScalarValue (taylorDisplacementPower b z N)
    exact ComplexRawQuotient.mul_comm _ _

theorem localCauchyTaylor_prefix_error (f : DomainFunctions.Map) (hf : Holomorphic f) (b : Scalar) (hb : f.domain b)
    (z : Scalar) (hz : (localCauchyTaylor f hf b hb).domain z) (N : Nat) :
    Small (sub ((localCauchyTaylor f hf b hb).eval z hz).val (cauchyMomentPrefix f hf b hb z N).val)
      (4*(localCauchyCoefficientBound f b hb).val*((1:Rat)/8)^N) := by
  let C := (localCauchyCoefficientBound f b hb).val
  let K := (localCauchyCoefficientRate f hf b hb).val
  let R := (localCauchyTaylorRadius f hf b hb).val
  have hsmall := LocalODE.interior_bound R (Centered.offset b z) hz
  have hrate := localCauchyTaylorRadius_rate f hf b hb
  have hbudget : 2*K*R≤(1:Rat)/2 := by have hs := localCauchyTaylor_series_budget f hf b hb; have hp := Rat.mul_nonneg (Rat.le_of_lt (localCauchyCoefficientRate f hf b hb).property) (Rat.le_of_lt (localCauchyTaylorRadius f hf b hb).property); dsimp [K,R]; grind only
  have hs := BoundedSeries.sumValue_close_prefix (localCauchyTaylorCoefficients f hf b hb) (Centered.offset b z).val
    (localCauchyTaylorCoefficients_valid f hf b hb) (Centered.offset b z).property C K R
    (Rat.le_of_lt (localCauchyCoefficientBound f b hb).property) (Rat.le_of_lt (localCauchyCoefficientRate f hf b hb).property)
    (Rat.le_of_lt (localCauchyTaylorRadius f hf b hb).property) (localCauchyMoment_majorant f hf b hb) hsmall hbudget N
  have hq : 2*K*R=(1:Rat)/8 := by dsimp [K,R]; grind only
  change Small _ (4*C*(2*K*R)^N) at hs
  rw [hq] at hs
  exact Small.congr
    (sub_valid ((localCauchyTaylor f hf b hb).eval z hz).property
      (BoundedSeries.valueBlock_valid _ _ (localCauchyTaylorCoefficients_valid f hf b hb) (Centered.offset b z).property 0 N))
    (sub_valid ((localCauchyTaylor f hf b hb).eval z hz).property (cauchyMomentPrefix f hf b hb z N).property)
    (FunctionTheory.sub_congr (equiv_refl _ ((localCauchyTaylor f hf b hb).eval z hz).property)
      (equiv_symm (cauchyMomentPrefix_series_prefix f hf b hb z N))) hs

theorem localCauchyTaylor_prefix_converges (f : DomainFunctions.Map) (hf : Holomorphic f) (b : Scalar) (hb : f.domain b)
    (z : Scalar) (hz : (localCauchyTaylor f hf b hb).domain z) :
    Converges (cauchyMomentPrefix f hf b hb z) ((localCauchyTaylor f hf b hb).eval z hz) := by
  have he := LocalODE.tail_bound_shrinks (localCauchyCoefficientBound f b hb).val ((1:Rat)/8)
    (Rat.le_of_lt (localCauchyCoefficientBound f b hb).property) (by decide +kernel) (by decide +kernel)
  intro eps
  obtain ⟨N,hN⟩ := he eps
  exact ⟨N,fun n hn => (RepresentedCauchySum.small_sub_symm _ _ _ (localCauchyTaylor_prefix_error f hf b hb z hz n)).mono (hN n hn)⟩

/-- Exact reconstruction, for every valid represented point in the computed neighborhood. -/
theorem localCauchyTaylor_agrees (f : DomainFunctions.Map) (hf : Holomorphic f) (b : Scalar) (hb : f.domain b)
    (z : Scalar) (hz : (localCauchyTaylor f hf b hb).domain z) (hza : f.domain z) :
    (localCauchyTaylor f hf b hb).eval z hz≈f.eval z hza :=
  converge_unique (cauchyMomentPrefix f hf b hb z) _ _ (localCauchyTaylor_prefix_converges f hf b hb z hz)
    (localCauchyMomentPrefix_converges f hf b hb z (LocalODE.interior_bound _ _ hz) hza)

/-- The exact reconstructed value is independent of the local holomorphy witness and represented names. -/
theorem localCauchyTaylor_value_congr (f : DomainFunctions.Map) (hf hg : Holomorphic f) (b c : Scalar)
    (hb : f.domain b) (hc : f.domain c) (z w : Scalar)
    (hz : (localCauchyTaylor f hf b hb).domain z) (hw : (localCauchyTaylor f hg c hc).domain w) (he : z≈w) :
    (localCauchyTaylor f hf b hb).eval z hz≈(localCauchyTaylor f hg c hc).eval w hw := by
  let hza := localCauchyTaylor_domain f hf b hb z hz
  let hwa := localCauchyTaylor_domain f hg c hc w hw
  exact Setoid.trans (localCauchyTaylor_agrees f hf b hb z hz hza)
    (Setoid.trans (f.eval_congr z w hza hwa he) (equiv_symm (localCauchyTaylor_agrees f hg c hc w hw hwa)))

end ComputableAnalysis.RiemannHilbert.RectangularContour
