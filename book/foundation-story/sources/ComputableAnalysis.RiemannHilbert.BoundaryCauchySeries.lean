import ComputableAnalysis.RiemannHilbert.BoundaryCauchyNear
import ComputableAnalysis.RiemannHilbert.CenteredSeriesEstimates

/-! An actual holomorphic series built from constructed boundary-only Cauchy
moments. Its geometric majorant and rational radius are derived from genuine
edge data, without a source value at the center or an assumed projection. -/
namespace ComputableAnalysis.RiemannHilbert.BoundaryCauchySeries
open ComplexRaw FunctionTheory DomainFunctions RectangularContour BoundaryCauchyPowers
set_option autoImplicit false
variable (d : Data)

def coefficients (k : Nat) : ComplexRaw := (moment d k).val
theorem coefficients_valid (k : Nat) : (coefficients d k).Valid := (moment d k).property

theorem budget : 8*(rate d).val*(BoundaryCauchyNear.radius d).val≤(1:Rat)/2 := by
  calc
    8*(rate d).val*(BoundaryCauchyNear.radius d).val=8*((rate d).val*(BoundaryCauchyNear.radius d).val) := by grind only
    _=8*((1:Rat)/16) := by rw [BoundaryCauchyNear.radius_rate]
    _≤(1:Rat)/2 := by decide +kernel

def function : DomainFunctions.Map := CenteredSeries.function d.center (coefficients d) (coefficients_valid d)
  (bound d).val (rate d).val (BoundaryCauchyNear.radius d).val (Rat.le_of_lt (bound d).property)
  (Rat.le_of_lt (rate d).property) (Rat.le_of_lt (BoundaryCauchyNear.radius d).property) (moment_bound d) (budget d)

def holomorphic : Holomorphic (function d) := CenteredSeries.holomorphic d.center (coefficients d) (coefficients_valid d)
  (bound d).val (rate d).val (BoundaryCauchyNear.radius d).val (Rat.le_of_lt (bound d).property)
  (Rat.le_of_lt (rate d).property) (Rat.le_of_lt (BoundaryCauchyNear.radius d).property) (moment_bound d) (budget d)

theorem center_mem : (function d).domain d.center := Centered.center_mem _ _

def finiteSum (z : Scalar) (N : Nat) : Scalar :=
  gridScalarSum N (fun k => scalarProduct (taylorDisplacementPower d.center z k) (moment d k))

theorem finiteSum_series (z : Scalar) (N : Nat) : finiteSum d z N≈
    ⟨BoundedSeries.valueBlock (coefficients d) (Centered.offset d.center z).val 0 N,
      BoundedSeries.valueBlock_valid _ _ (coefficients_valid d) (Centered.offset d.center z).property 0 N⟩ := by
  induction N with
  | zero => exact equiv_refl _ (ofQComplex_valid _)
  | succ N ih =>
    apply add_equiv ih
    simp only [Nat.zero_add]
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
    change gridScalarValue (taylorDisplacementPower d.center z N)*gridScalarValue (moment d N)=
      gridScalarValue (moment d N)*gridScalarValue (taylorDisplacementPower d.center z N)
    exact ComplexRawQuotient.mul_comm _ _

theorem prefix_error (z : Scalar) (hz : (function d).domain z) (N : Nat) :
    Small (sub ((function d).eval z hz).val (finiteSum d z N).val) (4*(bound d).val*((1:Rat)/8)^N) := by
  have hrate := BoundaryCauchyNear.radius_rate d
  have hlocal := budget d
  have hp := Rat.mul_nonneg (Rat.le_of_lt (rate d).property) (Rat.le_of_lt (BoundaryCauchyNear.radius d).property)
  have hb : 2*(rate d).val*(BoundaryCauchyNear.radius d).val≤(1:Rat)/2 := by grind only
  have hs := BoundedSeries.sumValue_close_prefix (coefficients d) (Centered.offset d.center z).val
    (coefficients_valid d) (Centered.offset d.center z).property (bound d).val (rate d).val (BoundaryCauchyNear.radius d).val
    (Rat.le_of_lt (bound d).property) (Rat.le_of_lt (rate d).property) (Rat.le_of_lt (BoundaryCauchyNear.radius d).property)
    (moment_bound d) (LocalODE.interior_bound _ _ hz) hb N
  have he : 2*(rate d).val*(BoundaryCauchyNear.radius d).val=(1:Rat)/8 := by
    calc
      _=2*((rate d).val*(BoundaryCauchyNear.radius d).val) := by grind only
      _=2*((1:Rat)/16) := by rw [hrate]
      _=(1:Rat)/8 := by decide +kernel
  change Small _ (4*(bound d).val*(2*(rate d).val*(BoundaryCauchyNear.radius d).val)^N) at hs
  rw [he] at hs
  exact Small.congr
    (sub_valid ((function d).eval z hz).property
      (BoundedSeries.valueBlock_valid _ _ (coefficients_valid d) (Centered.offset d.center z).property 0 N))
    (sub_valid ((function d).eval z hz).property (finiteSum d z N).property)
    (FunctionTheory.sub_congr (equiv_refl _ ((function d).eval z hz).property) (equiv_symm (finiteSum_series d z N))) hs

theorem finiteSum_converges (z : Scalar) (hz : (function d).domain z) :
    Converges (finiteSum d z) ((function d).eval z hz) := by
  have he := LocalODE.tail_bound_shrinks (bound d).val ((1:Rat)/8)
    (Rat.le_of_lt (bound d).property) (by decide +kernel) (by decide +kernel)
  intro eps
  obtain ⟨N,hN⟩ := he eps
  exact ⟨N,fun n hn => (RepresentedCauchySum.small_sub_symm _ _ _ (prefix_error d z hz n)).mono (hN n hn)⟩

end ComputableAnalysis.RiemannHilbert.BoundaryCauchySeries
