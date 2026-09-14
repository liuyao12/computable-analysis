import ComputableAnalysis.GeometricSineConcavity
import ComputableAnalysis.ConcaveFTCIntegral

/-!
# The second proof of the same cosine integral proposition

This file never imports CosineFTC (the direct proof). It applies the generic
concave FTC to sine/pi and the original cosine, using the already constructed
concavity and secant-derivative data. The integral algorithm and target
proposition are the same proof-independent definitions as in the direct route.
-/
namespace ComputableAnalysis
namespace CosineFTC
open IntegralIdentities SinPiIntegral GeometricSineDerivative
open GeometricSineConcavity IntervalSelections FiniteRiemannAlgebra

private theorem concave_error_budget (B : ArctanInverseBisection)
    {a b : Rat} (hab : a <= b) (k : Nat) :
    ((k+1 : Nat) : Rat)*((primitiveDerivativeData B).K : Rat)*
      mesh a b (k+1)*mesh a b (k+1) <= error a b k := by
  rw [error_eq_mesh]
  change ((k+1 : Nat) : Rat)*32*mesh a b (k+1)*mesh a b (k+1) <=
    ((k+1 : Nat) : Rat)*(4000*mesh a b (k+1)*mesh a b (k+1))
  have hh := mesh_nonneg_of_le (Nat.succ_pos k) hab
  have hm0 : 0 <= ((k+1 : Nat) : Rat) := Rat.le_of_lt ((Rat.natCast_pos).2 (Nat.succ_pos k))
  have hw0 := Rat.mul_nonneg (Rat.mul_nonneg hm0 hh) hh
  have hb := Rat.mul_le_mul_of_nonneg_right (by decide : (32 : Rat) <= 4000) hw0
  grind

/-- Finite distributivity between the independently evaluated endpoint
programs. At each stage one common rational selection lies in both boxes. -/
theorem primitive_difference_equiv_endpoint (B : ArctanInverseBisection) (a b : Rat) :
    (ConcaveFTC.endpointDifference (primitiveFun B) a b).Equiv (endpoint B a b) := by
  intro n
  let r := (reciprocalPiRaw.compute n).hi
  let sa := sineSample B a n
  let sb := sineSample B b n
  have hr : InBox r (reciprocalPiRaw.compute n) :=
    ⟨RealRaw.interval_order_of_valid _ reciprocalPiRaw_valid n, Rat.le_refl⟩
  have hsa := sineSample_mem B a n
  have hsb := sineSample_mem B b n
  have haP : InBox (r*sa) ((primitive B a).compute n) := mul_mem hr hsa
  have hbP : InBox (r*sb) ((primitive B b).compute n) := mul_mem hr hsb
  have hleft : InBox (r*sb-r*sa) ((ConcaveFTC.endpointDifference (primitiveFun B) a b).compute n) :=
    sub_mem hbP haP
  have hs : InBox (sb-sa) ((sine B b-sine B a).compute n) := sub_mem hsb hsa
  have hright : InBox (r*(sb-sa)) ((endpoint B a b).compute n) := mul_mem hr hs
  have he : r*(sb-sa) = r*sb-r*sa := by grind
  rw [he] at hright
  apply (RealRaw.compareAt_overlap_iff _ _ n n).2
  exact ⟨Rat.le_trans hleft.1 hright.2, Rat.le_trans hright.1 hleft.2⟩

/-- A validity proof from concave FTC, not from the direct endpoint theorem. -/
theorem integral_valid_viaFTC (B : ArctanInverseBisection) (a b : Rat)
    (ha : OnHalf a) (hb : OnHalf b) (hab : a <= b) :
    (integral B a b ha hb hab).Valid := by
  exact ConcaveFTC.integral_valid (primitiveDerivativeData B) ha hb hab (error a b)
    (error_shrinks ha hb hab) (concave_error_budget B hab)

/-- The concavity/derivative/FTC proof of the same proposition proved
independently by `integral_cosPi_viaInequalities`. -/
theorem integral_cosPi_viaFTC (B : ArctanInverseBisection) (a b : Rat)
    (ha : OnHalf a) (hb : OnHalf b) (hab : a <= b) :
    IntegralCosineStatement B a b ha hb hab := by
  have hftc := ConcaveFTC.integral_equiv_endpoint (primitiveDerivativeData B)
    ha hb hab (error a b) (concave_error_budget B hab)
  have hfirst : (integral B a b ha hb hab).Equiv
      (ConcaveFTC.endpointDifference (primitiveFun B) a b) := hftc
  have h := RealRaw.equiv_trans (integral_valid_viaFTC B a b ha hb hab)
    (ConcaveFTC.endpointDifference_valid (primitiveDerivativeData B) ha hb)
    (endpoint_valid B a b) hfirst (primitive_difference_equiv_endpoint B a b)
  simpa only [IntegralCosineStatement, endpoint, sine, dif_pos ha, dif_pos hb] using h

end CosineFTC
end ComputableAnalysis
