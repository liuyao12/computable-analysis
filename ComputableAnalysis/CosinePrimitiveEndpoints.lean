import ComputableAnalysis.CosinePrimitiveData

/-! Endpoint simplification shared by the two basepoint proofs. This file
contains no integral evaluation theorem and imports no Mathlib module. -/
namespace ComputableAnalysis.CosinePrimitive
open ClosedArctanInverse IntervalSelections

theorem inversePi_valid : inversePi.Valid := by
  rw [inversePi_eq]
  exact SinPiIntegral.reciprocalPiRaw_valid

theorem endpoint_valid (t : Rat) : (endpoint t).Valid :=
  RealRaw.mul_valid inversePi_valid (S_valid t)

/-- The zero sine value is obtained from the inverse clock, not from any
integral endpoint formula or a second trigonometric implementation. -/
theorem S_zero : (S 0).Equiv RealRaw.zero := by
  have h0 : Domain 0 := by constructor <;> decide +kernel
  have hle : (S 0).Le RealRaw.zero := by
    apply le_of_eventually (S_valid 0) (RealRaw.ofRat_valid 0)
      (fun n => ((S 0).compute n).lo) (fun _ => 0)
      (fun n => ⟨Rat.le_refl,RealRaw.interval_order_of_valid _ (S_valid 0) n⟩)
      (fun _ => ⟨Rat.le_refl,Rat.le_refl⟩)
    intro eps
    let eta : QPos := ⟨eps.val/2,by
      rw [Rat.div_def]
      exact Rat.mul_pos eps.property ((Rat.inv_pos).2 (by decide))⟩
    obtain ⟨N,hN⟩ := GeometricSineDerivative.slope_clock_close provider 0 h0 eta
    refine ⟨N,?_⟩
    intro n hn
    let u := ((GeometricSineDerivative.slope provider 0 h0).compute n).lo
    have hu := GeometricSineDerivative.slope_unit provider 0 h0 n
    have hu1 : u <= 1 := Rat.le_trans hu.2.1 hu.2.2
    have ha := hN n hn u (ArctanGeometry.arctanIntegralRectangleCompute u n).lo
      (piCircleArea.compute n).lo Rat.le_refl hu.2.1 Rat.le_refl
      (RealRaw.interval_order_of_valid _ (ArctanGeometry.arctanIntegralRectangleRaw_valid hu.1 hu1) n)
      Rat.le_refl (RealRaw.interval_order_of_valid _ CauchyPi.piCircleArea_valid n)
    have hk := ArctanGeometry.arctanIntegralRectangleCompute_input_mul_kernel_le_lower hu.1 n
    have hh := self_le_qabs (ArctanGeometry.arctanIntegralRectangleCompute u n).lo
    have hs : ((S 0).compute n).lo = 2*(u*ArctanGeometry.integralKernel u) := by
      simp only [S,CosineFTC.sine,dif_pos h0]
      change SinPiIntegral.rationalCircleSin u = _
      unfold SinPiIntegral.rationalCircleSin ArctanGeometry.integralKernel
      simp only [Rat.div_def,Rat.one_mul]
      grind
    rw [hs]
    dsimp [eta] at ha
    simp only [Rat.div_def,Rat.zero_mul,Rat.sub_eq_add_neg] at ha
    grind
  intro n
  have hu := GeometricSineDerivative.slope_unit provider 0 h0 n
  have hpos : 0 <= ((S 0).compute n).lo := by
    simp only [S,CosineFTC.sine,dif_pos h0]
    exact (SinPiIntegral.rationalCircleSin_bounds hu.1 (Rat.le_trans hu.2.1 hu.2.2)).1
  exact (RealRaw.compareAt_overlap_iff _ _ n n).2
    ⟨hle n n,Rat.le_trans hpos (RealRaw.interval_order_of_valid _ (S_valid 0) n)⟩

theorem endpoints_from_zero (t : Rat) :
    (CosineFTC.endpoint provider 0 t).Equiv (endpoint t) := by
  intro n
  have hzero := (RealRaw.compareAt_overlap_iff _ _ n n).1 (S_zero n)
  have hz : InBox 0 ((S 0).compute n) := ⟨hzero.1,hzero.2⟩
  let s := ((S t).compute n).lo
  let r := (inversePi.compute n).lo
  have hs : InBox s ((S t).compute n) :=
    ⟨Rat.le_refl,RealRaw.interval_order_of_valid _ (S_valid t) n⟩
  have hr : InBox r (inversePi.compute n) :=
    ⟨Rat.le_refl,RealRaw.interval_order_of_valid _ inversePi_valid n⟩
  have hr' : InBox r (SinPiIntegral.reciprocalPiRaw.compute n) := by
    rw [← inversePi_compute]; exact hr
  have hdiff : InBox s (((S t)-(S 0)).compute n) := by
    have h := sub_mem hs hz
    rw [show s-0=s by grind] at h
    exact h
  have hl : InBox (r*s) ((CosineFTC.endpoint provider 0 t).compute n) := mul_mem hr' hdiff
  have hu : InBox (r*s) ((endpoint t).compute n) := mul_mem hr hs
  exact (RealRaw.compareAt_overlap_iff _ _ n n).2
    ⟨Rat.le_trans hl.1 hu.2,Rat.le_trans hu.1 hl.2⟩

end ComputableAnalysis.CosinePrimitive
