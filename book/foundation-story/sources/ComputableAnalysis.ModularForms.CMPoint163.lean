import ComputableAnalysis.AlgebraicFunctions
import ComputableAnalysis.ModularForms.UpperHalfPlane

/-! An executable represented CM point for discriminant -163. -/
namespace ComputableAnalysis.ModularForms

private theorem sqrt163_domain : sqrtDomain 163 := by
  unfold sqrtDomain
  decide +kernel

def sqrt163 : RealRaw := sqrtRaw 163 sqrt163_domain

theorem sqrt163_valid : sqrt163.Valid := sqrtRaw_valid _ _

theorem sqrt163_square : (RealRaw.mul sqrt163 sqrt163).Equiv (RealRaw.ofRat 163) :=
  sqrtRaw_mul_self_equiv_of_domain _ _

theorem sqrt163_positive : sqrt163.Pos := by
  obtain ⟨N,hN⟩ := sqrt163_valid.2.2 (⟨1/2,by decide +kernel⟩ : QPos)
  have hw := hN N (Nat.le_refl N)
  have hs := sqrtRaw_stage_spec 163 sqrt163_domain N
  have hl := hs.sub_width_le_lo_of_sq_le (r := 1) (by decide +kernel)
  refine ⟨N, ?_⟩
  change 0<(sqrtApproxOnDomain 163 sqrt163_domain N).lo
  change (sqrtApproxOnDomain 163 sqrt163_domain N).width≤1/2 at hw
  change 1-(sqrtApproxOnDomain 163 sqrt163_domain N).width≤
    (sqrtApproxOnDomain 163 sqrt163_domain N).lo at hl
  grind

def cmPoint163 : ComplexRaw :=
  ComplexRaw.scaleRat (1/2)
    (ComplexRaw.add ComplexRaw.one (ComplexRaw.imaginaryAxis sqrt163))

theorem cmPoint163_valid : cmPoint163.Valid :=
  ComplexRaw.scaleRat_valid_of_nonneg (by decide +kernel)
    (ComplexRaw.add_valid (ComplexRaw.ofQComplex_valid _) (ComplexRaw.imaginaryAxis_valid sqrt163_valid))

theorem cmPoint163_upper : InUpperHalfPlane cmPoint163 := by
  obtain ⟨N,hN⟩ := sqrt163_positive
  refine ⟨N, ?_⟩
  change 0<(cmPoint163.compute N).lo.im
  unfold cmPoint163
  simp only [ComplexRaw.scaleRat,ComplexRaw.add,ComplexRaw.one,
    ComplexRaw.ofQComplex,ComplexRaw.imaginaryAxis_compute,QBox.scaleRat,
    QBox.add,if_pos (show (0:Rat)≤1/2 by decide +kernel)]
  change 0<(1/2)*(0+(sqrt163.compute N).lo)
  change 0<(sqrt163.compute N).lo at hN
  grind

end ComputableAnalysis.ModularForms
