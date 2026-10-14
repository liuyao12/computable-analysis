import ComputableAnalysis.ModularForms.CMCoordinates163

/-! Exact imaginary coordinates and a uniform root enclosure for lattice estimates. -/
namespace ComputableAnalysis.ModularForms

theorem sqrt163_uniform_bounds (n : Nat) :
    0≤(sqrt163.compute n).lo ∧ (sqrt163.compute n).hi≤163 := by
  have hs := sqrtRaw_stage_spec 163 (by unfold sqrtDomain; decide +kernel) n
  have hh := sqrtApproxOnDomain_hi_le_upperBound 163 (by unfold sqrtDomain; decide +kernel) n
  have hl := hs.1
  change 0≤(sqrt163.compute n).lo at hl
  change (sqrt163.compute n).hi≤sqrtUpperBound 163 at hh
  have hb : sqrtUpperBound 163=163 := by decide +kernel
  rw [hb] at hh
  exact ⟨hl,hh⟩

namespace QuadraticOrder163

theorem complexRaw_imag_compute (u : QuadraticOrder163) (n : Nat) :
    u.complexRaw.imagPart.compute n=
      (RealRaw.scaleRat ((u.y:Rat)/2) sqrt163).compute n := by
  simp only [complexRaw,integerAffine,translate,cmPoint163,ComplexRaw.imagPart,
    ComplexRaw.scaleRat,ComplexRaw.add,ComplexRaw.one,ComplexRaw.ofQComplex,
    ComplexRaw.imaginaryAxis_compute,QBox.scaleRat,QBox.add,QComplex.add,QComplex.one,
    RealRaw.scaleRat,RealRaw.scaleRatCompute]
  simp only [if_pos (show (0:Rat)≤1/2 by decide +kernel)]
  split <;> split <;> congr 1 <;> grind

end QuadraticOrder163
end ComputableAnalysis.ModularForms
