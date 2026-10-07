import ComputableAnalysis.ModularForms.UpperFourthRoot
import ComputableAnalysis.ModularForms.StrictOrderSandwich
import ComputableAnalysis.ModularForms.NomePeriodicity

/-! Identification of the actual lattice half-frequency with the geometric
half-pi construction, using proved represented angle uniqueness. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert

theorem latticeHalfFrequency_geometric_halfPi :
    latticeHalfFrequencyRotationInput.raw.Equiv GeometricPiRotation.halfPi := by
  let A : BoundedAngle := ⟨latticeHalfFrequencyRotationInput.raw,
    latticeHalfFrequencyRotationInput.valid,latticeHalfFrequencyRotationInput.bounds⟩
  let B : BoundedAngle := ⟨GeometricPiRotation.halfPiInput.raw,
    GeometricPiRotation.halfPiInput.valid,GeometricPiRotation.halfPiInput.bounds⟩
  have ha := angleRotationMap_real_input_agreement latticeHalfFrequencyRotationInput
  have hb := angleRotationMap_real_input_agreement GeometricPiRotation.halfPiInput
  have hi := equiv_trans (RotationLift.HalfPiInput.rotation_valid latticeHalfFrequencyRotationInput)
    latticeImaginaryUnit.property GeometricPiRotation.rotation_valid
    latticeHalfFrequency_rotation_imaginary_unit (equiv_symm geometricRotation_quarterTurn)
  have he := equiv_trans (angleRotationMap.eval A.scalar ⟨trivial,trivial⟩).property
    (RotationLift.HalfPiInput.rotation_valid latticeHalfFrequencyRotationInput)
    (angleRotationMap.eval B.scalar ⟨trivial,trivial⟩).property ha
    (equiv_trans (RotationLift.HalfPiInput.rotation_valid latticeHalfFrequencyRotationInput)
      GeometricPiRotation.rotation_valid
      (angleRotationMap.eval B.scalar ⟨trivial,trivial⟩).property hi (equiv_symm hb))
  exact represented_rotation_angle_unique A B (realPart_equiv he)

theorem latticeFrequency_half_geometric_halfPi :
    (RealRaw.scaleRat (1/2) latticeFrequency.val.realPart).Equiv GeometricPiRotation.halfPi :=
  RealRaw.equiv_trans
    (RealRaw.scaleRat_valid (realPart_valid latticeFrequency.property))
    latticeHalfFrequencyRotationInput.valid GeometricPiRotation.halfPi_valid
    (RealRaw.equiv_symm latticeHalfFrequencyRotationInput_agreement)
    latticeHalfFrequency_geometric_halfPi

theorem latticeFrequency_geometric_pi :
    latticeFrequency.val.realPart.Equiv (RealRaw.scaleRat 2 GeometricPiRotation.halfPi) := by
  let x := latticeFrequency.val.realPart
  have hx := realPart_valid latticeFrequency.property
  have hc : (RealRaw.scaleRat 2 (RealRaw.scaleRat (1/2) x)).Equiv x := by
    intro n
    apply (RealRaw.compareAt_overlap_iff _ _ n n).2
    have ho := RealRaw.interval_order_of_valid x hx n
    change QInterval.Overlaps
      (RealRaw.scaleRatCompute 2 (RealRaw.scaleRat (1/2) x) n) (x.compute n)
    simp only [RealRaw.scaleRatCompute,RealRaw.scaleRat,
      if_pos (show (0:Rat)≤2 by decide +kernel),
      if_pos (show (0:Rat)≤1/2 by decide +kernel),QInterval.Overlaps]
    constructor <;> grind only
  exact RealRaw.equiv_trans hx
    (RealRaw.scaleRat_valid (RealRaw.scaleRat_valid hx))
    (RealRaw.scaleRat_valid GeometricPiRotation.halfPi_valid)
    (RealRaw.equiv_symm hc) (RealRaw.scaleRat_equiv latticeFrequency_half_geometric_halfPi)

end ComputableAnalysis.ModularForms
