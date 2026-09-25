import ComputableAnalysis.IntegralEnclosure
import ComputableAnalysis.ArctanEffectiveFTC

/-! Concrete clients retain range evidence all the way to the public value. -/
namespace ComputableAnalysis.Integral

/-- The arctangent kernel has a specific whole-cell enclosure construction.
Its endpoint evaluator is licensed by the finite derivative-bound comparison. -/
def arctanEnclosureRealization : EnclosureRealizationFor arctanKernelOnUnit :=
  enclosureRealizationOfEffectiveFTC arctanEffectiveFTCData
    (RealFunRaw.exact_valid _) (by intro _ _; trivial)
    arctanEffectiveFTCEndpointValid

theorem arctanEnclosureRealization_valid : arctanEnclosureRealization.value.Valid :=
  arctanEnclosureRealization.valid

theorem arctanEnclosureRealization_equiv_geometric :
    arctanEnclosureRealization.value.Equiv (ArctanGeometry.arctanGeom 1) := by
  exact RealRaw.equiv_trans
    arctanEnclosureRealization.valid
    (candidateValue_valid arctanKernelOnUnit arctanEffectiveFTCConstruction)
    ArctanGeometry.arctanGeom_one_valid
    (RealRaw.equiv_symm arctanEffectiveFTCIntegral_equiv_endpointDifference)
    arctanEffectiveFTCIntegral_equiv_arctanGeom_one

/-- Restricting a constant integral recomputes the rectangle on the new domain. -/
theorem constant_half_interval :
    (EnclosureConstructionFor.constant 1 0 (1/2) (by native_decide)).value.Equiv
      (RealRaw.ofRat (1/2)) := by
  have h := EnclosureConstructionFor.constant_value 1 0 (1/2) (by native_decide)
  have he : (((1/2 : Rat)-0)*1) = (1/2 : Rat) := by grind
  rw [he] at h
  exact h

end ComputableAnalysis.Integral
