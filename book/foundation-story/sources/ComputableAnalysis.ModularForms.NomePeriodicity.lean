import ComputableAnalysis.ModularForms.GeometricQuarterTurn
import ComputableAnalysis.ModularForms.NomeRotation

/-! Exact geometric rotation and period one for the actual nome. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

theorem geometricRotation_quarterTurn : GeometricPiRotation.rotation.Equiv
    (ofQComplex RotationSeries.imaginaryUnit) :=
  equiv_trans GeometricPiRotation.rotation_valid (entireExponentialValue _).property
    (ofQComplex_valid _) (equiv_symm entireExponential_geometric_halfPi_rotation)
    entireExponential_geometric_quarterTurn

private theorem imaginaryUnit_fourth :
    (LocalODE.power (ofQComplex RotationSeries.imaginaryUnit) 4).Equiv
      (ofQComplex QComplex.one) := by
  intro n
  apply (compareAt_overlap_iff _ _ n n).mpr
  change ((LocalODE.power (ofQComplex RotationSeries.imaginaryUnit) 4).compute 0).Overlaps
    ((ofQComplex QComplex.one).compute 0)
  decide +kernel

theorem geometricRotation_fourth : (LocalODE.power GeometricPiRotation.rotation 4).Equiv
    (ofQComplex QComplex.one) :=
  equiv_trans (LocalODE.power_valid _ GeometricPiRotation.rotation_valid 4)
    (LocalODE.power_valid _ (ofQComplex_valid _) 4) (ofQComplex_valid _)
    (LocalODE.power_congr _ _ GeometricPiRotation.rotation_valid (ofQComplex_valid _)
      geometricRotation_quarterTurn 4) imaginaryUnit_fourth

theorem nome_period_one (z : Scalar) (hz : InUpperHalfPlane z.val) :
    (nome.eval ⟨translate 1 z.val,translate_valid 1 z.property⟩ (translate_mem 1 hz)).val.Equiv
      (nome.eval z hz).val := by
  have hv := (nome.eval z hz).property
  have hm := mul_equiv hv hv (LocalODE.power_valid _ GeometricPiRotation.rotation_valid 4)
    (ofQComplex_valid _) (equiv_refl _ hv) geometricRotation_fourth
  exact equiv_trans (nome.eval _ _).property
    (mul_valid hv (LocalODE.power_valid _ GeometricPiRotation.rotation_valid 4)) hv
    (nome_translate_one z hz)
    (equiv_trans (mul_valid hv (LocalODE.power_valid _ GeometricPiRotation.rotation_valid 4))
      (mul_valid hv (ofQComplex_valid _)) hv hm (mul_one_equiv _ hv))

end ComputableAnalysis.ModularForms
