import ComputableAnalysis.ModularForms.GlobalDiscriminantNonvanishing
import ComputableAnalysis.ModularForms.ScalarNoZeroDivisors

/-! Exact modular fixed-point laws for the actual lattice sums and j function.
These laws use genuine transformation and fixed-point evidence; they do not
assume algebraicity or a class-polynomial certificate. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

/-- A value multiplied by a nonidentity scalar can be fixed only if it vanishes. -/
theorem modular_weight_fixed_value_zero (x m : Scalar)
    (h : x.val.Equiv (mul m.val x.val))
    (hm : ¬m.val.Equiv (ofQComplex QComplex.one)) :
    x.val.Equiv zero := by
  let X := ComplexRawQuotient.ofRaw x.val x.property
  let M := ComplexRawQuotient.ofRaw m.val m.property
  have he : X=M*X := ComplexRawQuotient.ofRaw_eq_ofRaw h
  have hn : M-1≠0 := by
    intro hz
    apply hm
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := m.property) (hright := ofQComplex_valid _)
    change M=1
    grind only
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := x.property) (hright := ofQComplex_valid _)
  change X=0
  apply Classical.byContradiction
  intro hx
  apply scalarClass_mul_nonzero (M-1) X hn hx
  grind only

theorem upperWeightFour_zero_of_modular_fixed (g : SL2Z) (z : Scalar)
    (hz : InUpperHalfPlane z.val)
    (hfix : (fractionalLinear g z hz).val.Equiv z.val)
    (hm : ¬(LocalODE.power (integerAffine g.c g.d z.val) 4).Equiv
      (ofQComplex QComplex.one)) :
    (upperWeightFourLatticeSum z hz).Equiv zero := by
  apply modular_weight_fixed_value_zero
    ⟨upperWeightFourLatticeSum z hz,upperWeightFourLatticeSum_valid z hz⟩
    ⟨LocalODE.power (integerAffine g.c g.d z.val) 4,
      LocalODE.power_valid _ (integerAffine_valid _ _ z.property) 4⟩ _ hm
  exact equiv_trans (upperWeightFourLatticeSum_valid z hz)
    (upperWeightFourLatticeSum_valid _ (fractionalLinear_mem g z hz))
    (mul_valid (LocalODE.power_valid _ (integerAffine_valid _ _ z.property) 4)
      (upperWeightFourLatticeSum_valid z hz))
    (equiv_symm (upperWeightFourLatticeSum_congr _ _ _ hz hfix))
    (upperWeightFourLatticeSum_action g z hz)

theorem upperWeightSix_zero_of_modular_fixed (g : SL2Z) (z : Scalar)
    (hz : InUpperHalfPlane z.val)
    (hfix : (fractionalLinear g z hz).val.Equiv z.val)
    (hm : ¬(LocalODE.power (integerAffine g.c g.d z.val) 6).Equiv
      (ofQComplex QComplex.one)) :
    (upperWeightSixLatticeSum z hz).Equiv zero := by
  apply modular_weight_fixed_value_zero
    ⟨upperWeightSixLatticeSum z hz,upperWeightSixLatticeSum_valid z hz⟩
    ⟨LocalODE.power (integerAffine g.c g.d z.val) 6,
      LocalODE.power_valid _ (integerAffine_valid _ _ z.property) 6⟩ _ hm
  exact equiv_trans (upperWeightSixLatticeSum_valid z hz)
    (upperWeightSixLatticeSum_valid _ (fractionalLinear_mem g z hz))
    (mul_valid (LocalODE.power_valid _ (integerAffine_valid _ _ z.property) 6)
      (upperWeightSixLatticeSum_valid z hz))
    (equiv_symm (upperWeightSixLatticeSum_congr _ _ _ hz hfix))
    (upperWeightSixLatticeSum_action g z hz)

theorem latticeJMap_value_of_weightFour_zero (z : Scalar)
    (hz : InUpperHalfPlane z.val)
    (h4 : (upperWeightFourLatticeSum z hz).Equiv zero) :
    (latticeJMap.eval z (latticeJMap_global_domain z hz)).val.Equiv zero := by
  have he := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := upperWeightFourLatticeSum_valid z hz) (hright := ofQComplex_valid _) h4
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (latticeJMap.eval z (latticeJMap_global_domain z hz)).property)
    (hright := ofQComplex_valid _)
  let V := ComplexRawQuotient.ofRaw (upperWeightFourLatticeSum z hz)
    (upperWeightFourLatticeSum_valid z hz)
  let R := ComplexRawQuotient.ofRaw
    (RepresentedReciprocal.inverse (latticeDiscriminantMap.eval z hz)
      (latticeDiscriminantMap_global_nonzero z hz)).val
    (RepresentedReciprocal.inverse (latticeDiscriminantMap.eval z hz)
      (latticeDiscriminantMap_global_nonzero z hz)).property
  let C60 := ComplexRawQuotient.ofQComplex ⟨60,0⟩
  let C := ComplexRawQuotient.ofQComplex ⟨1728,0⟩
  change V=0 at he
  change R*(C*(((C60*V)*(C60*V))*(C60*V)))=0
  rw [he]
  grind only

theorem latticeJMap_value_of_weightSix_zero (z : Scalar)
    (hz : InUpperHalfPlane z.val)
    (h6 : (upperWeightSixLatticeSum z hz).Equiv zero) :
    (latticeJMap.eval z (latticeJMap_global_domain z hz)).val.Equiv
      (ofQComplex ⟨1728,0⟩) := by
  let D := latticeDiscriminantMap.eval z hz
  let R := RepresentedReciprocal.inverse D (latticeDiscriminantMap_global_nonzero z hz)
  let N := latticeG2CubeMap.eval z hz
  let DV := ComplexRawQuotient.ofRaw D.val D.property
  let RV := ComplexRawQuotient.ofRaw R.val R.property
  let NV := ComplexRawQuotient.ofRaw N.val N.property
  let V6 := ComplexRawQuotient.ofRaw (upperWeightSixLatticeSum z hz)
    (upperWeightSixLatticeSum_valid z hz)
  let C140 := ComplexRawQuotient.ofQComplex ⟨140,0⟩
  let C27 := ComplexRawQuotient.ofQComplex ⟨27,0⟩
  let C := ComplexRawQuotient.ofQComplex ⟨1728,0⟩
  have he : V6=0 := ComplexRawQuotient.ofRaw_eq_ofRaw h6
  have hd : DV=NV := by
    change NV + -(C27*((C140*V6)*(C140*V6)))=NV
    rw [he]
    grind only
  have hi : DV*RV=1 := ComplexRawQuotient.ofRaw_eq_ofRaw
    (RepresentedReciprocal.mul_inverse D (latticeDiscriminantMap_global_nonzero z hz))
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (latticeJMap.eval z (latticeJMap_global_domain z hz)).property)
    (hright := ofQComplex_valid _)
  change RV*(C*NV)=C
  grind only

/-- At a modular fixed point with nontrivial weight-four multiplier, j is zero. -/
theorem latticeJMap_zero_of_modular_fixed (g : SL2Z) (z : Scalar)
    (hz : InUpperHalfPlane z.val)
    (hfix : (fractionalLinear g z hz).val.Equiv z.val)
    (hm : ¬(LocalODE.power (integerAffine g.c g.d z.val) 4).Equiv
      (ofQComplex QComplex.one)) :
    (latticeJMap.eval z (latticeJMap_global_domain z hz)).val.Equiv zero :=
  latticeJMap_value_of_weightFour_zero z hz
    (upperWeightFour_zero_of_modular_fixed g z hz hfix hm)

/-- At a modular fixed point with nontrivial weight-six multiplier, j is 1728. -/
theorem latticeJMap_1728_of_modular_fixed (g : SL2Z) (z : Scalar)
    (hz : InUpperHalfPlane z.val)
    (hfix : (fractionalLinear g z hz).val.Equiv z.val)
    (hm : ¬(LocalODE.power (integerAffine g.c g.d z.val) 6).Equiv
      (ofQComplex QComplex.one)) :
    (latticeJMap.eval z (latticeJMap_global_domain z hz)).val.Equiv
      (ofQComplex ⟨1728,0⟩) :=
  latticeJMap_value_of_weightSix_zero z hz
    (upperWeightSix_zero_of_modular_fixed g z hz hfix hm)

end ComputableAnalysis.ModularForms
