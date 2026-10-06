import ComputableAnalysis.ModularForms.EntireExponential

/-! The factorial exponential satisfies its actual derivative equation. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert

 theorem exponentialCoefficient_shift (n : Nat) :
    (scaleRat ((n+1 : Nat) : Rat) (exponentialCoefficients (n+1))).Equiv
      (exponentialCoefficients n) := by
  have he := congrFun FormalPowerSeries.expCoeff_derivative n
  change ((n+1 : Nat) : Rat)*(1/factorialRat (n+1))=1/factorialRat n at he
  have hp : 0 ≤ ((n+1 : Nat) : Rat) := Rat.le_of_lt (Rat.natCast_pos.mpr (Nat.succ_pos n))
  intro k
  apply (compareAt_overlap_iff _ _ k k).mpr
  simp only [scaleRat, exponentialCoefficients, ofQComplex, QBox.scaleRat, if_pos hp,
    QBox.Overlaps, QComplex.le_def, he, Rat.mul_zero]
  exact ⟨⟨Rat.le_refl,Rat.le_refl⟩,⟨Rat.le_refl,Rat.le_refl⟩⟩

theorem exponentialDerivativeTerm (z : Scalar) (n : Nat) :
    (BoundedSeries.derivativeTerm exponentialCoefficients z.val n).Equiv
      (LocalODE.seriesTerm exponentialCoefficients z.val n) := by
  have h := scaleRat_mul_equiv ((n+1 : Nat) : Rat) (exponentialCoefficients (n+1))
    (LocalODE.power z.val n) (exponentialCoefficients_valid _) (LocalODE.power_valid _ z.property _)
  exact equiv_trans
    (BoundedSeries.derivativeTerm_valid _ _ exponentialCoefficients_valid z.property n)
    (mul_valid (scaleRat_valid (exponentialCoefficients_valid _)) (LocalODE.power_valid _ z.property _))
    (LocalODE.seriesTerm_valid _ _ exponentialCoefficients_valid z.property n) h
    (mul_equiv (scaleRat_valid (exponentialCoefficients_valid _)) (exponentialCoefficients_valid _)
      (LocalODE.power_valid _ z.property _) (LocalODE.power_valid _ z.property _)
      (exponentialCoefficient_shift n) (equiv_refl _ (LocalODE.power_valid _ z.property _)))

/-- The independently constructed sum of derivative terms equals the value sum. -/
theorem exponentialChart_derivative_value (R : QPos) (z : Scalar)
    (hz : (exponentialChart R).domain z) :
    ((exponentialChart_holomorphic R).derivative z).Equiv ((exponentialChart R).eval z) := by
  let K := exponentialRatio R
  let C := exponentialBudget K
  have hK : 0 ≤ K := Rat.le_of_lt (exponentialRatio_positive R)
  have hC : 0 ≤ C := exponentialBudget_nonnegative K (exponentialRatio_positive R)
  have hR : 0 ≤ R.val := Rat.le_of_lt R.property
  have hzB := LocalODE.interior_bound R.val z hz
  have hcB := exponentialCoefficients_small K (exponentialRatio_positive R)
  have h8 := exponentialRatio_local R
  have hq : 0 ≤ 4*K*R.val := Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) hK) hR
  have hr : 0 ≤ 2*K*R.val := Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) hK) hR
  have h4 : 4*K*R.val ≤ (1 : Rat)/2 := by change 8*K*R.val ≤ (1 : Rat)/2 at h8; grind only
  have h2 : 2*K*R.val ≤ (1 : Rat)/2 := by grind only
  apply ScalarSeries.value_congr
    (BoundedSeries.derivativeTerm exponentialCoefficients z.val)
    (LocalODE.seriesTerm exponentialCoefficients z.val)
    (BoundedSeries.derivativeTerm_valid _ _ exponentialCoefficients_valid z.property)
    (LocalODE.seriesTerm_valid _ _ exponentialCoefficients_valid z.property)
    (C*K) (4*K*R.val) C (2*K*R.val) (Rat.mul_nonneg hC hK) hq hC hr h4 h2
  · intro n
    simpa only [Rat.mul_assoc] using BoundedSeries.derivativeTerm_majorant
      exponentialCoefficients z.val exponentialCoefficients_valid z.property C K R.val hC hK hR hcB hzB n
  · exact LocalODE.seriesTerm_bound exponentialCoefficients z.val exponentialCoefficients_valid
      z.property C K R.val hC hK hR hcB hzB
  · exact exponentialDerivativeTerm z

/-- The actual entire exponential has derivative equal to its value. -/
theorem entireExponential_derivative_value (z : Scalar) :
    (entireExponential_holomorphic.derivative z trivial).val.Equiv
      (entireExponentialValue z).val :=
  equiv_trans (entireExponential_holomorphic.derivative z trivial).property
    (entireExponentialValue z).property (entireExponentialValue z).property
    (exponentialChart_derivative_value (exponentialInputRadius z) z (exponentialInputRadius_mem z))
    (equiv_refl _ (entireExponentialValue z).property)

/-- The entire factorial exponential is normalized to one at zero. -/
theorem entireExponential_zero :
    (entireExponentialValue ⟨zero,ofQComplex_valid _⟩).val.Equiv (ofQComplex QComplex.one) := by
  let R : QPos := ⟨1,by decide +kernel⟩
  let z : Scalar := ⟨zero,ofQComplex_valid _⟩
  have hz : (exponentialChart R).domain z :=
    ⟨0,Rat.le_refl,R.property,Small.zero Rat.le_refl⟩
  have hinit := BoundedSeries.seriesMap_initial exponentialCoefficients exponentialCoefficients_valid
    (exponentialBudget (exponentialRatio R)) (exponentialRatio R) R.val
    (exponentialBudget_nonnegative _ (exponentialRatio_positive R))
    (Rat.le_of_lt (exponentialRatio_positive R)) (Rat.le_of_lt R.property)
    (exponentialCoefficients_small _ (exponentialRatio_positive R)) (exponentialRatio_local R)
  have hc : (exponentialCoefficients 0).Equiv (ofQComplex QComplex.one) := by
    intro k
    apply (compareAt_overlap_iff _ _ k k).mpr
    change ((1 : Rat)/((1 : Nat) : Rat) ≤ 1 ∧ (0 : Rat) ≤ 0) ∧
      ((1 : Rat) ≤ (1 : Rat)/((1 : Nat) : Rat) ∧ (0 : Rat) ≤ 0)
    decide +kernel
  exact equiv_trans (entireExponentialValue z).property
    ((exponentialChart R).valid z hz) (ofQComplex_valid _)
    (equiv_symm (entireExponential_chart R z hz))
    (equiv_trans ((exponentialChart R).valid z hz) (exponentialCoefficients_valid 0)
      (ofQComplex_valid _) hinit hc)

end ComputableAnalysis.ModularForms
