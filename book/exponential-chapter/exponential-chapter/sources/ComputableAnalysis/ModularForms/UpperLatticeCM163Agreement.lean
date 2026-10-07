import ComputableAnalysis.ModularForms.UpperLatticeSumCongruence
import ComputableAnalysis.ModularForms.CMWeightSixSum163

/-! Agreement of general lattice evaluators with the earlier discriminant-163 sums. -/
namespace ComputableAnalysis.ModularForms
open RiemannHilbert FunctionTheory ComplexRaw QuadraticOrder163

abbrev cmScalar163 : Scalar := ⟨cmPoint163,cmPoint163_valid⟩

theorem upperShellTerm_cm_agreement (r : Nat) (hr : 0<r) (k i : Nat) :
    (upperShellTerm cmScalar163 cmPoint163_upper r hr k i).Equiv (shellTerm r hr k i) := by
  unfold upperShellTerm shellTerm
  split
  · rename_i hi
    have ha := latticeInverse_cm_agreement (shellPoint r ⟨i,hi⟩) (shellPoint_nonzero r hr ⟨i,hi⟩)
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := LocalODE.power_valid _ (latticeInverse cmScalar163 cmPoint163_upper _ _).property k)
      (hright := LocalODE.power_valid _ (complexInverse _ _).property k)
    rw [ScalarAlgebra.ofRaw_power _ (latticeInverse cmScalar163 cmPoint163_upper _ _).property k,
      ScalarAlgebra.ofRaw_power _ (complexInverse _ _).property k]
    rw [ComplexRawQuotient.ofRaw_eq_ofRaw ha]
  · exact equiv_refl _ (ofQComplex_valid _)

theorem upperShellPrefix_cm_agreement (r : Nat) (hr : 0<r) (k n : Nat) :
    (upperShellPrefix cmScalar163 cmPoint163_upper r hr k n).Equiv (shellPrefix r hr k n) := by
  induction n with
  | zero => exact equiv_refl _ (ofQComplex_valid _)
  | succ n ih => exact add_equiv ih (upperShellTerm_cm_agreement r hr k n)

theorem upperWeightFourTailBlock_cm_agreement (N n : Nat) :
    (upperWeightFourTailBlock cmScalar163 cmPoint163_upper N n).Equiv (weightFourTailBlock N n) := by
  induction n with
  | zero => exact equiv_refl _ (ofQComplex_valid _)
  | succ n ih => exact add_equiv ih (upperShellPrefix_cm_agreement (N+n+1) (by omega) 4 _)

theorem upperWeightFourLatticeSum_cm_agreement :
    (upperWeightFourLatticeSum cmScalar163 cmPoint163_upper).Equiv weightFourLatticeSum163 := by
  apply RepresentedCauchySum.value_congr
    (upperWeightFourPrefix cmScalar163 cmPoint163_upper) weightFourPrefix
    (upperWeightFourPrefix_valid cmScalar163 cmPoint163_upper) weightFourPrefix_valid
    (upperWeightFourTailRate cmScalar163 cmPoint163_upper) weightFourTailRate
    (upperWeightFourTailRate_shrinks cmScalar163 cmPoint163_upper) weightFourTailRate_shrinks
  · intro n
    unfold upperWeightFourTailRate upperWeightFourTailConstant reciprocalSquare
    have hp : 0<((n+1:Nat):Rat) := by exact_mod_cast (show 0<n+1 by omega)
    exact Rat.mul_nonneg
      (Rat.mul_nonneg (by decide) (Rat.pow_nonneg
        (Rat.mul_nonneg (by decide) (latticeReciprocalConstant_nonnegative cmScalar163 cmPoint163_upper))))
      (Rat.le_of_lt (Rat.inv_pos.mpr (Rat.mul_pos hp hp)))
  · intro n
    unfold weightFourTailRate reciprocalSquare
    have hp : 0<((n+1:Nat):Rat) := by exact_mod_cast (show 0<n+1 by omega)
    exact Rat.mul_nonneg (by unfold weightFourTailConstant; decide +kernel)
      (Rat.le_of_lt (Rat.inv_pos.mpr (Rat.mul_pos hp hp)))
  · exact upperWeightFourPrefix_cauchy cmScalar163 cmPoint163_upper
  · exact weightFourPrefix_cauchy
  · intro n
    exact upperWeightFourTailBlock_cm_agreement 0 (n+1)

theorem upperWeightSixTailBlock_cm_agreement (N n : Nat) :
    (upperWeightSixTailBlock cmScalar163 cmPoint163_upper N n).Equiv (weightSixTailBlock N n) := by
  induction n with
  | zero => exact equiv_refl _ (ofQComplex_valid _)
  | succ n ih => exact add_equiv ih (upperShellPrefix_cm_agreement (N+n+1) (by omega) 6 _)

theorem upperWeightSixLatticeSum_cm_agreement :
    (upperWeightSixLatticeSum cmScalar163 cmPoint163_upper).Equiv weightSixLatticeSum163 := by
  apply RepresentedCauchySum.value_congr
    (upperWeightSixPrefix cmScalar163 cmPoint163_upper) weightSixPrefix
    (upperWeightSixPrefix_valid cmScalar163 cmPoint163_upper) weightSixPrefix_valid
    (upperWeightSixTailRate cmScalar163 cmPoint163_upper) weightSixTailRate
    (upperWeightSixTailRate_shrinks cmScalar163 cmPoint163_upper) weightSixTailRate_shrinks
  · intro n
    unfold upperWeightSixTailRate upperWeightSixTailConstant reciprocalSquare
    have hp : 0<((n+1:Nat):Rat) := by exact_mod_cast (show 0<n+1 by omega)
    exact Rat.mul_nonneg
      (Rat.mul_nonneg (by decide) (Rat.pow_nonneg
        (Rat.mul_nonneg (by decide) (latticeReciprocalConstant_nonnegative cmScalar163 cmPoint163_upper))))
      (Rat.le_of_lt (Rat.inv_pos.mpr (Rat.mul_pos hp hp)))
  · intro n
    unfold weightSixTailRate reciprocalSquare
    have hp : 0<((n+1:Nat):Rat) := by exact_mod_cast (show 0<n+1 by omega)
    exact Rat.mul_nonneg (by unfold weightSixTailConstant; decide +kernel)
      (Rat.le_of_lt (Rat.inv_pos.mpr (Rat.mul_pos hp hp)))
  · exact upperWeightSixPrefix_cauchy cmScalar163 cmPoint163_upper
  · exact weightSixPrefix_cauchy
  · intro n
    exact upperWeightSixTailBlock_cm_agreement 0 (n+1)

end ComputableAnalysis.ModularForms
