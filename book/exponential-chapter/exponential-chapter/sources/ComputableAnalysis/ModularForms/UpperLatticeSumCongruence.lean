import ComputableAnalysis.ModularForms.UpperWeightFourSum
import ComputableAnalysis.ModularForms.UpperWeightSixSum
import ComputableAnalysis.ModularForms.UpperLatticeCongruence

/-! Representation invariance of the constructed upper-half-plane lattice sums. -/
namespace ComputableAnalysis.ModularForms
open RiemannHilbert FunctionTheory ComplexRaw

theorem upperShellTerm_congr (z w : Scalar) (hz : InUpperHalfPlane z.val)
    (hw : InUpperHalfPlane w.val) (he : z.val.Equiv w.val)
    (r : Nat) (hr : 0<r) (k i : Nat) :
    (upperShellTerm z hz r hr k i).Equiv (upperShellTerm w hw r hr k i) := by
  unfold upperShellTerm
  split
  · rename_i hi
    have ha := latticeInverse_congr z w hz hw _
      (QuadraticOrder163.shellPoint_nonzero r hr ⟨i,hi⟩) he
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := LocalODE.power_valid _ (latticeInverse z hz _ _).property k)
      (hright := LocalODE.power_valid _ (latticeInverse w hw _ _).property k)
    rw [ScalarAlgebra.ofRaw_power _ (latticeInverse z hz _ _).property k,
      ScalarAlgebra.ofRaw_power _ (latticeInverse w hw _ _).property k]
    rw [ComplexRawQuotient.ofRaw_eq_ofRaw ha]
  · exact equiv_refl _ (ofQComplex_valid _)

theorem upperShellPrefix_congr (z w : Scalar) (hz : InUpperHalfPlane z.val)
    (hw : InUpperHalfPlane w.val) (he : z.val.Equiv w.val)
    (r : Nat) (hr : 0<r) (k n : Nat) :
    (upperShellPrefix z hz r hr k n).Equiv (upperShellPrefix w hw r hr k n) := by
  induction n with
  | zero => exact equiv_refl _ (ofQComplex_valid _)
  | succ n ih =>
      exact add_equiv ih (upperShellTerm_congr z w hz hw he r hr k n)

theorem upperWeightFourTailBlock_congr (z w : Scalar) (hz : InUpperHalfPlane z.val)
    (hw : InUpperHalfPlane w.val) (he : z.val.Equiv w.val) (N n : Nat) :
    (upperWeightFourTailBlock z hz N n).Equiv (upperWeightFourTailBlock w hw N n) := by
  induction n with
  | zero => exact equiv_refl _ (ofQComplex_valid _)
  | succ n ih =>
      exact add_equiv ih (upperShellPrefix_congr z w hz hw he (N+n+1) (by omega) 4 _)

theorem upperWeightFourLatticeSum_congr (z w : Scalar) (hz : InUpperHalfPlane z.val)
    (hw : InUpperHalfPlane w.val) (he : z.val.Equiv w.val) :
    (upperWeightFourLatticeSum z hz).Equiv (upperWeightFourLatticeSum w hw) := by
  apply RepresentedCauchySum.value_congr
    (upperWeightFourPrefix z hz) (upperWeightFourPrefix w hw)
    (upperWeightFourPrefix_valid z hz) (upperWeightFourPrefix_valid w hw)
    (upperWeightFourTailRate z hz) (upperWeightFourTailRate w hw)
    (upperWeightFourTailRate_shrinks z hz) (upperWeightFourTailRate_shrinks w hw)
  · intro n
    unfold upperWeightFourTailRate upperWeightFourTailConstant reciprocalSquare
    have hp : 0<((n+1:Nat):Rat) := by exact_mod_cast (show 0<n+1 by omega)
    exact Rat.mul_nonneg
      (Rat.mul_nonneg (by decide) (Rat.pow_nonneg
        (Rat.mul_nonneg (by decide) (latticeReciprocalConstant_nonnegative z hz))))
      (Rat.le_of_lt (Rat.inv_pos.mpr (Rat.mul_pos hp hp)))
  · intro n
    unfold upperWeightFourTailRate upperWeightFourTailConstant reciprocalSquare
    have hp : 0<((n+1:Nat):Rat) := by exact_mod_cast (show 0<n+1 by omega)
    exact Rat.mul_nonneg
      (Rat.mul_nonneg (by decide) (Rat.pow_nonneg
        (Rat.mul_nonneg (by decide) (latticeReciprocalConstant_nonnegative w hw))))
      (Rat.le_of_lt (Rat.inv_pos.mpr (Rat.mul_pos hp hp)))
  · exact upperWeightFourPrefix_cauchy z hz
  · exact upperWeightFourPrefix_cauchy w hw
  · intro n
    exact upperWeightFourTailBlock_congr z w hz hw he 0 (n+1)

theorem upperWeightSixTailBlock_congr (z w : Scalar) (hz : InUpperHalfPlane z.val)
    (hw : InUpperHalfPlane w.val) (he : z.val.Equiv w.val) (N n : Nat) :
    (upperWeightSixTailBlock z hz N n).Equiv (upperWeightSixTailBlock w hw N n) := by
  induction n with
  | zero => exact equiv_refl _ (ofQComplex_valid _)
  | succ n ih =>
      exact add_equiv ih (upperShellPrefix_congr z w hz hw he (N+n+1) (by omega) 6 _)

theorem upperWeightSixLatticeSum_congr (z w : Scalar) (hz : InUpperHalfPlane z.val)
    (hw : InUpperHalfPlane w.val) (he : z.val.Equiv w.val) :
    (upperWeightSixLatticeSum z hz).Equiv (upperWeightSixLatticeSum w hw) := by
  apply RepresentedCauchySum.value_congr
    (upperWeightSixPrefix z hz) (upperWeightSixPrefix w hw)
    (upperWeightSixPrefix_valid z hz) (upperWeightSixPrefix_valid w hw)
    (upperWeightSixTailRate z hz) (upperWeightSixTailRate w hw)
    (upperWeightSixTailRate_shrinks z hz) (upperWeightSixTailRate_shrinks w hw)
  · intro n
    unfold upperWeightSixTailRate upperWeightSixTailConstant reciprocalSquare
    have hp : 0<((n+1:Nat):Rat) := by exact_mod_cast (show 0<n+1 by omega)
    exact Rat.mul_nonneg
      (Rat.mul_nonneg (by decide) (Rat.pow_nonneg
        (Rat.mul_nonneg (by decide) (latticeReciprocalConstant_nonnegative z hz))))
      (Rat.le_of_lt (Rat.inv_pos.mpr (Rat.mul_pos hp hp)))
  · intro n
    unfold upperWeightSixTailRate upperWeightSixTailConstant reciprocalSquare
    have hp : 0<((n+1:Nat):Rat) := by exact_mod_cast (show 0<n+1 by omega)
    exact Rat.mul_nonneg
      (Rat.mul_nonneg (by decide) (Rat.pow_nonneg
        (Rat.mul_nonneg (by decide) (latticeReciprocalConstant_nonnegative w hw))))
      (Rat.le_of_lt (Rat.inv_pos.mpr (Rat.mul_pos hp hp)))
  · exact upperWeightSixPrefix_cauchy z hz
  · exact upperWeightSixPrefix_cauchy w hw
  · intro n
    exact upperWeightSixTailBlock_congr z w hz hw he 0 (n+1)

end ComputableAnalysis.ModularForms
