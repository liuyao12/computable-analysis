import ComputableAnalysis.ModularForms.IntegerBoundaryBound
import ComputableAnalysis.ModularForms.IntegerReciprocalTranslation

/-! Transfer the concrete boundary bounds to the actual integer-indexed reciprocal family. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

theorem integerShiftScalar_translate (z : Scalar) (k : Int) :
    (integerShiftScalar z k).val.Equiv (translate (k:Rat) z.val) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (integerShiftScalar z k).property) (hright := translate_valid _ z.property)
  change ComplexRawQuotient.ofRaw (integerAffine 1 k z.val) _ =
    ComplexRawQuotient.ofRaw z.val z.property + ComplexRawQuotient.ofQComplex ⟨(k:Rat),0⟩
  rw [integerAffine_class,integer_constant]
  grind only

theorem integerShiftScalar_plus (z : Scalar) (n : Nat) :
    (integerShiftScalar z (n:Int)).val.Equiv (pairedPlus z (boundaryIntegerScalar n)).val := by
  simpa only [Rat.intCast_natCast,translate,pairedPlus,boundaryIntegerScalar] using integerShiftScalar_translate z (n:Int)

theorem integerShiftScalar_minus (z : Scalar) (n : Nat) :
    (integerShiftScalar z (-(n:Int))).val.Equiv (pairedMinus z (boundaryIntegerScalar n)).val := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (integerShiftScalar z (-(n:Int))).property)
    (hright := (pairedMinus z (boundaryIntegerScalar n)).property)
  have h := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := (integerShiftScalar z (-(n:Int))).property)
    (hright := translate_valid _ z.property) (integerShiftScalar_translate z (-(n:Int)))
  rw [h]
  change ComplexRawQuotient.ofRaw z.val z.property +
    ComplexRawQuotient.ofQComplex ⟨((-(n:Int)):Rat),0⟩ =
    ComplexRawQuotient.ofRaw z.val z.property - ComplexRawQuotient.ofQComplex ⟨(n:Rat),0⟩
  have hneg := integer_constant (-(n:Int))
  simp only [Rat.intCast_neg, Rat.intCast_natCast] at hneg
  simp only [Rat.intCast_natCast]
  rw [hneg]
  have hc := integer_constant (n:Int)
  simp only [Rat.intCast_natCast] at hc
  rw [hc]
  grind only

theorem upperIntegerReciprocal_plus_bound (z : Scalar) (hz : InUpperHalfPlane z.val)
    (R : Rat) (hR : 0≤R) (hsmall : Small z.val R) (n : Nat) (hn : 0<n)
    (hlarge : 16*R*R≤pairedIntegerSquare n) (hRn : R≤(n:Rat)) :
    Small (upperIntegerReciprocal z hz (n:Int)).val (16*(1/(n:Rat))) := by
  have he := RepresentedReciprocal.inverse_congr
    (pairedPlus z (boundaryIntegerScalar n)) (integerShiftScalar z (n:Int))
    (upperShiftPlus_nonzero z hz (n:Rat)) (upperScalar_nonzero _ (integerShiftScalar_upper z hz (n:Int)))
    (equiv_symm (integerShiftScalar_plus z n))
  exact Small.congr (RepresentedReciprocal.inverse (pairedPlus z (boundaryIntegerScalar n))
    (upperShiftPlus_nonzero z hz (n:Rat))).property (upperIntegerReciprocal z hz (n:Int)).property he
    ((integerBoundaryPlus_bound z hz R hR hsmall n hn hlarge).mono (integerBoundaryRate_le R n hn hRn))

theorem upperIntegerReciprocal_minus_bound (z : Scalar) (hz : InUpperHalfPlane z.val)
    (R : Rat) (hR : 0≤R) (hsmall : Small z.val R) (n : Nat) (hn : 0<n)
    (hlarge : 16*R*R≤pairedIntegerSquare n) (hRn : R≤(n:Rat)) :
    Small (upperIntegerReciprocal z hz (-(n:Int))).val (16*(1/(n:Rat))) := by
  have he := RepresentedReciprocal.inverse_congr
    (pairedMinus z (boundaryIntegerScalar n)) (integerShiftScalar z (-(n:Int)))
    (upperShiftMinus_nonzero z hz (n:Rat)) (upperScalar_nonzero _ (integerShiftScalar_upper z hz (-(n:Int))))
    (equiv_symm (integerShiftScalar_minus z n))
  exact Small.congr (RepresentedReciprocal.inverse (pairedMinus z (boundaryIntegerScalar n))
    (upperShiftMinus_nonzero z hz (n:Rat))).property (upperIntegerReciprocal z hz (-(n:Int))).property he
    ((integerBoundaryMinus_bound z hz R hR hsmall n hn hlarge).mono (integerBoundaryRate_le R n hn hRn))

end ComputableAnalysis.ModularForms
