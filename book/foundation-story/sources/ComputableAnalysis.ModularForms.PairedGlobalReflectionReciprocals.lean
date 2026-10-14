import ComputableAnalysis.ModularForms.PairedGlobalOffPoleIntegerDomain
import ComputableAnalysis.ModularForms.PairedReflectedRiccatiIntegerAgreement

/-! Exact reflection laws for the actual global integer reciprocal family. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

theorem reflectedScalar_inverse_identity (z w : Scalar) (hz : NonzeroBoxSearch.Nonzero z)
    (he : w.val.Equiv (neg z.val)) :
    (mul w.val (neg (RepresentedReciprocal.inverse z hz).val)).Equiv (ofQComplex QComplex.one) := by
  have hi := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid z.property (RepresentedReciprocal.inverse z hz).property)
    (hright := ofQComplex_valid _) (RepresentedReciprocal.mul_inverse z hz)
  have hw := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := w.property)
    (hright := neg_valid z.property) he
  rw [ComplexRawQuotient.ofRaw_neg _ z.property] at hw
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := mul_valid w.property (neg_valid (RepresentedReciprocal.inverse z hz).property))
    (hright := ofQComplex_valid _)
  change ComplexRawQuotient.ofRaw w.val w.property *
    ComplexRawQuotient.ofRaw (neg (RepresentedReciprocal.inverse z hz).val)
      (neg_valid (RepresentedReciprocal.inverse z hz).property) = 1
  change ComplexRawQuotient.ofRaw z.val z.property *
    ComplexRawQuotient.ofRaw (RepresentedReciprocal.inverse z hz).val
      (RepresentedReciprocal.inverse z hz).property = 1 at hi
  rw [ComplexRawQuotient.ofRaw_neg _ (RepresentedReciprocal.inverse z hz).property]
  rw [hw]
  grind only

theorem reflectedScalar_nonzero (z w : Scalar) (hz : NonzeroBoxSearch.Nonzero z)
    (he : w.val.Equiv (neg z.val)) : NonzeroBoxSearch.Nonzero w :=
  RepresentedReciprocal.nonzero_of_inverse w
    ⟨neg (RepresentedReciprocal.inverse z hz).val,neg_valid (RepresentedReciprocal.inverse z hz).property⟩
    (reflectedScalar_inverse_identity z w hz he)

theorem reflectedScalar_inverse (z w : Scalar) (hz : NonzeroBoxSearch.Nonzero z)
    (hw : NonzeroBoxSearch.Nonzero w) (he : w.val.Equiv (neg z.val)) :
    (RepresentedReciprocal.inverse w hw).val.Equiv (neg (RepresentedReciprocal.inverse z hz).val) :=
  RepresentedReciprocal.inverse_unique w hw
    ⟨neg (RepresentedReciprocal.inverse z hz).val,neg_valid (RepresentedReciprocal.inverse z hz).property⟩
    (reflectedScalar_inverse_identity z w hz he)

theorem pairedReflection_shift_argument (z : Scalar) (k : Int) :
    (integerShiftScalar (pairedReflectionMap.eval z trivial) k).val.Equiv
      (neg (integerShiftScalar z (-k)).val) := by
  have hs := pairedReflection_integerShift z (-k)
  have hn := pairedReflectionMap_eval (integerShiftScalar z (-k))
  have hss : (pairedReflectionMap.eval (integerShiftScalar z (-k)) trivial).val.Equiv
      (integerShiftScalar (pairedReflectionMap.eval z trivial) k).val := by
    simpa only [Int.neg_neg] using hs
  exact equiv_trans (integerShiftScalar (pairedReflectionMap.eval z trivial) k).property
    (pairedReflectionMap.eval (integerShiftScalar z (-k)) trivial).property
    (neg_valid (integerShiftScalar z (-k)).property) (equiv_symm hss) hn

theorem pairedOffPoleDomain_reflection (z : Scalar) (hz : pairedOffPoleDomain z) :
    pairedOffPoleDomain (pairedReflectionMap.eval z trivial) := by
  apply pairedOffPoleDomain_of_integer_nonzero
  intro k
  exact reflectedScalar_nonzero (integerShiftScalar z (-k))
    (integerShiftScalar (pairedReflectionMap.eval z trivial) k)
    (pairedOffPoleDomain_integer_nonzero z hz (-k)) (pairedReflection_shift_argument z k)

theorem globalOffPoleIntegerReciprocal_reflection (z : Scalar) (hz : pairedOffPoleDomain z) (k : Int) :
    (globalOffPoleIntegerReciprocal (pairedReflectionMap.eval z trivial)
      (pairedOffPoleDomain_reflection z hz) k).val.Equiv
      (neg (globalOffPoleIntegerReciprocal z hz (-k)).val) :=
  reflectedScalar_inverse _ _ _ _ (pairedReflection_shift_argument z k)

end ComputableAnalysis.ModularForms
