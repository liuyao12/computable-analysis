import ComputableAnalysis.ModularForms.PairedGlobalReflectionReciprocals
import ComputableAnalysis.ModularForms.PairedGlobalOffPolePrefixes

/-! Reflection of the actual finite paired terms and symmetric prefixes. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

theorem globalOffPoleIntegerReciprocalClass_reflection (z : Scalar) (hz : pairedOffPoleDomain z) (k : Int) :
    globalOffPoleIntegerReciprocalClass (pairedReflectionMap.eval z trivial)
      (pairedOffPoleDomain_reflection z hz) k = -globalOffPoleIntegerReciprocalClass z hz (-k) := by
  have h := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := (globalOffPoleIntegerReciprocal (pairedReflectionMap.eval z trivial)
      (pairedOffPoleDomain_reflection z hz) k).property)
    (hright := neg_valid (globalOffPoleIntegerReciprocal z hz (-k)).property)
    (globalOffPoleIntegerReciprocal_reflection z hz k)
  rw [ComplexRawQuotient.ofRaw_neg _ (globalOffPoleIntegerReciprocal z hz (-k)).property] at h
  exact h

theorem pairedFullTerm_reflection (z : Scalar) (hz : pairedOffPoleDomain z) (n : Nat) :
    (pairedFullTerm (pairedReflectionMap.eval z trivial) (pairedOffPoleDomain_reflection z hz).2 n).val.Equiv
      (neg (pairedFullTerm z hz.2 n).val) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (pairedFullTerm (pairedReflectionMap.eval z trivial)
      (pairedOffPoleDomain_reflection z hz).2 n).property)
    (hright := neg_valid (pairedFullTerm z hz.2 n).property)
  rw [ComplexRawQuotient.ofRaw_neg _ (pairedFullTerm z hz.2 n).property]
  rw [globalOffPoleFullTerm_class _ (pairedOffPoleDomain_reflection z hz),globalOffPoleFullTerm_class z hz]
  rw [globalOffPoleIntegerReciprocalClass_reflection z hz,globalOffPoleIntegerReciprocalClass_reflection z hz]
  simp only [Int.neg_neg]
  grind only

theorem globalOffPoleSymmetricPrefix_reflection (z : Scalar) (hz : pairedOffPoleDomain z) (N : Nat) :
    (globalOffPoleSymmetricPrefix (pairedReflectionMap.eval z trivial)
      (pairedOffPoleDomain_reflection z hz) N).Equiv (neg (globalOffPoleSymmetricPrefix z hz N)) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := globalOffPoleSymmetricPrefix_valid _ (pairedOffPoleDomain_reflection z hz) N)
    (hright := neg_valid (globalOffPoleSymmetricPrefix_valid z hz N))
  rw [ComplexRawQuotient.ofRaw_neg _ (globalOffPoleSymmetricPrefix_valid z hz N)]
  rw [globalOffPoleSymmetricPrefix_class,globalOffPoleSymmetricPrefix_class]
  induction N with
  | zero =>
    change globalOffPoleIntegerReciprocalClass _ _ 0 = -globalOffPoleIntegerReciprocalClass z hz 0
    simpa only [Int.neg_zero] using globalOffPoleIntegerReciprocalClass_reflection z hz 0
  | succ N ih =>
    simp only [symmetricLatticeSum] at ih ⊢
    rw [globalOffPoleIntegerReciprocalClass_reflection z hz,globalOffPoleIntegerReciprocalClass_reflection z hz]
    simp only [Int.neg_neg]
    grind only

end ComputableAnalysis.ModularForms
