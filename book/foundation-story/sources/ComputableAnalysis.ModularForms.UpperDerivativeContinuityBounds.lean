import ComputableAnalysis.ModularForms.UpperDerivativeCongruence
import ComputableAnalysis.RiemannHilbert.SeriesLimitLaws

/-! Finite-approximation estimates for continuity of the derivative limits. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

private theorem difference_split (x y p q : Scalar) :
    (sub x.val y.val).Equiv (add (sub x.val p.val) (add (sub p.val q.val) (sub q.val y.val))) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := sub_valid x.property y.property)
    (hright := add_valid (sub_valid x.property p.property)
      (add_valid (sub_valid p.property q.property) (sub_valid q.property y.property)))
  change ComplexRawQuotient.ofRaw x.val x.property + -ComplexRawQuotient.ofRaw y.val y.property =
    (ComplexRawQuotient.ofRaw x.val x.property + -ComplexRawQuotient.ofRaw p.val p.property) +
    ((ComplexRawQuotient.ofRaw p.val p.property + -ComplexRawQuotient.ofRaw q.val q.property) +
      (ComplexRawQuotient.ofRaw q.val q.property + -ComplexRawQuotient.ofRaw y.val y.property))
  grind only

theorem derivativeWeightFourSum_difference_bound
    (a : Scalar) (ha : InUpperHalfPlane a.val) (z : Scalar) (hz : InUpperHalfPlane z.val)
    (hs : Small (sub z.val a.val) (upperRadius a ha).val) (n : Nat) (eps : Rat)
    (hf : Small (sub
      ((upperFiniteMap_holomorphic 4 (QuadraticOrder163.squarePoints (n+1))).derivative z hz).val
      ((upperFiniteMap_holomorphic 4 (QuadraticOrder163.squarePoints (n+1))).derivative a ha).val) eps) :
    Small (sub (derivativeWeightFourSum z hz) (derivativeWeightFourSum a ha))
      (2*localDerivativeWeightFourTailRate a ha n+eps) := by
  let p := (upperFiniteMap_holomorphic 4 (QuadraticOrder163.squarePoints (n+1))).derivative z hz
  let q := (upperFiniteMap_holomorphic 4 (QuadraticOrder163.squarePoints (n+1))).derivative a ha
  have hzTail := derivativeWeightFourSum_local_close_square_derivative a ha z hz hs n
  have haTail := derivativeWeightFourSum_local_close_square_derivative a ha a ha (upperSelf_near a ha) n
  have hneg := SeriesLimitLaws.small_neg haTail
  have he : (neg (sub (derivativeWeightFourSum a ha) q.val)).Equiv
      (sub q.val (derivativeWeightFourSum a ha)) := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := neg_valid (sub_valid (derivativeWeightFourSum_valid a ha) q.property))
      (hright := sub_valid q.property (derivativeWeightFourSum_valid a ha))
    change -(ComplexRawQuotient.ofRaw (derivativeWeightFourSum a ha) (derivativeWeightFourSum_valid a ha) +
      -ComplexRawQuotient.ofRaw q.val q.property) =
      ComplexRawQuotient.ofRaw q.val q.property +
      -ComplexRawQuotient.ofRaw (derivativeWeightFourSum a ha) (derivativeWeightFourSum_valid a ha)
    grind only
  have hrev := Small.congr (neg_valid (sub_valid (derivativeWeightFourSum_valid a ha) q.property))
    (sub_valid q.property (derivativeWeightFourSum_valid a ha)) he hneg
  have hb := LocalODE.small_add hzTail (LocalODE.small_add hf hrev)
  have herr : localDerivativeWeightFourTailRate a ha n+(eps+localDerivativeWeightFourTailRate a ha n)=
      2*localDerivativeWeightFourTailRate a ha n+eps := by grind
  rw [herr] at hb
  exact Small.congr
    (add_valid (sub_valid (derivativeWeightFourSum_valid z hz) p.property)
      (add_valid (sub_valid p.property q.property) (sub_valid q.property (derivativeWeightFourSum_valid a ha))))
    (sub_valid (derivativeWeightFourSum_valid z hz) (derivativeWeightFourSum_valid a ha))
    (equiv_symm (difference_split ⟨_,derivativeWeightFourSum_valid z hz⟩
      ⟨_,derivativeWeightFourSum_valid a ha⟩ p q)) hb

theorem derivativeWeightSixSum_difference_bound
    (a : Scalar) (ha : InUpperHalfPlane a.val) (z : Scalar) (hz : InUpperHalfPlane z.val)
    (hs : Small (sub z.val a.val) (upperRadius a ha).val) (n : Nat) (eps : Rat)
    (hf : Small (sub
      ((upperFiniteMap_holomorphic 6 (QuadraticOrder163.squarePoints (n+1))).derivative z hz).val
      ((upperFiniteMap_holomorphic 6 (QuadraticOrder163.squarePoints (n+1))).derivative a ha).val) eps) :
    Small (sub (derivativeWeightSixSum z hz) (derivativeWeightSixSum a ha))
      (2*localDerivativeWeightSixTailRate a ha n+eps) := by
  let p := (upperFiniteMap_holomorphic 6 (QuadraticOrder163.squarePoints (n+1))).derivative z hz
  let q := (upperFiniteMap_holomorphic 6 (QuadraticOrder163.squarePoints (n+1))).derivative a ha
  have hzTail := derivativeWeightSixSum_local_close_square_derivative a ha z hz hs n
  have haTail := derivativeWeightSixSum_local_close_square_derivative a ha a ha (upperSelf_near a ha) n
  have hneg := SeriesLimitLaws.small_neg haTail
  have he : (neg (sub (derivativeWeightSixSum a ha) q.val)).Equiv
      (sub q.val (derivativeWeightSixSum a ha)) := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := neg_valid (sub_valid (derivativeWeightSixSum_valid a ha) q.property))
      (hright := sub_valid q.property (derivativeWeightSixSum_valid a ha))
    change -(ComplexRawQuotient.ofRaw (derivativeWeightSixSum a ha) (derivativeWeightSixSum_valid a ha) +
      -ComplexRawQuotient.ofRaw q.val q.property) =
      ComplexRawQuotient.ofRaw q.val q.property +
      -ComplexRawQuotient.ofRaw (derivativeWeightSixSum a ha) (derivativeWeightSixSum_valid a ha)
    grind only
  have hrev := Small.congr (neg_valid (sub_valid (derivativeWeightSixSum_valid a ha) q.property))
    (sub_valid q.property (derivativeWeightSixSum_valid a ha)) he hneg
  have hb := LocalODE.small_add hzTail (LocalODE.small_add hf hrev)
  have herr : localDerivativeWeightSixTailRate a ha n+(eps+localDerivativeWeightSixTailRate a ha n)=
      2*localDerivativeWeightSixTailRate a ha n+eps := by grind
  rw [herr] at hb
  exact Small.congr
    (add_valid (sub_valid (derivativeWeightSixSum_valid z hz) p.property)
      (add_valid (sub_valid p.property q.property) (sub_valid q.property (derivativeWeightSixSum_valid a ha))))
    (sub_valid (derivativeWeightSixSum_valid z hz) (derivativeWeightSixSum_valid a ha))
    (equiv_symm (difference_split ⟨_,derivativeWeightSixSum_valid z hz⟩
      ⟨_,derivativeWeightSixSum_valid a ha⟩ p q)) hb

end ComputableAnalysis.ModularForms
