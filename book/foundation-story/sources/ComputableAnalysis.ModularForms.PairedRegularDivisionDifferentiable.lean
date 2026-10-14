import ComputableAnalysis.ModularForms.PairedRegularDivisionRemainderIdentity

/-! Differentiability of the actual regular-division sum through zero. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

def pairedRegularDivisionDerivative (a : Scalar) (ha : pairedRegularDivisionMap.domain a) : Scalar :=
  ⟨pairedRegularDivisionDerivativeValue a ha,pairedRegularDivisionDerivativeValue_valid a ha⟩

def pairedRegularDivisionMap_hasDerivativeAt (a : Scalar) (ha : pairedRegularDivisionMap.domain a) :
    HasDerivativeAt pairedRegularDivisionMap a ha (pairedRegularDivisionDerivative a ha) where
  delta eps := divideRadius eps ⟨4608,by decide +kernel⟩
  estimate eps H z hz hH hd := by
    have h := pairedRegularDivision_sum_remainder_bound a z ha hz H.val (Rat.le_of_lt H.property) hd
    apply h.mono
    have hm := Rat.mul_le_mul_of_nonneg_left hH (show (0:Rat)≤4608 by decide)
    rw [divideRadius_identity eps ⟨4608,by decide +kernel⟩] at hm
    exact Rat.mul_le_mul_of_nonneg_right hm (Rat.le_of_lt H.property)

theorem pairedRegularDivisionDerivativeTerm_congr (a b : Scalar)
    (ha : LocalODE.interior (1/4) a) (hb : LocalODE.interior (1/4) b)
    (he : a.val.Equiv b.val) (n : Nat) :
    (pairedRegularDivisionDerivativeTerm a ha n).val.Equiv
      (pairedRegularDivisionDerivativeTerm b hb n).val := by
  let ia := (pairedSmallDiskLiteralInverseMap n).eval a ha
  let ib := (pairedSmallDiskLiteralInverseMap n).eval b hb
  have hi := (pairedSmallDiskLiteralInverseMap n).eval_congr a b ha hb he
  have hs := mul_equiv (neg_valid (mul_valid ia.property ia.property))
    (neg_valid (mul_valid ib.property ib.property)) (add_valid a.property a.property) (add_valid b.property b.property)
    (neg_equiv (mul_equiv ia.property ib.property ia.property ib.property hi hi)) (add_equiv he he)
  exact add_equiv hs hs

theorem pairedRegularDivisionDerivative_congr (a b : Scalar)
    (ha : pairedRegularDivisionMap.domain a) (hb : pairedRegularDivisionMap.domain b)
    (he : a.val.Equiv b.val) :
    (pairedRegularDivisionDerivative a ha).val.Equiv (pairedRegularDivisionDerivative b hb).val :=
  inverseSquareSeriesValue_congr _ _
    (fun n => (pairedRegularDivisionDerivativeTerm a ha n).property)
    (fun n => (pairedRegularDivisionDerivativeTerm b hb n).property) 64
    (pairedRegularDivisionDerivativeTerm_square_bound a ha)
    (pairedRegularDivisionDerivativeTerm_square_bound b hb)
    (pairedRegularDivisionDerivativeTerm_congr a b ha hb he)

end ComputableAnalysis.ModularForms
