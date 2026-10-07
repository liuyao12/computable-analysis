import ComputableAnalysis.ModularForms.PairedRegularDivisionDerivativeZero

/-! Quadratic center estimates for the actual regular-division sum. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

theorem pairedRegularDivision_center_difference_bound (a z : Scalar)
    (ha : LocalODE.interior (1/4) a) (hz : LocalODE.interior (1/4) z)
    (he : a.val.Equiv zero) (R : Rat) (hR : 0≤R) (hs : Small z.val R) :
    Small (sub (pairedRegularDivisionMap.eval z hz).val (pairedRegularDivisionMap.eval a ha).val)
      (4608*R*R) := by
  have hzero := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := a.property) (hright := ofQComplex_valid _) he
  have hx : (sub z.val a.val).Equiv z.val := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := sub_valid z.property a.property) (hright := z.property)
    let A := ComplexRawQuotient.ofRaw a.val a.property
    let Z := ComplexRawQuotient.ofRaw z.val z.property
    change A=0 at hzero
    change Z-A=Z
    grind only
  have hd := Small.congr z.property (sub_valid z.property a.property) (equiv_symm hx) hs
  have hb := pairedRegularDivision_sum_remainder_bound a z ha hz R hR hd
  have hdz := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := (pairedRegularDivisionDerivative a ha).property) (hright := ofQComplex_valid _)
    (pairedRegularDivisionDerivative_at_zero a ha he)
  have hr : (SeriesLimitLaws.remainder (pairedRegularDivisionMap.eval z hz).val
      (pairedRegularDivisionMap.eval a ha).val (pairedRegularDivisionDerivative a ha).val (sub z.val a.val)).Equiv
      (sub (pairedRegularDivisionMap.eval z hz).val (pairedRegularDivisionMap.eval a ha).val) := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := SeriesLimitLaws.remainder_valid _ _ _ _ (pairedRegularDivisionMap.eval z hz).property
        (pairedRegularDivisionMap.eval a ha).property (pairedRegularDivisionDerivative a ha).property
        (sub_valid z.property a.property))
      (hright := sub_valid (pairedRegularDivisionMap.eval z hz).property (pairedRegularDivisionMap.eval a ha).property)
    let T := ComplexRawQuotient.ofRaw (pairedRegularDivisionMap.eval z hz).val (pairedRegularDivisionMap.eval z hz).property
    let C := ComplexRawQuotient.ofRaw (pairedRegularDivisionMap.eval a ha).val (pairedRegularDivisionMap.eval a ha).property
    let D := ComplexRawQuotient.ofRaw (pairedRegularDivisionDerivative a ha).val (pairedRegularDivisionDerivative a ha).property
    let X := ComplexRawQuotient.ofRaw (sub z.val a.val) (sub_valid z.property a.property)
    change D=0 at hdz
    change (T-C)-D*X=T-C
    grind only
  exact Small.congr
    (SeriesLimitLaws.remainder_valid _ _ _ _ (pairedRegularDivisionMap.eval z hz).property
      (pairedRegularDivisionMap.eval a ha).property (pairedRegularDivisionDerivative a ha).property
      (sub_valid z.property a.property))
    (sub_valid (pairedRegularDivisionMap.eval z hz).property (pairedRegularDivisionMap.eval a ha).property) hr hb

end ComputableAnalysis.ModularForms
