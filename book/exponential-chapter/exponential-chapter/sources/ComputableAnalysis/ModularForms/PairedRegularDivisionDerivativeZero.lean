import ComputableAnalysis.ModularForms.PairedRegularDivisionEven

/-! Exact zero derivative of actual regular division at its center. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

theorem pairedRegularDivisionDerivativeTerm_at_zero (z : Scalar) (hz : LocalODE.interior (1/4) z)
    (he : z.val.Equiv zero) (n : Nat) :
    (pairedRegularDivisionDerivativeTerm z hz n).val.Equiv zero := by
  have hzero := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := z.property) (hright := ofQComplex_valid _) he
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (pairedRegularDivisionDerivativeTerm z hz n).property) (hright := ofQComplex_valid _)
  let Z := ComplexRawQuotient.ofRaw z.val z.property
  let I := ComplexRawQuotient.ofRaw ((pairedSmallDiskLiteralInverseMap n).eval z hz).val
    ((pairedSmallDiskLiteralInverseMap n).eval z hz).property
  change Z=0 at hzero
  change (-(I*I)*(Z+Z))+(-(I*I)*(Z+Z))=0
  grind only

theorem pairedRegularDivisionDerivativePrefix_at_zero (z : Scalar) (hz : LocalODE.interior (1/4) z)
    (he : z.val.Equiv zero) (N : Nat) :
    (ScalarSeries.block (fun n => (pairedRegularDivisionDerivativeTerm z hz n).val) 0 N).Equiv zero := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := ScalarSeries.block_valid _ (fun n => (pairedRegularDivisionDerivativeTerm z hz n).property) 0 N)
    (hright := ofQComplex_valid _)
  rw [ScalarSeries.block_image _ (fun n => (pairedRegularDivisionDerivativeTerm z hz n).property)]
  let f := fun n => ComplexRawQuotient.ofRaw (pairedRegularDivisionDerivativeTerm z hz n).val
    (pairedRegularDivisionDerivativeTerm z hz n).property
  have hf (n : Nat) : f n=0 := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := (pairedRegularDivisionDerivativeTerm z hz n).property) (hright := ofQComplex_valid _)
    (pairedRegularDivisionDerivativeTerm_at_zero z hz he n)
  change FiniteProducts.block f 0 N=0
  simp only [FiniteProducts.block,Nat.zero_add]
  induction N with
  | zero => rfl
  | succ N ih => simp only [FiniteProducts.partialSum.eq_2,ih,hf]; grind only

theorem pairedRegularDivisionDerivative_at_zero (z : Scalar) (hz : LocalODE.interior (1/4) z)
    (he : z.val.Equiv zero) : (pairedRegularDivisionDerivative z hz).val.Equiv zero := by
  have hs : Small (pairedRegularDivisionDerivativeValue z hz) 0 := by
    apply SeriesLimitLaws.small_of_prefix_bound _ (pairedRegularDivisionDerivativeValue_valid z hz)
      (fun N => ScalarSeries.block (fun n => (pairedRegularDivisionDerivativeTerm z hz n).val) 0 (N+1))
      (fun N => ScalarSeries.block_valid _ (fun n => (pairedRegularDivisionDerivativeTerm z hz n).property) 0 (N+1))
      0 (fun N => (64:Rat)*((N+1:Nat):Rat)⁻¹) (pairedReciprocalTail_shrinks 64)
    · exact pairedRegularDivisionDerivativeValue_close z hz
    · intro N
      exact Small.congr (ofQComplex_valid _)
        (ScalarSeries.block_valid _ (fun n => (pairedRegularDivisionDerivativeTerm z hz n).property) 0 (N+1))
        (equiv_symm (pairedRegularDivisionDerivativePrefix_at_zero z hz he (N+1))) (Small.zero (by decide))
  have hd : (sub (pairedRegularDivisionDerivativeValue z hz) zero).Equiv
      (pairedRegularDivisionDerivativeValue z hz) := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := sub_valid (pairedRegularDivisionDerivativeValue_valid z hz) (ofQComplex_valid _))
      (hright := pairedRegularDivisionDerivativeValue_valid z hz)
    change ComplexRawQuotient.ofRaw (pairedRegularDivisionDerivativeValue z hz) (pairedRegularDivisionDerivativeValue_valid z hz) - 0 = ComplexRawQuotient.ofRaw (pairedRegularDivisionDerivativeValue z hz) (pairedRegularDivisionDerivativeValue_valid z hz)
    grind only
  exact SeriesLimitLaws.equiv_of_small_sub_zero _ _
    (Small.congr (pairedRegularDivisionDerivativeValue_valid z hz)
      (sub_valid (pairedRegularDivisionDerivativeValue_valid z hz) (ofQComplex_valid _)) (equiv_symm hd) hs)

end ComputableAnalysis.ModularForms
