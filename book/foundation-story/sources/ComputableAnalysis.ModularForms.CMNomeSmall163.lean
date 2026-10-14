import ComputableAnalysis.ModularForms.RealExponentialReality
import ComputableAnalysis.ModularForms.PositiveReciprocalAgreement

/-! An actual represented reciprocal and a first strict disk bound for the CM nome. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

def cmGrowthValue163 : RealRaw := (entireExponentialValue cmGrowthExponent163).val.realPart

def cmNomeMagnitude163 : RealRaw := RealRaw.positiveReciprocal cmGrowthValue163 25

theorem cmNomeMagnitude163_valid : cmNomeMagnitude163.Valid :=
  RealRaw.positiveReciprocal_valid _ _ (realPart_valid (entireExponentialValue cmGrowthExponent163).property)
    (by decide) (fun n => cmGrowthExponential163_lower_twentyFive 0 n)

theorem nome_cm163_reciprocal : (nome.eval cmScalar163 cmPoint163_upper).val.Equiv
    (neg (ofRealRaw cmNomeMagnitude163)) := by
  have hg := equiv_real_embedding (entireExponentialValue cmGrowthExponent163)
    cmGrowthExponential163_imag_zero
  have hi := positiveReciprocal_mul_identity cmGrowthValue163
    (realPart_valid (entireExponentialValue cmGrowthExponent163).property) 25 (by decide)
    cmGrowthExponential163_lower_twentyFive
  have he := real_embedding_mul cmGrowthValue163 cmNomeMagnitude163
    (realPart_valid (entireExponentialValue cmGrowthExponent163).property) cmNomeMagnitude163_valid
  have hunit := ofRealRaw_equiv_of_equiv
    (x := RealRaw.mul cmGrowthValue163 cmNomeMagnitude163) (y := RealRaw.one)
    (RealRaw.mul_valid (realPart_valid (entireExponentialValue cmGrowthExponent163).property) cmNomeMagnitude163_valid)
    (RealRaw.ofRat_valid 1) hi
  have hgr := equiv_trans
    (mul_valid (ofRealRaw_valid _ (realPart_valid (entireExponentialValue cmGrowthExponent163).property))
      (ofRealRaw_valid _ cmNomeMagnitude163_valid))
    (ofRealRaw_valid _ (RealRaw.mul_valid (realPart_valid (entireExponentialValue cmGrowthExponent163).property) cmNomeMagnitude163_valid))
    (ofRealRaw_valid RealRaw.one (RealRaw.ofRat_valid 1)) he hunit
  have hq := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid (nome.eval cmScalar163 cmPoint163_upper).property (entireExponentialValue cmGrowthExponent163).property)
    (hright := ofQComplex_valid _) nome_cm163_growth_product
  have hgv := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := (entireExponentialValue cmGrowthExponent163).property)
    (hright := ofRealRaw_valid _ (realPart_valid (entireExponentialValue cmGrowthExponent163).property)) hg
  have hrv := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid (ofRealRaw_valid _ (realPart_valid (entireExponentialValue cmGrowthExponent163).property))
      (ofRealRaw_valid _ cmNomeMagnitude163_valid)) (hright := ofRealRaw_valid RealRaw.one (RealRaw.ofRat_valid 1)) hgr
  apply ComplexRawQuotient.equiv_of_ofRaw_eq (hleft := (nome.eval cmScalar163 cmPoint163_upper).property)
    (hright := neg_valid (ofRealRaw_valid _ cmNomeMagnitude163_valid))
  let q := ComplexRawQuotient.ofRaw (nome.eval cmScalar163 cmPoint163_upper).val
    (nome.eval cmScalar163 cmPoint163_upper).property
  let g := ComplexRawQuotient.ofRaw (ofRealRaw cmGrowthValue163)
    (ofRealRaw_valid _ (realPart_valid (entireExponentialValue cmGrowthExponent163).property))
  let r := ComplexRawQuotient.ofRaw (ofRealRaw cmNomeMagnitude163) (ofRealRaw_valid _ cmNomeMagnitude163_valid)
  change g*r=1 at hrv
  change q*ComplexRawQuotient.ofRaw (entireExponentialValue cmGrowthExponent163).val
    (entireExponentialValue cmGrowthExponent163).property = ComplexRawQuotient.ofQComplex ⟨-1,0⟩ at hq
  rw [hgv] at hq
  have hneg : ComplexRawQuotient.ofQComplex ⟨-1,0⟩ = -(1:ScalarAlgebra.Value) := rfl
  rw [hneg] at hq
  change q*g= -(1:ScalarAlgebra.Value) at hq
  change q = -r
  grind only

theorem nome_cm163_small : Small (nome.eval cmScalar163 cmPoint163_upper).val (1/25) := by
  have hb : Small (ofRealRaw cmNomeMagnitude163) (1/25) := by
    have hu (n : Nat) := RealRaw.positiveReciprocal_compute_hi_le cmGrowthValue163 25 (by decide) n
    have hn (n : Nat) : 0 ≤ (cmNomeMagnitude163.compute n).lo := by
      have hl := cmGrowthExponential163_lower_twentyFive 0 n
      change (25:Rat) ≤ (cmGrowthValue163.compute n).hi at hl
      have hp : 0 < (cmGrowthValue163.compute n).hi := by grind only
      have he := RealRaw.positiveReciprocal_compute cmGrowthValue163 25 (by decide) n
      change 0 ≤ ((RealRaw.positiveReciprocal cmGrowthValue163 25).compute n).lo
      rw [he]
      change 0 ≤ 1/(cmGrowthValue163.compute n).hi
      rw [Rat.div_def,Rat.one_mul]
      exact Rat.le_of_lt (Rat.inv_pos.mpr hp)
    refine ⟨?_,?_,?_,?_⟩
    · intro n m
      have ho := RealRaw.interval_order_of_valid _ cmNomeMagnitude163_valid m
      have hl := hn m
      change -(1/25:Rat) ≤ (cmNomeMagnitude163.compute m).hi
      have hr : (0:Rat)≤1/25 := by decide +kernel
      grind only
    · intro n m
      have ho := RealRaw.interval_order_of_valid _ cmNomeMagnitude163_valid n
      exact Rat.le_trans ho (hu n)
    · intro n m; change -(1/25:Rat) ≤ 0; decide +kernel
    · intro n m; change (0:Rat) ≤ 1/25; decide +kernel
  exact Small.congr (neg_valid (ofRealRaw_valid _ cmNomeMagnitude163_valid))
    (nome.eval cmScalar163 cmPoint163_upper).property (equiv_symm nome_cm163_reciprocal)
    (SeriesLimitLaws.small_neg hb)

end ComputableAnalysis.ModularForms
