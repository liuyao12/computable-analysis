import ComputableAnalysis.ModularForms.ModularWordGeneration
import ComputableAnalysis.ModularForms.EntireNomeIntegerPeriodicity
import ComputableAnalysis.ModularForms.NomeLocalInverse
import ComputableAnalysis.ModularForms.NomePeriodicity
import ComputableAnalysis.ModularForms.ActionLaws

/-! Exact agreement of inverse nome charts across every signed integer period.
Their lifted values differ by the integer; no exponential-kernel classification is
assumed to deduce that identity. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions
private def scalarClass (z : Scalar) := ComplexRawQuotient.ofRaw z.val z.property

theorem fractionalLinear_translation (n : Int) (a : Scalar) (ha : InUpperHalfPlane a.val) :
    (fractionalLinear (SL2Z.translation n) a ha).val.Equiv (translate (n:Rat) a.val) := by
  let w : Scalar := ⟨translate (n:Rat) a.val,translate_valid _ a.property⟩
  apply fractionalLinear_unique (SL2Z.translation n) a ha w
  have hd := integerAffine_zero 1 a
  have hn := integerAffine_one n a
  exact equiv_trans (mul_valid (integerAffine_valid 0 1 a.property) w.property)
    (mul_valid (ofQComplex_valid _) w.property) (integerAffine_valid 1 n a.property)
    (mul_equiv (integerAffine_valid 0 1 a.property) (ofQComplex_valid _)
      w.property w.property hd (equiv_refl _ w.property))
    (equiv_trans (mul_valid (ofQComplex_valid _) w.property) w.property
      (integerAffine_valid 1 n a.property) (one_mul_equiv _ w.property) (equiv_symm hn))

theorem fractionalLinear_translation_mem (n : Int) (a : Scalar) (ha : InUpperHalfPlane a.val) :
    InUpperHalfPlane (fractionalLinear (SL2Z.translation n) a ha).val :=
  (upperOpenData.invariant ⟨translate (n:Rat) a.val,translate_valid _ a.property⟩ _
    (equiv_symm (fractionalLinear_translation n a ha))).mp (translate_mem _ ha)

theorem nome_translation_value (n : Int) (a : Scalar) (ha : InUpperHalfPlane a.val) :
    (nome.eval (fractionalLinear (SL2Z.translation n) a ha) (fractionalLinear_translation_mem n a ha)).val.Equiv
      (nome.eval a ha).val := by
  let b := fractionalLinear (SL2Z.translation n) a ha
  let hb := fractionalLinear_translation_mem n a ha
  have he : b.val.Equiv (integerShiftScalar a n).val :=
    equiv_trans b.property (translate_valid _ a.property) (integerShiftScalar a n).property
      (fractionalLinear_translation n a ha) (equiv_symm (integerAffine_one n a))
  have h1 := equiv_symm (entireNomeMap_upper_agreement b hb)
  have h2 := entireNomeMap.eval_congr b (integerShiftScalar a n) (entireNomeMap_mem b) (entireNomeMap_mem _) he
  have h3 := entireNomeMap_period_int a n
  exact equiv_trans (nome.eval b hb).property (entireNomeMap.eval b (entireNomeMap_mem b)).property
    (nome.eval a ha).property h1
    (equiv_trans (entireNomeMap.eval b (entireNomeMap_mem b)).property
      (entireNomeMap.eval (integerShiftScalar a n) (entireNomeMap_mem _)).property
      (nome.eval a ha).property h2
      (equiv_trans (entireNomeMap.eval (integerShiftScalar a n) (entireNomeMap_mem _)).property
        (entireNomeMap.eval a (entireNomeMap_mem a)).property (nome.eval a ha).property h3
        (entireNomeMap_upper_agreement a ha)))

theorem nomeLocalLift_translation_domain (n : Int) (a : Scalar) (ha : InUpperHalfPlane a.val) (q : Scalar) :
    (nomeLocalLift (fractionalLinear (SL2Z.translation n) a ha) (fractionalLinear_translation_mem n a ha)).domain q ↔
      (nomeLocalLift a ha).domain q := by
  have h := RelativeLogarithm.domain_congr
    (nome.eval (fractionalLinear (SL2Z.translation n) a ha) (fractionalLinear_translation_mem n a ha)) (nome.eval a ha)
    (nome_nonzero _ _) (nome_nonzero _ _) (nome_translation_value n a ha) q q (equiv_refl _ q.property)
  constructor
  · intro hq; exact ⟨⟨h.mp hq.1.1,trivial⟩,trivial⟩
  · intro hq; exact ⟨⟨h.mpr hq.1.1,trivial⟩,trivial⟩

/-- Lifting through the chart at the translated center changes the result
by exactly the supplied integer on the common nome domain. -/
theorem nomeLocalLift_translation_value (n : Int) (a : Scalar) (ha : InUpperHalfPlane a.val)
    (q : Scalar) (hq : (nomeLocalLift a ha).domain q) :
    ((nomeLocalLift (fractionalLinear (SL2Z.translation n) a ha) (fractionalLinear_translation_mem n a ha)).eval q
      ((nomeLocalLift_translation_domain n a ha q).mpr hq)).val.Equiv
      (translate (n:Rat) ((nomeLocalLift a ha).eval q hq).val) := by
  let b := fractionalLinear (SL2Z.translation n) a ha
  let hb := fractionalLinear_translation_mem n a ha
  let hqb := (nomeLocalLift_translation_domain n a ha q).mpr hq
  have hl := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := ((RelativeLogarithm.function (nome.eval b hb) (nome_nonzero b hb)).eval q hqb.1.1).property)
    (hright := ((RelativeLogarithm.function (nome.eval a ha) (nome_nonzero a ha)).eval q hq.1.1).property)
    (RelativeLogarithm.value_congr _ _ (nome_nonzero b hb) (nome_nonzero a ha)
      (nome_translation_value n a ha) q q hqb.1.1 hq.1.1 (equiv_refl _ q.property))
  have hab := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := b.property)
    (hright := translate_valid (n:Rat) a.property) (fractionalLinear_translation n a ha)
  have hi := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid nomeInverseSlope.property nomeSlope.property) (hright := ofQComplex_valid _)
    (RepresentedReciprocal.inverse_mul nomeSlope nomeSlope_nonzero)
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := ((nomeLocalLift b hb).eval q hqb).property)
    (hright := translate_valid (n:Rat) ((nomeLocalLift a ha).eval q hq).property)
  let R := scalarClass nomeInverseSlope
  let S := scalarClass nomeSlope
  let A := scalarClass a
  let B := scalarClass b
  let L := scalarClass ((RelativeLogarithm.function (nome.eval a ha) (nome_nonzero a ha)).eval q hq.1.1)
  let M := scalarClass ((RelativeLogarithm.function (nome.eval b hb) (nome_nonzero b hb)).eval q hqb.1.1)
  change M=L at hl
  let U := ComplexRawQuotient.ofQComplex ⟨(n:Rat),0⟩
  change B=A+U at hab
  change R*S=1 at hi
  change 0+R*(S*B+1*M)=(0+R*(S*A+1*L))+U
  grind only

end ComputableAnalysis.ModularForms
