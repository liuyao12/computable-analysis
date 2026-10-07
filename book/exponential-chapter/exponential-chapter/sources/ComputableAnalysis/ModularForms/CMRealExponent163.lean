import ComputableAnalysis.ModularForms.CMNome163

/-! Real-value identification of the actual CM growth exponent. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert

def cmGrowthReal163 : RealRaw :=
  RealRaw.scaleRat 2 (RealRaw.mul GeometricPiRotation.halfPi sqrt163)

theorem cmGrowthReal163_valid : cmGrowthReal163.Valid :=
  RealRaw.scaleRat_valid (r := 2) (RealRaw.mul_valid GeometricPiRotation.halfPi_valid sqrt163_valid)

theorem sqrt163_lower_twelve : (RealRaw.ofRat 12).Le sqrt163 := by
  intro n m
  have hs := sqrtRaw_stage_spec 163 (by unfold sqrtDomain; decide +kernel) m
  exact hs.le_hi_of_sq_le (r := 12) (by decide +kernel)

theorem sqrt163_upper_thirteen : sqrt163.Le (RealRaw.ofRat 13) := by
  intro n m
  have hs := sqrtRaw_stage_spec 163 (by unfold sqrtDomain; decide +kernel) n
  exact hs.lo_le_of_sq_le (r := 13) (by decide +kernel) (by decide +kernel)

private theorem realScale_two (x : RealRaw) (hx : x.Valid) :
    (scaleRat 2 (ofRealRaw x)).Equiv (ofRealRaw (RealRaw.scaleRat 2 x)) := by
  intro n
  apply (compareAt_overlap_iff _ _ n n).mpr
  have ho := RealRaw.interval_order_of_valid x hx n
  simp only [scaleRat,ofRealRaw,QBox.scaleRat,RealRaw.scaleRat,RealRaw.scaleRatCompute,
    if_pos (show (0:Rat)≤2 by decide),QBox.Overlaps,QComplex.le_def]
  have hm := Rat.mul_le_mul_of_nonneg_left ho (show (0:Rat)≤2 by decide)
  constructor <;> constructor <;> (try simp only [Rat.mul_zero]) <;> first | exact hm | exact Rat.le_refl

theorem cmGrowthExponent163_real : cmGrowthExponent163.val.Equiv (ofRealRaw cmGrowthReal163) := by
  have hm := real_embedding_mul GeometricPiRotation.halfPi sqrt163
    GeometricPiRotation.halfPi_valid sqrt163_valid
  have hs := scaleRat_equiv (r := 2) hm
  have he := equiv_trans
    (scaleRat_valid (mul_valid geometricHalfPiRealScalar.property sqrt163Complex_valid))
    (scaleRat_valid (ofRealRaw_valid _ (RealRaw.mul_valid GeometricPiRotation.halfPi_valid sqrt163_valid)))
    (ofRealRaw_valid _ cmGrowthReal163_valid) hs
    (realScale_two _ (RealRaw.mul_valid GeometricPiRotation.halfPi_valid sqrt163_valid))
  have hn : cmGrowthExponent163.val.Equiv
      (scaleRat 2 (mul geometricHalfPiRealScalar.val sqrt163Complex)) := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := cmGrowthExponent163.property)
      (hright := scaleRat_valid (mul_valid geometricHalfPiRealScalar.property sqrt163Complex_valid))
    change -(-ComplexRawQuotient.scaleRat 2
      (ComplexRawQuotient.ofRaw geometricHalfPiRealScalar.val geometricHalfPiRealScalar.property *
        ComplexRawQuotient.ofRaw sqrt163Complex sqrt163Complex_valid)) =
      ComplexRawQuotient.scaleRat 2
      (ComplexRawQuotient.ofRaw geometricHalfPiRealScalar.val geometricHalfPiRealScalar.property *
        ComplexRawQuotient.ofRaw sqrt163Complex sqrt163Complex_valid)
    grind only
  exact equiv_trans cmGrowthExponent163.property
    (scaleRat_valid (mul_valid geometricHalfPiRealScalar.property sqrt163Complex_valid))
    (ofRealRaw_valid _ cmGrowthReal163_valid) hn he

theorem nome_cm163_real_growth_product :
    (mul (nome.eval cmScalar163 cmPoint163_upper).val
      (entireExponentialValue ⟨ofRealRaw cmGrowthReal163,ofRealRaw_valid _ cmGrowthReal163_valid⟩).val).Equiv
      (ofQComplex ⟨-1,0⟩) := by
  have he := entireExponentialValue_congr cmGrowthExponent163
    ⟨ofRealRaw cmGrowthReal163,ofRealRaw_valid _ cmGrowthReal163_valid⟩ cmGrowthExponent163_real
  have hm := mul_equiv (nome.eval cmScalar163 cmPoint163_upper).property
    (nome.eval cmScalar163 cmPoint163_upper).property
    (entireExponentialValue cmGrowthExponent163).property (entireExponentialValue _).property
    (equiv_refl _ (nome.eval cmScalar163 cmPoint163_upper).property) he
  exact equiv_trans (mul_valid (nome.eval cmScalar163 cmPoint163_upper).property (entireExponentialValue _).property)
    (mul_valid (nome.eval cmScalar163 cmPoint163_upper).property (entireExponentialValue cmGrowthExponent163).property)
    (ofQComplex_valid _) (equiv_symm hm) nome_cm163_growth_product

end ComputableAnalysis.ModularForms
