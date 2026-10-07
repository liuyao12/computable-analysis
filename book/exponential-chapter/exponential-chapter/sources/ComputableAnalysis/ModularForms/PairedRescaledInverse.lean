import ComputableAnalysis.ModularForms.PairedNormalization

/-! Actual rescaled inverses for normalized paired denominators. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

theorem pairedRescaledInverse_identity (z : Scalar) (R c t : Rat)
    (hR : 0≤R) (hc : 0≤c) (hz : Small z.val R)
    (hsmall : c*(2*R*R)≤(1:Rat)/8) (hct : t*c=1) :
    (mul (scaleRat (-t) (nomeDenominator (pairedNormalizedSquare z c)).val)
      (scaleRat (-c) (nomeGeometricSum (pairedNormalizedSquare z c) (1/8)))).Equiv
      (ofQComplex QComplex.one) := by
  let q := pairedNormalizedSquare z c
  have hq := pairedNormalizedSquare_eighth z R c hR hc hz hsmall
  have vs := nomeGeometricSum_valid q (1/8) (by decide +kernel) (by decide +kernel) hq
  have hi := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid (nomeDenominator q).property vs) (hright := ofQComplex_valid _)
    (nomeGeometricSum_inverse q (1/8) (by decide +kernel) (by decide +kernel) hq)
  rw [ComplexRawQuotient.ofRaw_mul _ _ (nomeDenominator q).property vs] at hi
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := mul_valid (scaleRat_valid (nomeDenominator q).property) (scaleRat_valid vs))
    (hright := ofQComplex_valid _)
  rw [ComplexRawQuotient.ofRaw_mul _ _ (scaleRat_valid (nomeDenominator q).property) (scaleRat_valid vs),
    ComplexRawQuotient.ofRaw_scaleRat (-t) _ (nomeDenominator q).property,
    ComplexRawQuotient.ofRaw_scaleRat (-c) _ vs,ComplexRawQuotient.scaleRat_mul_scaleRat,hi]
  rw [show (-t)*(-c)=1 by grind only,ComplexRawQuotient.scaleRat_one]

theorem pairedRescaledInverse_bound (z : Scalar) (R c : Rat)
    (hR : 0≤R) (hc : 0≤c) (hz : Small z.val R) (hsmall : c*(2*R*R)≤(1:Rat)/8) :
    Small (neg (scaleRat c (nomeGeometricSum (pairedNormalizedSquare z c) (1/8)))) (4*c) := by
  have h := SeriesLimitLaws.small_neg (LocalODE.small_scale hc
    (pairedNormalizedGeometric_bound z R c hR hc hz hsmall))
  rw [show c*4=4*c by grind only] at h
  exact h

end ComputableAnalysis.ModularForms
