import ComputableAnalysis.ModularForms.PairedDenominatorAgreement

/-! Bounds for actual reciprocals of literal large paired denominators. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

def pairedLiteralDenominator (z : Scalar) (t : Rat) : Scalar :=
  ⟨sub (mul z.val z.val) (ofQComplex ⟨t,0⟩),
    sub_valid (mul_valid z.property z.property) (ofQComplex_valid _)⟩

def pairedInverseCandidate (z : Scalar) (R c : Rat) (hR : 0≤R) (hc : 0≤c)
    (hz : Small z.val R) (hsmall : c*(2*R*R)≤(1:Rat)/8) : Scalar :=
  ⟨scaleRat (-c) (nomeGeometricSum (pairedNormalizedSquare z c) (1/8)),
    scaleRat_valid (nomeGeometricSum_valid (pairedNormalizedSquare z c) (1/8)
      (by decide +kernel) (by decide +kernel) (pairedNormalizedSquare_eighth z R c hR hc hz hsmall))⟩

theorem pairedInverseCandidate_identity (z : Scalar) (R c t : Rat)
    (hR : 0≤R) (hc : 0≤c) (hz : Small z.val R) (hsmall : c*(2*R*R)≤(1:Rat)/8)
    (hct : t*c=1) :
    (mul (pairedLiteralDenominator z t).val (pairedInverseCandidate z R c hR hc hz hsmall).val).Equiv
      (ofQComplex QComplex.one) := by
  have hd := pairedDenominator_rescaling z c t hct
  have vi := (pairedInverseCandidate z R c hR hc hz hsmall).property
  have vd := scaleRat_valid (r := -t) (nomeDenominator (pairedNormalizedSquare z c)).property
  exact equiv_trans (mul_valid (pairedLiteralDenominator z t).property vi) (mul_valid vd vi)
    (ofQComplex_valid _) (mul_equiv (pairedLiteralDenominator z t).property vd vi vi
      (equiv_symm hd) (equiv_refl _ vi)) (pairedRescaledInverse_identity z R c t hR hc hz hsmall hct)

theorem pairedLiteralDenominator_nonzero (z : Scalar) (R c t : Rat)
    (hR : 0≤R) (hc : 0≤c) (hz : Small z.val R) (hsmall : c*(2*R*R)≤(1:Rat)/8)
    (hct : t*c=1) : NonzeroBoxSearch.Nonzero (pairedLiteralDenominator z t) :=
  RepresentedReciprocal.nonzero_of_inverse _ (pairedInverseCandidate z R c hR hc hz hsmall)
    (pairedInverseCandidate_identity z R c t hR hc hz hsmall hct)

theorem pairedInverseCandidate_bound (z : Scalar) (R c : Rat)
    (hR : 0≤R) (hc : 0≤c) (hz : Small z.val R) (hsmall : c*(2*R*R)≤(1:Rat)/8) :
    Small (pairedInverseCandidate z R c hR hc hz hsmall).val (4*c) := by
  have vs := nomeGeometricSum_valid (pairedNormalizedSquare z c) (1/8)
    (by decide +kernel) (by decide +kernel) (pairedNormalizedSquare_eighth z R c hR hc hz hsmall)
  have he : (neg (scaleRat c (nomeGeometricSum (pairedNormalizedSquare z c) (1/8)))).Equiv
      (pairedInverseCandidate z R c hR hc hz hsmall).val := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := neg_valid (scaleRat_valid vs))
      (hright := (pairedInverseCandidate z R c hR hc hz hsmall).property)
    rw [ComplexRawQuotient.ofRaw_neg _ (scaleRat_valid vs),
      ComplexRawQuotient.ofRaw_scaleRat c _ vs]
    exact ComplexRawQuotient.neg_scaleRat _ _
  exact Small.congr (neg_valid (scaleRat_valid vs))
    (pairedInverseCandidate z R c hR hc hz hsmall).property he
    (pairedRescaledInverse_bound z R c hR hc hz hsmall)

theorem pairedLiteralInverse_bound (z : Scalar) (R c t : Rat)
    (hR : 0≤R) (hc : 0≤c) (hz : Small z.val R) (hsmall : c*(2*R*R)≤(1:Rat)/8)
    (hct : t*c=1) (hd : NonzeroBoxSearch.Nonzero (pairedLiteralDenominator z t)) :
    Small (RepresentedReciprocal.inverse (pairedLiteralDenominator z t) hd).val (4*c) :=
  Small.congr (pairedInverseCandidate z R c hR hc hz hsmall).property
    (RepresentedReciprocal.inverse (pairedLiteralDenominator z t) hd).property
    (equiv_symm (RepresentedReciprocal.inverse_unique _ hd (pairedInverseCandidate z R c hR hc hz hsmall)
      (pairedInverseCandidate_identity z R c t hR hc hz hsmall hct)))
    (pairedInverseCandidate_bound z R c hR hc hz hsmall)

theorem pairedLiteralQuotient_bound (z : Scalar) (R c t : Rat)
    (hR : 0≤R) (hc : 0≤c) (hz : Small z.val R) (hsmall : c*(2*R*R)≤(1:Rat)/8)
    (hct : t*c=1) (hd : NonzeroBoxSearch.Nonzero (pairedLiteralDenominator z t)) :
    Small (mul (add z.val z.val)
      (RepresentedReciprocal.inverse (pairedLiteralDenominator z t) hd).val) (16*R*c) := by
  have h := Small.mul (add_valid z.property z.property)
    (RepresentedReciprocal.inverse (pairedLiteralDenominator z t) hd).property
    (Rat.add_nonneg hR hR) (Rat.mul_nonneg (by decide) hc)
    (LocalODE.small_add hz hz) (pairedLiteralInverse_bound z R c t hR hc hz hsmall hct hd)
  rw [show (2:Rat)*(R+R)*(4*c)=16*R*c by grind only] at h
  exact h

end ComputableAnalysis.ModularForms
