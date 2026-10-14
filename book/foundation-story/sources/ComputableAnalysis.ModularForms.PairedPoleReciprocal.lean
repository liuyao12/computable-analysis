import ComputableAnalysis.ModularForms.PairedPoleExtension

/-! Executable inverse of the regular pole denominator on a supplied small disk. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

theorem pairedPoleExtension_room (z : Scalar) (hz : LocalODE.interior (1/32) z) :
    pairedPoleExtensionMap.domain z :=
  by
    obtain ⟨r,hr,hrq,hs⟩ := hz
    have hq : (1/32:Rat)≤1/4 := by decide +kernel
    exact ⟨r,hr,by grind only,hs⟩

def pairedPolePerturbation (z : Scalar) (hz : LocalODE.interior (1/32) z) : Scalar :=
  ⟨neg (mul z.val (pairedRegularPartMap.eval z (pairedPoleExtension_room z hz)).val),
    neg_valid (mul_valid z.property (pairedRegularPartMap.eval z (pairedPoleExtension_room z hz)).property)⟩

theorem pairedPolePerturbation_small (z : Scalar) (hz : LocalODE.interior (1/32) z) :
    Small (pairedPolePerturbation z hz).val (1/8) := by
  have hq := LocalODE.interior_bound (1/32) z hz
  have hs := pairedRegularPart_bound z (LocalODE.interior_bound (1/4) z (pairedPoleExtension_room z hz))
    (1/32) (by decide +kernel) (by decide +kernel) hq
  have h := SeriesLimitLaws.small_neg (Small.mul z.property
    (pairedRegularPartMap.eval z (pairedPoleExtension_room z hz)).property
    (by decide +kernel : (0:Rat)≤1/32) (by decide +kernel : (0:Rat)≤32*(1/32)) hq hs)
  exact h.mono (by decide +kernel)

def pairedPoleInverseCandidate (z : Scalar) (hz : LocalODE.interior (1/32) z) : Scalar :=
  ⟨nomeGeometricSum (pairedPolePerturbation z hz) (1/8),
    nomeGeometricSum_valid _ _ (by decide +kernel) (by decide +kernel) (pairedPolePerturbation_small z hz)⟩

theorem pairedPoleInverseCandidate_identity (z : Scalar) (hz : LocalODE.interior (1/32) z) :
    (mul (pairedPoleExtensionMap.eval z (pairedPoleExtension_room z hz)).val
      (pairedPoleInverseCandidate z hz).val).Equiv (ofQComplex QComplex.one) := by
  have h := nomeGeometricSum_inverse (pairedPolePerturbation z hz) (1/8)
    (by decide +kernel) (by decide +kernel) (pairedPolePerturbation_small z hz)
  have he : (pairedPoleExtensionMap.eval z (pairedPoleExtension_room z hz)).val.Equiv
      (sub (ofQComplex QComplex.one) (pairedPolePerturbation z hz).val) := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := (pairedPoleExtensionMap.eval z (pairedPoleExtension_room z hz)).property)
      (hright := sub_valid (ofQComplex_valid _) (pairedPolePerturbation z hz).property)
    let Z := ComplexRawQuotient.ofRaw z.val z.property
    let S := ComplexRawQuotient.ofRaw (pairedRegularPartMap.eval z (pairedPoleExtension_room z hz)).val
      (pairedRegularPartMap.eval z (pairedPoleExtension_room z hz)).property
    change 1+Z*S=1-(-(Z*S))
    grind only
  exact equiv_trans (mul_valid (pairedPoleExtensionMap.eval z (pairedPoleExtension_room z hz)).property
      (pairedPoleInverseCandidate z hz).property)
    (mul_valid (sub_valid (ofQComplex_valid _) (pairedPolePerturbation z hz).property)
      (pairedPoleInverseCandidate z hz).property) (ofQComplex_valid _)
    (mul_equiv (pairedPoleExtensionMap.eval z (pairedPoleExtension_room z hz)).property
      (sub_valid (ofQComplex_valid _) (pairedPolePerturbation z hz).property)
      (pairedPoleInverseCandidate z hz).property (pairedPoleInverseCandidate z hz).property he
      (equiv_refl _ (pairedPoleInverseCandidate z hz).property)) h

theorem pairedPoleExtension_nonzero (z : Scalar) (hz : LocalODE.interior (1/32) z) :
    NonzeroBoxSearch.Nonzero (pairedPoleExtensionMap.eval z (pairedPoleExtension_room z hz)) :=
  RepresentedReciprocal.nonzero_of_inverse _ _ (pairedPoleInverseCandidate_identity z hz)

def pairedPoleReciprocalMap : DomainFunctions.Map where
  domain := LocalODE.interior (1/32)
  eval z hz := RepresentedReciprocal.inverse
    (pairedPoleExtensionMap.eval z (pairedPoleExtension_room z hz)) (pairedPoleExtension_nonzero z hz)
  domain_congr z w he := by
    constructor
    · rintro ⟨r,hr,hrq,hz⟩
      exact ⟨r,hr,hrq,Small.congr z.property w.property he hz⟩
    · rintro ⟨r,hr,hrq,hw⟩
      exact ⟨r,hr,hrq,Small.congr w.property z.property (equiv_symm he) hw⟩
  eval_congr z w hz hw he := RepresentedReciprocal.inverse_congr _ _ _ _
    (pairedPoleExtensionMap.eval_congr z w _ _ he)

def pairedPoleReciprocalMap_holomorphic : Holomorphic pairedPoleReciprocalMap := by
  have h := ReciprocalHolomorphic.holomorphic.compose pairedPoleExtensionMap_holomorphic
  apply h.transfer pairedPoleReciprocalMap
    (fun z hz => ⟨pairedPoleExtension_room z hz,pairedPoleExtension_nonzero z hz⟩)
    ⟨LocalODE.interiorRadius (1/32),LocalODE.interiorRadius_inside (1/32)⟩
  intro z hz
  exact equiv_refl _ (pairedPoleReciprocalMap.eval z hz).property

end ComputableAnalysis.ModularForms
