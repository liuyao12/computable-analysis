import ComputableAnalysis.ModularForms.RationalRepresentedReciprocalAgreement

/-! Exact agreement of the holomorphic integrand with rational contour kernels. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

theorem pairedCenterTranslationMap_eval (a z : Scalar) :
    ((pairedCenterTranslationMap a).eval z trivial).val.Equiv (add a.val z.val) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := ((pairedCenterTranslationMap a).eval z trivial).property)
    (hright := add_valid a.property z.property)
  let A := ComplexRawQuotient.ofRaw a.val a.property
  let Z := ComplexRawQuotient.ofRaw z.val z.property
  change A+1*Z=A+Z
  grind only

theorem pairedRiccatiCauchyIntegrandMap_rational_agreement (a : Scalar) (q : QComplex)
    (hq : QComplex.normSq q≠0)
    (hz : (pairedRiccatiCauchyIntegrandMap a).domain ⟨ofQComplex q,ofQComplex_valid _⟩) :
    ((pairedRiccatiCauchyIntegrandMap a).eval ⟨ofQComplex q,ofQComplex_valid _⟩ hz).val.Equiv
      (mul (pairedEntireRiccatiMap.eval
        ⟨add a.val (ofQComplex q),add_valid a.property (ofQComplex_valid _)⟩ trivial).val
        (mul (ofQComplex (RationalReciprocal.inverse q))
          (ofQComplex (RationalReciprocal.inverse q)))) := by
  let z : Scalar := ⟨ofQComplex q,ofQComplex_valid _⟩
  let t : Scalar := ⟨add a.val z.val,add_valid a.property z.property⟩
  have hi := representedInverse_rational_agreement q hq hz
  have hv := pairedEntireRiccatiMap.eval_congr ((pairedCenterTranslationMap a).eval z trivial)
    t trivial trivial (pairedCenterTranslationMap_eval a z)
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := ((pairedRiccatiCauchyIntegrandMap a).eval z hz).property)
    (hright := mul_valid (pairedEntireRiccatiMap.eval t trivial).property
      (mul_valid (ofQComplex_valid _) (ofQComplex_valid _)))
  have hI := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := (RepresentedReciprocal.inverse z hz).property) (hright := ofQComplex_valid _) hi
  have hV := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := (pairedEntireRiccatiMap.eval ((pairedCenterTranslationMap a).eval z trivial) trivial).property)
    (hright := (pairedEntireRiccatiMap.eval t trivial).property) hv
  let I := ComplexRawQuotient.ofRaw (RepresentedReciprocal.inverse z hz).val (RepresentedReciprocal.inverse z hz).property
  let J := ComplexRawQuotient.ofRaw (ofQComplex (RationalReciprocal.inverse q)) (ofQComplex_valid _)
  let V := ComplexRawQuotient.ofRaw
    (pairedEntireRiccatiMap.eval ((pairedCenterTranslationMap a).eval z trivial) trivial).val (pairedEntireRiccatiMap.eval ((pairedCenterTranslationMap a).eval z trivial) trivial).property
  let W := ComplexRawQuotient.ofRaw (pairedEntireRiccatiMap.eval t trivial).val (pairedEntireRiccatiMap.eval t trivial).property
  change (I*I)*V=W*(J*J)
  change I=J at hI
  change V=W at hV
  rw [hI,hV]
  grind only

end ComputableAnalysis.ModularForms
