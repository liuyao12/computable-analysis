import ComputableAnalysis.ModularForms.PairedRiccatiLargeSquareDecay

/-! Holomorphic squared-kernel integrands about arbitrary represented centers. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

def pairedCenterTranslationMap (a : Scalar) : DomainFunctions.Map :=
  affine a ⟨one,ofQComplex_valid _⟩

def pairedCenterTranslationMap_holomorphic (a : Scalar) :
    Holomorphic (pairedCenterTranslationMap a) :=
  affine_holomorphic a ⟨one,ofQComplex_valid _⟩

def pairedCenteredEntireRiccatiMap (a : Scalar) : DomainFunctions.Map :=
  compose pairedEntireRiccatiMap (pairedCenterTranslationMap a)

noncomputable def pairedCenteredEntireRiccatiMap_holomorphic (a : Scalar) :
    Holomorphic (pairedCenteredEntireRiccatiMap a) :=
  pairedEntireRiccatiMap_holomorphic.compose (pairedCenterTranslationMap_holomorphic a)

def pairedSquaredReciprocalMap : DomainFunctions.Map :=
  productOn ReciprocalHolomorphic.function ReciprocalHolomorphic.function (fun _ h => h)

def pairedSquaredReciprocalMap_holomorphic : Holomorphic pairedSquaredReciprocalMap :=
  ReciprocalHolomorphic.holomorphic.productOn ReciprocalHolomorphic.holomorphic (fun _ h => h)

def pairedRiccatiCauchyIntegrandMap (a : Scalar) : DomainFunctions.Map :=
  productOn pairedSquaredReciprocalMap (pairedCenteredEntireRiccatiMap a)
    (fun _ _ => ⟨trivial,trivial⟩)

noncomputable def pairedRiccatiCauchyIntegrandMap_holomorphic (a : Scalar) :
    Holomorphic (pairedRiccatiCauchyIntegrandMap a) :=
  pairedSquaredReciprocalMap_holomorphic.productOn (pairedCenteredEntireRiccatiMap_holomorphic a)
    (fun _ _ => ⟨trivial,trivial⟩)

theorem pairedRiccatiCauchyIntegrandMap_domain (a z : Scalar) :
    (pairedRiccatiCauchyIntegrandMap a).domain z ↔ NonzeroBoxSearch.Nonzero z :=
  Iff.rfl

end ComputableAnalysis.ModularForms
