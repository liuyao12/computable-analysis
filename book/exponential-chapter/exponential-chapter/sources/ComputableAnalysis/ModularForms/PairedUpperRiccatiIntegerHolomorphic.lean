import ComputableAnalysis.ModularForms.PairedUpperRiccatiIntegerAgreement

/-! Local holomorphicity of the canonical Riccati expression at all integer charts. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

def pairedIntegerRiccatiUpperDomain (k : Int) (z : Scalar) : Prop :=
  InUpperHalfPlane z.val ∧ (pairedIntegerRiccatiExtensionMap k).domain z

def pairedIntegerRiccatiUpperOpenData (k : Int) :
    ScalarTopology.OpenData (pairedIntegerRiccatiUpperDomain k) where
  invariant z w he := and_congr (pairedPartialFractionMap.domain_congr z w he)
    ((pairedIntegerRiccatiExtensionMap k).domain_congr z w he)
  radius z hz := minRadius (pairedPartialFractionMap_holomorphic.openDomain.radius z hz.1)
    ((pairedIntegerRiccatiExtensionMap_holomorphic k).openDomain.radius z hz.2)
  inside a ha z hd :=
    ⟨pairedPartialFractionMap_holomorphic.openDomain.inside a ha.1 z (hd.mono (minRadius_left _ _)),
      (pairedIntegerRiccatiExtensionMap_holomorphic k).openDomain.inside a ha.2 z (hd.mono (minRadius_right _ _))⟩

def pairedUpperRiccatiIntegerLocalMap (k : Int) : DomainFunctions.Map :=
  onDomain pairedUpperRiccatiMap (pairedIntegerRiccatiUpperOpenData k).invariant (fun _ hz => hz.1)

def pairedUpperRiccatiIntegerLocalMap_holomorphic (k : Int) :
    Holomorphic (pairedUpperRiccatiIntegerLocalMap k) :=
  (pairedIntegerRiccatiExtensionMap_holomorphic k).transfer (pairedUpperRiccatiIntegerLocalMap k)
    (fun _ hz => hz.2)
    ⟨(pairedIntegerRiccatiUpperOpenData k).radius,(pairedIntegerRiccatiUpperOpenData k).inside⟩
    (fun z hz => equiv_symm (pairedUpperRiccati_integer_extension_agreement k z
      ⟨hz.2.1,hz.2.2,upperScalar_nonzero (integerShiftScalar z (-k))
        (integerShiftScalar_upper z hz.1 (-k))⟩ hz.1))

end ComputableAnalysis.ModularForms
