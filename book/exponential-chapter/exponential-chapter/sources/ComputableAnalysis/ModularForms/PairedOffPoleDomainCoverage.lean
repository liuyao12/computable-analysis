import ComputableAnalysis.ModularForms.PairedOffPoleCutoffDerivativeAgreement

/-! Exact pole exclusions and executable coverage by finite-plus-tail disk charts. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions NonzeroBoxSearch

def pairedOffPoleDomain (z : Scalar) : Prop := Nonzero z ∧ PairedSeriesDomain z

theorem pairedOffPoleDomain_congr (z w : Scalar) (he : z.val.Equiv w.val) :
    pairedOffPoleDomain z ↔ pairedOffPoleDomain w :=
  and_congr (nonzero_congr z w he) (pairedSeriesDomain_congr z w he)

theorem integerShiftScalar_zero_equiv (z : Scalar) : (integerShiftScalar z 0).val.Equiv z.val := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (integerShiftScalar z 0).property) (hright := z.property)
  change ComplexRawQuotient.ofRaw (integerAffine 1 0 z.val) _=ComplexRawQuotient.ofRaw z.val z.property
  rw [integerAffine_class]
  grind only

theorem pairedOffPoleAssemblyMap_domain_global (B : Nat) (z : Scalar)
    (hz : (pairedOffPoleAssemblyMap B).domain z) : pairedOffPoleDomain z :=
  ⟨(nonzero_congr _ _ (integerShiftScalar_zero_equiv z)).mp hz.1.2,
    pairedOffPoleAssemblyMap_seriesDomain B z hz⟩

theorem pairedOffPoleAssemblyMap_global_mem (B : Nat) (z : Scalar)
    (hz : pairedOffPoleDomain z) (hq : LocalODE.interior (B:Rat) z) :
    (pairedOffPoleAssemblyMap B).domain z := by
  have hf (N : Nat) : (pairedFiniteOffPoleMap N).domain z := by
    induction N with
    | zero => exact trivial
    | succ N ih =>
      have h := pairedSeriesDomain_factors z hz.2 N
      exact ⟨ih,⟨trivial,(nonzero_congr _ _ (integerShiftScalar_minus z (N+1))).mpr h.1⟩,
        ⟨trivial,(nonzero_congr _ _ (integerShiftScalar_plus z (N+1))).mpr h.2⟩⟩
  exact ⟨⟨trivial,(nonzero_congr _ _ (integerShiftScalar_zero_equiv z)).mpr hz.1⟩,hf (4*B),hq⟩

def pairedOffPoleCanonicalCutoff (z : Scalar) : Nat := pairedInternalBound z+1

theorem pairedOffPoleCanonicalCutoff_interior (z : Scalar) :
    LocalODE.interior (pairedOffPoleCanonicalCutoff z:Rat) z := by
  refine ⟨(pairedInternalBound z:Rat),Rat.natCast_nonneg,?_,pairedInternalBound_small z⟩
  simp only [pairedOffPoleCanonicalCutoff,Rat.natCast_add,show ((1:Nat):Rat)=1 by decide +kernel]
  grind only

def pairedOffPoleCanonicalCutoff_mem (z : Scalar) (hz : pairedOffPoleDomain z) :
    (pairedOffPoleAssemblyMap (pairedOffPoleCanonicalCutoff z)).domain z :=
  pairedOffPoleAssemblyMap_global_mem _ z hz (pairedOffPoleCanonicalCutoff_interior z)

theorem pairedOffPoleDomain_covered (z : Scalar) :
    pairedOffPoleDomain z ↔ ∃ B, (pairedOffPoleAssemblyMap B).domain z := by
  constructor
  · intro hz
    exact ⟨pairedOffPoleCanonicalCutoff z,pairedOffPoleCanonicalCutoff_mem z hz⟩
  · rintro ⟨B,hz⟩
    exact pairedOffPoleAssemblyMap_domain_global B z hz

end ComputableAnalysis.ModularForms
