import ComputableAnalysis.ModularForms.PairedFiniteOffPole
import ComputableAnalysis.ModularForms.PairedJoinedDerivative

/-! Actual finite-plus-tail lattice evaluators across the real axis off the poles. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

def pairedOffPoleTailMap (B : Nat) : DomainFunctions.Map where
  domain := LocalODE.interior (B:Rat)
  eval z hz := ⟨pairedTailValue z B (LocalODE.interior_bound _ z hz),
    pairedTailValue_valid z B (LocalODE.interior_bound _ z hz)⟩
  domain_congr z w he := ⟨Centered.interior_congr _ z w he,
    Centered.interior_congr _ w z (equiv_symm he)⟩
  eval_congr z w hz hw he := pairedTailValue_congr z w B
    (LocalODE.interior_bound _ z hz) (LocalODE.interior_bound _ w hw) he

def pairedOffPoleAssemblyMap (B : Nat) : DomainFunctions.Map :=
  intersectionSum (integerReciprocalOffPoleMap 0)
    (intersectionSum (pairedFiniteOffPoleMap (4*B)) (pairedOffPoleTailMap B))

def pairedOffPoleAssemblyMap_upper_mem (B : Nat) (z : Scalar)
    (hz : InUpperHalfPlane z.val) (hq : LocalODE.interior (B:Rat) z) :
    (pairedOffPoleAssemblyMap B).domain z :=
  ⟨integerReciprocalOffPoleMap_upper_mem 0 z hz,pairedFiniteOffPoleMap_upper_mem (4*B) z hz,hq⟩

theorem pairedOffPoleAssemblyMap_upper_agreement (B : Nat) (z : Scalar)
    (hz : InUpperHalfPlane z.val) (hq : LocalODE.interior (B:Rat) z) :
    ((pairedOffPoleAssemblyMap B).eval z (pairedOffPoleAssemblyMap_upper_mem B z hz hq)).val.Equiv
      (upperPairedPartialFractionValue z hz) := by
  let hd : (pairedWholeJoinedMap B).domain z := ⟨hz,LocalODE.interior_bound _ z hq⟩
  have he : ((pairedOffPoleAssemblyMap B).eval z (pairedOffPoleAssemblyMap_upper_mem B z hz hq)).val.Equiv
      ((pairedWholeJoinedMap B).eval z hd).val :=
    add_equiv (integerReciprocalOffPoleMap_upper_agreement 0 z hz)
      (add_equiv (pairedFiniteOffPoleMap_upper_agreement (4*B) z hz)
        (equiv_refl _ (pairedTailValue_valid z B hd.2)))
  exact equiv_trans ((pairedOffPoleAssemblyMap B).eval z (pairedOffPoleAssemblyMap_upper_mem B z hz hq)).property
    ((pairedWholeJoinedMap B).eval z hd).property (upperPairedPartialFractionValue_valid z hz)
    he (pairedWholeJoinedMap_eval B z hd)

end ComputableAnalysis.ModularForms
