import ComputableAnalysis.ModularForms.UpperLatticeTermHolomorphic
import ComputableAnalysis.RiemannHilbert.DomainHolomorphicSums
import ComputableAnalysis.ModularForms.RepresentedSumFactor

/-! Holomorphicity of the actual total point evaluator and finite lattice sums. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

def upperPointMap (k : Nat) (u : QuadraticOrder163) : DomainFunctions.Map where
  domain z := InUpperHalfPlane z.val
  eval z hz := ⟨upperPointPower z hz k u,upperPointPower_valid z hz k u⟩
  domain_congr := upperOpenData.invariant
  eval_congr z w hz hw he := by
    unfold upperPointPower
    split
    · rename_i hu
      exact LocalODE.power_congr _ _ (latticeInverse z hz u hu).property
        (latticeInverse w hw u hu).property (latticeInverse_congr z w hz hw u hu he) k
    · exact equiv_refl _ (ofQComplex_valid _)

def upperPointMap_holomorphic (k : Nat) (u : QuadraticOrder163) :
    DomainFunctions.Holomorphic (upperPointMap k u) := by
  by_cases hu : u≠QuadraticOrder163.zero
  · apply (latticePowerMap_holomorphic u hu k).transfer (upperPointMap k u)
      (fun _ hz => hz) ⟨upperRadius,upperRadius_inside⟩
    intro z hz
    change (LocalODE.power (latticeInverse z hz u hu).val k).Equiv (upperPointPower z hz k u)
    simp only [upperPointPower,dif_pos hu]
    exact equiv_refl _ (LocalODE.power_valid _ (latticeInverse z hz u hu).property k)
  · apply (constantOn_holomorphic upperOpenData
      (⟨ComplexRaw.zero,ofQComplex_valid _⟩ : Scalar)).transfer (upperPointMap k u)
      (fun _ hz => hz) ⟨upperRadius,upperRadius_inside⟩
    intro z hz
    change ComplexRaw.zero.Equiv (upperPointPower z hz k u)
    simp only [upperPointPower,dif_neg hu]
    exact equiv_refl _ (ofQComplex_valid _)

private theorem pointList_valid (z : Scalar) (hz : InUpperHalfPlane z.val)
    (k : Nat) (us : List QuadraticOrder163) :
    ∀ t ∈ us.map (upperPointPower z hz k), t.Valid := by
  intro t ht
  obtain ⟨u,_,rfl⟩ := List.mem_map.mp ht
  exact upperPointPower_valid z hz k u

def upperFiniteMap (k : Nat) (us : List QuadraticOrder163) : DomainFunctions.Map where
  domain z := InUpperHalfPlane z.val
  eval z hz := ⟨LocalODE.sum (us.map (upperPointPower z hz k)),
    LocalODE.sum_valid _ (pointList_valid z hz k us)⟩
  domain_congr := upperOpenData.invariant
  eval_congr z w hz hw he := by
    exact representedSum_map_equiv us (upperPointPower z hz k) (upperPointPower w hw k)
      (fun u => (upperPointMap k u).eval_congr z w hz hw he)

def upperFiniteMap_holomorphic (k : Nat) (us : List QuadraticOrder163) :
    DomainFunctions.Holomorphic (upperFiniteMap k us) :=
  match us with
  | [] => by
    apply (constantOn_holomorphic upperOpenData
      (⟨ComplexRaw.zero,ofQComplex_valid _⟩ : Scalar)).transfer (upperFiniteMap k [])
      (fun _ hz => hz) ⟨upperRadius,upperRadius_inside⟩
    intro z hz
    exact equiv_refl _ (ofQComplex_valid _)
  | u::us => by
    have ih := upperFiniteMap_holomorphic k us
    have h := (upperPointMap_holomorphic k u).sumOn ih (fun _ hz => hz)
    apply h.transfer (upperFiniteMap k (u::us)) (fun _ hz => hz) ⟨upperRadius,upperRadius_inside⟩
    intro z hz
    exact equiv_refl _ (add_valid (upperPointPower_valid z hz k u)
      (LocalODE.sum_valid _ (pointList_valid z hz k us)))

end ComputableAnalysis.ModularForms
