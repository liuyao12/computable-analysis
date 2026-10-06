import ComputableAnalysis.ModularForms.CMLatticePointTerms163
import ComputableAnalysis.ModularForms.CMFiniteConjugationComparison163

/-! Conjugation of finite executable sums at valid represented inputs. -/
namespace ComputableAnalysis.ModularForms
open RiemannHilbert

theorem representedSum_conjugate {α : Type} (f : α → ComplexRaw)
    (hf : ∀ a, (f a).Valid) (as : List α) :
    (ComplexRaw.conj (LocalODE.sum (as.map f))).Equiv
      (LocalODE.sum (as.map (fun a => ComplexRaw.conj (f a)))) := by
  induction as with
  | nil =>
    intro n
    apply (ComplexRaw.compareAt_overlap_iff _ _ n n).mpr
    change (⟨(0:Rat),0⟩ : QComplex) ≤ ⟨0,0⟩ ∧ (⟨(0:Rat),0⟩ : QComplex) ≤ ⟨0,0⟩
    decide +kernel
  | cons a as ih =>
    have ht : (LocalODE.sum (as.map f)).Valid := by
      apply LocalODE.sum_valid
      intro z hz
      obtain ⟨a,_,rfl⟩ := List.mem_map.mp hz
      exact hf a
    have hc : (LocalODE.sum (as.map (fun a => ComplexRaw.conj (f a)))).Valid := by
      apply LocalODE.sum_valid
      intro z hz
      obtain ⟨a,_,rfl⟩ := List.mem_map.mp hz
      exact ComplexRaw.conj_valid _ (hf a)
    have he := RepresentedPolynomial.conj_add
      (⟨f a,hf a⟩ : ComplexCert) (⟨LocalODE.sum (as.map f),ht⟩ : ComplexCert)
    exact ComplexRaw.equiv_trans
      (ComplexRaw.conj_valid _ (ComplexRaw.add_valid (hf a) ht))
      (ComplexRaw.add_valid (ComplexRaw.conj_valid _ (hf a)) (ComplexRaw.conj_valid _ ht))
      (ComplexRaw.add_valid (ComplexRaw.conj_valid _ (hf a)) hc) he
      (ComplexRaw.add_equiv (ComplexRaw.equiv_refl _ (ComplexRaw.conj_valid _ (hf a))) ih)

private theorem sum_map_congr {α : Type} (as : List α) (f g : α → ComplexRaw)
    (he : ∀ a, (f a).Equiv (g a)) :
    (LocalODE.sum (as.map f)).Equiv (LocalODE.sum (as.map g)) := by
  induction as with
  | nil => exact ComplexRaw.equiv_refl _ (ComplexRaw.ofQComplex_valid _)
  | cons a as ih => exact ComplexRaw.add_equiv (he a) ih

namespace QuadraticOrder163

/-- The conjugated square sum is precisely the sum over the conjugated point list. -/
theorem squarePointSum_conjugate (w N : Nat) :
    (ComplexRaw.conj (LocalODE.sum ((squarePoints N).map (pointPower w)))).Equiv
      (LocalODE.sum (((squarePoints N).map conjugate).map (pointPower w))) := by
  have hv (f : QuadraticOrder163 → ComplexRaw) (hf : ∀ u, (f u).Valid) :
      (LocalODE.sum ((squarePoints N).map f)).Valid := by
    apply LocalODE.sum_valid
    intro z hz
    obtain ⟨u,_,rfl⟩ := List.mem_map.mp hz
    exact hf u
  rw [List.map_map]
  exact ComplexRaw.equiv_trans
    (ComplexRaw.conj_valid _ (hv _ (pointPower_valid w)))
    (hv _ (fun u => ComplexRaw.conj_valid _ (pointPower_valid w u)))
    (hv _ (fun u => pointPower_valid w (conjugate u)))
    (representedSum_conjugate (pointPower w) (pointPower_valid w) (squarePoints N))
    (sum_map_congr _ _ _ (pointPower_conjugate w))


theorem squareWeightFour_minus_conjugate_small (N : Nat) (hN : 0<N) :
    FunctionTheory.Small (ComplexRaw.sub
      (LocalODE.sum ((squarePoints (2*N)).map (pointPower 4)))
      (ComplexRaw.conj (LocalODE.sum ((squarePoints (2*N)).map (pointPower 4)))))
      (weightFourTailConstant*reciprocalSquare N+weightFourTailConstant*reciprocalSquare N) := by
  have hv (us : List QuadraticOrder163) : (LocalODE.sum (us.map (pointPower 4))).Valid := by
    apply LocalODE.sum_valid
    intro z hz
    obtain ⟨u,_,rfl⟩ := List.mem_map.mp hz
    exact pointPower_valid 4 u
  exact FunctionTheory.Small.congr
    (ComplexRaw.sub_valid (hv _) (hv _))
    (ComplexRaw.sub_valid (hv _) (ComplexRaw.conj_valid _ (hv _)))
    (FunctionTheory.sub_congr (ComplexRaw.equiv_refl _ (hv _))
      (ComplexRaw.equiv_symm (squarePointSum_conjugate 4 (2*N))))
    (squareWeightFour_conjugate_enumeration_small N hN)

theorem squareWeightSix_minus_conjugate_small (N : Nat) (hN : 0<N) :
    FunctionTheory.Small (ComplexRaw.sub
      (LocalODE.sum ((squarePoints (2*N)).map (pointPower 6)))
      (ComplexRaw.conj (LocalODE.sum ((squarePoints (2*N)).map (pointPower 6)))))
      (weightSixTailConstant*reciprocalSquare N+weightSixTailConstant*reciprocalSquare N) := by
  have hv (us : List QuadraticOrder163) : (LocalODE.sum (us.map (pointPower 6))).Valid := by
    apply LocalODE.sum_valid
    intro z hz
    obtain ⟨u,_,rfl⟩ := List.mem_map.mp hz
    exact pointPower_valid 6 u
  exact FunctionTheory.Small.congr
    (ComplexRaw.sub_valid (hv _) (hv _))
    (ComplexRaw.sub_valid (hv _) (ComplexRaw.conj_valid _ (hv _)))
    (FunctionTheory.sub_congr (ComplexRaw.equiv_refl _ (hv _))
      (ComplexRaw.equiv_symm (squarePointSum_conjugate 6 (2*N))))
    (squareWeightSix_conjugate_enumeration_small N hN)

end QuadraticOrder163
end ComputableAnalysis.ModularForms
