import ComputableAnalysis.ModularForms.CMLatticePointTerms163
import ComputableAnalysis.ModularForms.CMMaskedShellList163
import ComputableAnalysis.ModularForms.CMMaskedTailList163

/-! Filtered lattice-point lists agree with the bounded indexed term lists. -/
namespace ComputableAnalysis.ModularForms.QuadraticOrder163
open RiemannHilbert

def shellKeep (r : Nat) (keep : QuadraticOrder163 → Bool) (i : Nat) : Bool :=
  if hi : i<8*r then keep (shellPoint r ⟨i,hi⟩) else false

private theorem finRange_values (n : Nat) : (List.finRange n).map Fin.val=List.range n := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_map,List.getElem_finRange,List.getElem_range]
    rfl

theorem filteredShellPoints_term_list (k r : Nat) (hr : 0<r)
    (keep : QuadraticOrder163 → Bool) :
    ((shellPoints r).filter keep).map (pointPower k)=
      ((List.range (8*r)).filter (shellKeep r keep)).map (shellTerm r hr k) := by
  have hp : (fun i : Fin (8*r) => keep (shellPoint r i))=
      (fun i : Fin (8*r) => shellKeep r keep i.val) := by
    funext i
    simp only [shellKeep,dif_pos i.isLt]
  have ht : (fun i : Fin (8*r) => pointPower k (shellPoint r i))=
      (fun i : Fin (8*r) => shellTerm r hr k i.val) := by
    funext i
    exact pointPower_shellPoint k r hr i
  simp only [shellPoints,List.filter_map,List.map_map,Function.comp_def]
  rw [hp,ht]
  have h := congrArg (fun is : List Nat => (is.filter (shellKeep r keep)).map (shellTerm r hr k))
    (finRange_values (8*r))
  simpa only [List.filter_map,List.map_map,Function.comp_def] using h

theorem filteredAnnulus_term_list (w N k : Nat) (keep : QuadraticOrder163 → Bool) :
    ((annulusPoints N k).filter keep).map (pointPower w)=
      maskedTailTerms (fun r => shellKeep r keep) w N k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [annulusPoints,List.filter_append,List.map_append,maskedTailTerms]
    rw [ih,filteredShellPoints_term_list w (N+k+1) (by omega)]

/-- Every duplicate-free finite subset of an annulus has the proved uniform tail bound. -/
theorem finiteSubsetWeightFour_small (N k : Nat) (hN : 0<N)
    (us : List QuadraticOrder163) (hu : us.Nodup)
    (hb : ∀ u ∈ us, u≠zero ∧ N<shellRadius u ∧ shellRadius u≤N+k) :
    FunctionTheory.Small (LocalODE.sum (us.map (pointPower 4)))
      (weightFourTailConstant*reciprocalSquare N) := by
  have he := representedSum_reindex (pointPower 4) (pointPower_valid 4)
    (annulus_subset_perm N k us hu hb)
  rw [filteredAnnulus_term_list] at he
  exact FunctionTheory.Small.congr
    (LocalODE.sum_valid _ (maskedTailTerms_valid _ 4 N k))
    (LocalODE.sum_valid _ (by
      intro z hz
      obtain ⟨u,_,rfl⟩ := List.mem_map.mp hz
      exact pointPower_valid 4 u))
    (ComplexRaw.equiv_symm he)
    (maskedWeightFourTail_list_uniform_small _ N k hN)

/-- Every duplicate-free finite subset of an annulus has the proved uniform tail bound. -/
theorem finiteSubsetWeightSix_small (N k : Nat) (hN : 0<N)
    (us : List QuadraticOrder163) (hu : us.Nodup)
    (hb : ∀ u ∈ us, u≠zero ∧ N<shellRadius u ∧ shellRadius u≤N+k) :
    FunctionTheory.Small (LocalODE.sum (us.map (pointPower 6)))
      (weightSixTailConstant*reciprocalSquare N) := by
  have he := representedSum_reindex (pointPower 6) (pointPower_valid 6)
    (annulus_subset_perm N k us hu hb)
  rw [filteredAnnulus_term_list] at he
  exact FunctionTheory.Small.congr
    (LocalODE.sum_valid _ (maskedTailTerms_valid _ 6 N k))
    (LocalODE.sum_valid _ (by
      intro z hz
      obtain ⟨u,_,rfl⟩ := List.mem_map.mp hz
      exact pointPower_valid 6 u))
    (ComplexRaw.equiv_symm he)
    (maskedWeightSixTail_list_uniform_small _ N k hN)

end ComputableAnalysis.ModularForms.QuadraticOrder163
