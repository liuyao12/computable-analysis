import ComputableAnalysis.ModularForms.UpperLatticePointTerms
import ComputableAnalysis.ModularForms.CMFilteredPointTerms163
import ComputableAnalysis.ModularForms.UpperMaskedShellLists
import ComputableAnalysis.ModularForms.UpperMaskedTailLists

/-! Filtered lattice-point lists agree with the bounded indexed term lists. -/
namespace ComputableAnalysis.ModularForms
open RiemannHilbert QuadraticOrder163

private theorem finRange_values (n : Nat) : (List.finRange n).map Fin.val=List.range n := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_map,List.getElem_finRange,List.getElem_range]
    rfl

theorem upperFilteredShellPoints_term_list (z : Scalar) (hz : InUpperHalfPlane z.val) (k r : Nat) (hr : 0<r)
    (keep : QuadraticOrder163 → Bool) :
    ((shellPoints r).filter keep).map (upperPointPower z hz k)=
      ((List.range (8*r)).filter (shellKeep r keep)).map (upperShellTerm z hz r hr k) := by
  have hp : (fun i : Fin (8*r) => keep (shellPoint r i))=
      (fun i : Fin (8*r) => shellKeep r keep i.val) := by
    funext i
    simp only [shellKeep,dif_pos i.isLt]
  have ht : (fun i : Fin (8*r) => upperPointPower z hz k (shellPoint r i))=
      (fun i : Fin (8*r) => upperShellTerm z hz r hr k i.val) := by
    funext i
    exact upperPointPower_shellPoint z hz k r hr i
  simp only [shellPoints,List.filter_map,List.map_map,Function.comp_def]
  rw [hp,ht]
  have h := congrArg (fun is : List Nat => (is.filter (shellKeep r keep)).map (upperShellTerm z hz r hr k))
    (finRange_values (8*r))
  simpa only [List.filter_map,List.map_map,Function.comp_def] using h

theorem upperFilteredAnnulus_term_list (z : Scalar) (hz : InUpperHalfPlane z.val) (w N k : Nat) (keep : QuadraticOrder163 → Bool) :
    ((annulusPoints N k).filter keep).map (upperPointPower z hz w)=
      upperMaskedTailTerms z hz (fun r => shellKeep r keep) w N k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [annulusPoints,List.filter_append,List.map_append,upperMaskedTailTerms]
    rw [ih,upperFilteredShellPoints_term_list z hz w (N+k+1) (by omega)]

/-- Every duplicate-free finite subset of an annulus has the proved uniform tail bound. -/
theorem upperFiniteSubsetWeightFour_small (z : Scalar) (hz : InUpperHalfPlane z.val) (N k : Nat) (hN : 0<N)
    (us : List QuadraticOrder163) (hu : us.Nodup)
    (hb : ∀ u ∈ us, u≠zero ∧ N<shellRadius u ∧ shellRadius u≤N+k) :
    FunctionTheory.Small (LocalODE.sum (us.map (upperPointPower z hz 4)))
      (upperWeightFourTailConstant z hz*reciprocalSquare N) := by
  have he := representedSum_reindex (upperPointPower z hz 4) (upperPointPower_valid z hz 4)
    (annulus_subset_perm N k us hu hb)
  rw [upperFilteredAnnulus_term_list z hz] at he
  exact FunctionTheory.Small.congr
    (LocalODE.sum_valid _ (upperMaskedTailTerms_valid z hz _ 4 N k))
    (LocalODE.sum_valid _ (by
      intro zz hzz
      obtain ⟨u,_,rfl⟩ := List.mem_map.mp hzz
      exact upperPointPower_valid z hz 4 u))
    (ComplexRaw.equiv_symm he)
    (upperMaskedWeightFourTail_list_uniform_small z hz _ N k hN)

/-- Every duplicate-free finite subset of an annulus has the proved uniform tail bound. -/
theorem upperFiniteSubsetWeightSix_small (z : Scalar) (hz : InUpperHalfPlane z.val) (N k : Nat) (hN : 0<N)
    (us : List QuadraticOrder163) (hu : us.Nodup)
    (hb : ∀ u ∈ us, u≠zero ∧ N<shellRadius u ∧ shellRadius u≤N+k) :
    FunctionTheory.Small (LocalODE.sum (us.map (upperPointPower z hz 6)))
      (upperWeightSixTailConstant z hz*reciprocalSquare N) := by
  have he := representedSum_reindex (upperPointPower z hz 6) (upperPointPower_valid z hz 6)
    (annulus_subset_perm N k us hu hb)
  rw [upperFilteredAnnulus_term_list z hz] at he
  exact FunctionTheory.Small.congr
    (LocalODE.sum_valid _ (upperMaskedTailTerms_valid z hz _ 6 N k))
    (LocalODE.sum_valid _ (by
      intro zz hzz
      obtain ⟨u,_,rfl⟩ := List.mem_map.mp hzz
      exact upperPointPower_valid z hz 6 u))
    (ComplexRaw.equiv_symm he)
    (upperMaskedWeightSixTail_list_uniform_small z hz _ N k hN)

end ComputableAnalysis.ModularForms
