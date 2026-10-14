import ComputableAnalysis.ModularForms.CMFiniteSquares163

/-! Multiplicity control for the explicit finite CM lattice enumerations. -/
namespace ComputableAnalysis.ModularForms.QuadraticOrder163

theorem shellPoints_nodup (r : Nat) : (shellPoints r).Nodup := by
  apply List.Pairwise.map (shellPoint r) _ (List.nodup_finRange (8*r))
  intro i j hij he
  exact hij (shellPoint_injective r i j he)

theorem squarePoints_succ (N : Nat) : squarePoints (N+1)=squarePoints N++shellPoints (N+1) := by
  simp only [squarePoints,List.range_succ,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil]

theorem squarePoints_nodup (N : Nat) : (squarePoints N).Nodup := by
  induction N with
  | zero => exact List.nodup_nil
  | succ N ih =>
    rw [squarePoints_succ]
    apply List.nodup_append.mpr
    refine ⟨ih,shellPoints_nodup _,?_⟩
    intro a ha b hb he
    have h1 := (mem_squarePoints a N).mp ha
    have h2 := (mem_shellPoints b (N+1)).mp hb
    subst b
    omega

theorem conjugate_squarePoints_nodup (N : Nat) : ((squarePoints N).map conjugate).Nodup := by
  apply List.Pairwise.map conjugate _ (squarePoints_nodup N)
  intro u v huv he
  have h := congrArg conjugate he
  simp only [conjugate_involution] at h
  exact huv h

end ComputableAnalysis.ModularForms.QuadraticOrder163
