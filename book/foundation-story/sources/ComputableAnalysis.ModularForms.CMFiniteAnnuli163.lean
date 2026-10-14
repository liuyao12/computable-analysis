import ComputableAnalysis.ModularForms.CMFiniteSquaresNodup163

/-! Explicit annulus lists and enumeration of arbitrary finite lattice subsets. -/
namespace ComputableAnalysis.ModularForms.QuadraticOrder163

def annulusPoints (N : Nat) : Nat → List QuadraticOrder163
  | 0 => []
  | k+1 => annulusPoints N k++shellPoints (N+k+1)

theorem mem_annulusPoints (u : QuadraticOrder163) (N k : Nat) :
    u ∈ annulusPoints N k ↔ u≠zero ∧ N<shellRadius u ∧ shellRadius u≤N+k := by
  induction k with
  | zero => simp only [annulusPoints,List.not_mem_nil,false_iff]; omega
  | succ k ih =>
    simp only [annulusPoints,List.mem_append,ih,mem_shellPoints]
    constructor
    · intro h
      rcases h with h|h
      · exact ⟨h.1,h.2.1,by omega⟩
      · exact ⟨h.1,by omega,by omega⟩
    · intro h
      by_cases he : shellRadius u=N+k+1
      · exact Or.inr ⟨h.1,he⟩
      · exact Or.inl ⟨h.1,h.2.1,by omega⟩

theorem annulusPoints_nodup (N k : Nat) : (annulusPoints N k).Nodup := by
  induction k with
  | zero => exact List.nodup_nil
  | succ k ih =>
    apply List.nodup_append.mpr
    refine ⟨ih,shellPoints_nodup _,?_⟩
    intro a ha b hb he
    have h1 := (mem_annulusPoints a N k).mp ha
    have h2 := (mem_shellPoints b (N+k+1)).mp hb
    subst b
    omega

/-- A duplicate-free finite subset can be reindexed as the annulus filtered
by its actual membership, with no sum equality among the hypotheses. -/
theorem annulus_subset_perm (N k : Nat) (us : List QuadraticOrder163) (hu : us.Nodup)
    (hb : ∀ u ∈ us, u≠zero ∧ N<shellRadius u ∧ shellRadius u≤N+k) :
    us.Perm ((annulusPoints N k).filter (fun u => decide (u ∈ us))) := by
  apply (List.perm_ext_iff_of_nodup hu
    (List.Nodup.sublist List.filter_sublist (annulusPoints_nodup N k))).mpr
  intro u
  simp only [List.mem_filter,decide_eq_true_eq]
  constructor
  · intro h
    exact ⟨(mem_annulusPoints u N k).mpr (hb u h),h⟩
  · exact fun h => h.2

def squareUnmatched (N : Nat) : List QuadraticOrder163 :=
  (squarePoints (2*N)).filter
    (fun u => !decide (u ∈ (squarePoints (2*N)).map conjugate))

def conjugateUnmatched (N : Nat) : List QuadraticOrder163 :=
  ((squarePoints (2*N)).map conjugate).filter
    (fun u => !decide (u ∈ squarePoints (2*N)))

theorem squareUnmatched_annulus_perm (N : Nat) :
    (squareUnmatched N).Perm ((annulusPoints N (3*N)).filter
      (fun u => decide (u ∈ squareUnmatched N))) := by
  apply annulus_subset_perm N (3*N) _
    (List.Nodup.sublist List.filter_sublist (squarePoints_nodup (2*N)))
  intro u hu
  have h : u ∈ squarePoints (2*N) ∧ u ∉ (squarePoints (2*N)).map conjugate := by
    simpa [squareUnmatched] using hu
  have hb := (mem_squarePoints _ _).mp h.1
  exact ⟨hb.1,square_conjugate_unmatched_radius u N (Or.inl h),by omega⟩

theorem conjugateUnmatched_annulus_perm (N : Nat) :
    (conjugateUnmatched N).Perm ((annulusPoints N (3*N)).filter
      (fun u => decide (u ∈ conjugateUnmatched N))) := by
  apply annulus_subset_perm N (3*N) _
    (List.Nodup.sublist List.filter_sublist (conjugate_squarePoints_nodup (2*N)))
  intro u hu
  have h : u ∈ (squarePoints (2*N)).map conjugate ∧ u ∉ squarePoints (2*N) := by
    simpa [conjugateUnmatched] using hu
  have hb := (mem_squarePoints _ _).mp ((mem_conjugate_squarePoints _ _).mp h.1)
  have hn : u≠zero := by intro hz; subst u; exact hb.1 rfl
  have hr := shellRadius_le_twice_conjugate u
  exact ⟨hn,square_conjugate_unmatched_radius u N (Or.inr h),by omega⟩

end ComputableAnalysis.ModularForms.QuadraticOrder163
