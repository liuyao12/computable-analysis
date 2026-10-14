import ComputableAnalysis.ModularForms.CMLatticeRadius163

/-! Executable finite lists exhausting the nonzero integral CM lattice. -/
namespace ComputableAnalysis.ModularForms.QuadraticOrder163

def shellPoints (r : Nat) : List QuadraticOrder163 := (List.finRange (8*r)).map (shellPoint r)

theorem mem_shellPoints (u : QuadraticOrder163) (r : Nat) :
    u ∈ shellPoints r ↔ u≠zero ∧ shellRadius u=r := by
  constructor
  · intro h
    obtain ⟨i,_,he⟩ := List.mem_map.mp h
    have hr : 0<r := by have := i.isLt; omega
    subst u
    exact ⟨shellPoint_nonzero r hr i,shellRadius_shellPoint r i⟩
  · intro h
    obtain ⟨i,hi⟩ := shellRadius_enumerated u h.1
    have he := h.2
    subst r
    apply List.mem_map.mpr
    exact ⟨i,List.mem_finRange i,hi⟩

def squarePoints (N : Nat) : List QuadraticOrder163 :=
  (List.range N).flatMap (fun n => shellPoints (n+1))

/-- The explicit list contains exactly the nonzero points of the coordinate square. -/
theorem mem_squarePoints (u : QuadraticOrder163) (N : Nat) :
    u ∈ squarePoints N ↔ u≠zero ∧ shellRadius u≤N := by
  constructor
  · intro h
    obtain ⟨n,hn,hu⟩ := List.mem_flatMap.mp h
    have hm := (mem_shellPoints u (n+1)).mp hu
    have hr := List.mem_range.mp hn
    exact ⟨hm.1,by omega⟩
  · intro h
    apply List.mem_flatMap.mpr
    have hp := shellRadius_positive u h.1
    refine ⟨shellRadius u-1,List.mem_range.mpr (by omega),?_⟩
    apply (mem_shellPoints _ _).mpr
    exact ⟨h.1,by omega⟩

/-- Conjugating every point of a square gives points in the doubled square. -/
theorem conjugate_mem_squarePoints (u : QuadraticOrder163) (N : Nat)
    (h : u ∈ squarePoints N) : conjugate u ∈ squarePoints (2*N) := by
  have hu := (mem_squarePoints u N).mp h
  apply (mem_squarePoints _ _).mpr
  have hb := shellRadius_conjugate_le u
  exact ⟨conjugate_nonzero u hu.1,by omega⟩

/-- The image list has exactly the points whose conjugates belong to the source square. -/
theorem mem_conjugate_squarePoints (u : QuadraticOrder163) (N : Nat) :
    u ∈ (squarePoints N).map conjugate ↔ conjugate u ∈ squarePoints N := by
  constructor
  · intro h
    obtain ⟨v,hv,he⟩ := List.mem_map.mp h
    subst u
    simpa only [conjugate_involution] using hv
  · intro h
    exact List.mem_map.mpr ⟨conjugate u,h,conjugate_involution u⟩

/-- The doubled square and its conjugate image share the original inner square. -/
theorem inner_square_mem_conjugate (u : QuadraticOrder163) (N : Nat)
    (h : u ∈ squarePoints N) : u ∈ (squarePoints (2*N)).map conjugate := by
  apply (mem_conjugate_squarePoints _ _).mpr
  exact conjugate_mem_squarePoints u N h

/-- Unmatched points in either finite list are outside the inner square. -/
theorem square_conjugate_unmatched_radius (u : QuadraticOrder163) (N : Nat)
    (h : (u ∈ squarePoints (2*N) ∧ u ∉ (squarePoints (2*N)).map conjugate) ∨
      (u ∈ (squarePoints (2*N)).map conjugate ∧ u ∉ squarePoints (2*N))) :
    N<shellRadius u := by
  rcases h with h | h
  · have hu := (mem_squarePoints _ _).mp h.1
    by_cases hi : shellRadius u≤N
    · exact False.elim (h.2 (inner_square_mem_conjugate u N
        ((mem_squarePoints _ _).mpr ⟨hu.1,hi⟩)))
    · omega
  · have hc := (mem_conjugate_squarePoints _ _).mp h.1
    have hu := (mem_squarePoints _ _).mp hc
    have hn : u≠zero := by
      intro hz
      subst u
      exact hu.1 rfl
    by_cases hi : shellRadius u≤N
    · exact False.elim (h.2 ((mem_squarePoints _ _).mpr ⟨hn,by omega⟩))
    · omega

end ComputableAnalysis.ModularForms.QuadraticOrder163
