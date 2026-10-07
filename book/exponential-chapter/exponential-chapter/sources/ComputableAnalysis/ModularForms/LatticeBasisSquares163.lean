import ComputableAnalysis.ModularForms.LatticeBasisIndices163

/-! Concrete square comparisons for arbitrary determinant-one basis changes. -/
namespace ComputableAnalysis.ModularForms.QuadraticOrder163

theorem basisIndex_inverse_right (g : SL2Z) (u : QuadraticOrder163) :
    basisIndex g (basisIndex (SL2Z.inverse g) u)=u := by
  rw [basisIndex_compose,SL2Z.multiply_inverse,basisIndex_identity]

theorem mem_basis_square (g : SL2Z) (u : QuadraticOrder163) (N : Nat) :
    u ∈ (squarePoints N).map (basisIndex g) ↔ basisIndex (SL2Z.inverse g) u ∈ squarePoints N := by
  constructor
  · intro h
    obtain ⟨v,hv,he⟩ := List.mem_map.mp h
    subst u
    simpa only [basisIndex_inverse] using hv
  · intro h
    exact List.mem_map.mpr ⟨basisIndex (SL2Z.inverse g) u,h,basisIndex_inverse_right g u⟩

def basisComparisonFactor (g : SL2Z) : Nat :=
  1+basisRadiusFactor g+basisRadiusFactor (SL2Z.inverse g)

theorem inner_square_mem_basis_image (g : SL2Z) (N : Nat) (u : QuadraticOrder163)
    (hu : u ∈ squarePoints N) :
    u ∈ (squarePoints (basisComparisonFactor g*N)).map (basisIndex g) := by
  apply (mem_basis_square g u _).mpr
  have h := basisIndex_square_enclosure (SL2Z.inverse g) N u hu
  have hb := (mem_squarePoints _ _).mp h
  have hf : basisRadiusFactor (SL2Z.inverse g)≤basisComparisonFactor g := by
    unfold basisComparisonFactor
    omega
  have hm := Nat.mul_le_mul_right N hf
  exact (mem_squarePoints _ _).mpr ⟨hb.1,by omega⟩

/-- Both finite lists contain the inner square, so unmatched points lie in the tail. -/
theorem basis_square_unmatched_radius (g : SL2Z) (N : Nat) (u : QuadraticOrder163)
    (h : (u ∈ squarePoints (basisComparisonFactor g*N) ∧
      u ∉ (squarePoints (basisComparisonFactor g*N)).map (basisIndex g)) ∨
      (u ∈ (squarePoints (basisComparisonFactor g*N)).map (basisIndex g) ∧
        u ∉ squarePoints (basisComparisonFactor g*N))) : N<shellRadius u := by
  have hf : N≤basisComparisonFactor g*N := by
    have hp : 1≤basisComparisonFactor g := by unfold basisComparisonFactor; omega
    have hm := Nat.mul_le_mul_right N hp
    simpa only [Nat.one_mul] using hm
  rcases h with h|h
  · have hu := (mem_squarePoints _ _).mp h.1
    by_cases hi : shellRadius u≤N
    · exact False.elim (h.2 (inner_square_mem_basis_image g N u
        ((mem_squarePoints _ _).mpr ⟨hu.1,hi⟩)))
    · omega
  · obtain ⟨v,hv,he⟩ := List.mem_map.mp h.1
    have hvn := (mem_squarePoints _ _).mp hv
    have hu : u≠zero := by rw [← he]; exact basisIndex_nonzero g v hvn.1
    by_cases hi : shellRadius u≤N
    · exact False.elim (h.2 ((mem_squarePoints _ _).mpr ⟨hu,by omega⟩))
    · omega

theorem basis_square_union_radius (g : SL2Z) (N : Nat) (u : QuadraticOrder163)
    (h : u ∈ squarePoints (basisComparisonFactor g*N) ∨
      u ∈ (squarePoints (basisComparisonFactor g*N)).map (basisIndex g)) :
    u≠zero ∧ shellRadius u≤basisComparisonFactor g*(basisComparisonFactor g*N) := by
  have hp : 1≤basisComparisonFactor g := by unfold basisComparisonFactor; omega
  have hm := Nat.mul_le_mul_right (basisComparisonFactor g*N) hp
  rcases h with h|h
  · have hb := (mem_squarePoints _ _).mp h
    simp only [Nat.one_mul] at hm
    exact ⟨hb.1,Nat.le_trans hb.2 hm⟩
  · obtain ⟨v,hv,he⟩ := List.mem_map.mp h
    have hb := (mem_squarePoints _ _).mp
      (basisIndex_square_enclosure g (basisComparisonFactor g*N) v hv)
    have hf : basisRadiusFactor g≤basisComparisonFactor g := by
      unfold basisComparisonFactor
      omega
    have hmul := Nat.mul_le_mul_right (basisComparisonFactor g*N) hf
    rw [he] at hb
    exact ⟨hb.1,Nat.le_trans hb.2 hmul⟩

end ComputableAnalysis.ModularForms.QuadraticOrder163
