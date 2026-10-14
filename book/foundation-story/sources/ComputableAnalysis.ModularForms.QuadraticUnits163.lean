import ComputableAnalysis.ModularForms.QuadraticOrder163

/-! Classification of the units in the concrete quadratic order. -/
namespace ComputableAnalysis.ModularForms.QuadraticOrder163

private theorem square_nonnegative (v : Int) : 0≤v*v := by
  by_cases hv : 0≤v
  · exact Int.mul_nonneg hv hv
  · exact Int.mul_nonneg_of_nonpos_of_nonpos (by omega) (by omega)

theorem norm_one_coordinates (u : QuadraticOrder163) (hn : norm u=1) :
    u.y=0 ∧ (u.x=1 ∨ u.x= -1) := by
  have hs := principalIntegralForm163.completed_square u.x u.y
  rw [← norm_eq_principal, hn] at hs
  simp only [principalIntegralForm163,Int.mul_one,Int.one_mul] at hs
  have hq := square_nonnegative (2*u.x+u.y)
  have hy : u.y=0 := by
    by_cases hzero : u.y=0
    · exact hzero
    · have hp : 0<u.y*u.y := by
        by_cases hpos : 0<u.y
        · exact Int.mul_pos hpos hpos
        · exact Int.mul_pos_of_neg_of_neg (by omega) (by omega)
      grind
  have hx : u.x*u.x=1 := by unfold norm at hn; rw [hy] at hn; grind
  have hupper : u.x≤1 := by
    by_cases h : u.x≤1
    · exact h
    · have hm := Int.mul_le_mul_of_nonneg_left (show 2≤u.x by omega) (show 0≤u.x by omega)
      grind
  have hlower : -1≤u.x := by
    by_cases h : -1≤u.x
    · exact h
    · have hp : 2≤ -u.x := by omega
      have hm := Int.mul_le_mul_of_nonneg_left hp (show 0≤ -u.x by omega)
      grind
  have hxzero : u.x≠0 := by intro hz; rw [hz] at hx; omega
  exact ⟨hy, by omega⟩

theorem norm_one_iff (u : QuadraticOrder163) :
    norm u=1 ↔ u=one ∨ u=neg one := by
  constructor
  · intro hn
    obtain ⟨hy,hx⟩ := norm_one_coordinates u hn
    rcases hx with hx | hx
    · exact Or.inl (ext hx hy)
    · exact Or.inr (ext hx hy)
  · intro hu
    rcases hu with hu | hu <;> rw [hu] <;> decide

def IsUnit (u : QuadraticOrder163) : Prop := ∃ v, mul u v=one

theorem isUnit_iff_norm_one (u : QuadraticOrder163) : IsUnit u ↔ norm u=1 := by
  constructor
  · rintro ⟨v,hv⟩
    have hp := norm_mul u v
    rw [hv] at hp
    have hu0 : u≠zero := by intro hu; rw [hu] at hp; simp [norm,zero,one] at hp
    have hv0 : v≠zero := by intro hz; rw [hz] at hp; simp [norm,zero,one] at hp
    have hu := norm_positive u hu0
    have hvpos := norm_positive v hv0
    change 1=norm u*norm v at hp
    have hm := Int.mul_le_mul_of_nonneg_left (show 1≤norm v by omega)
      (show 0≤norm u by omega)
    grind
  · intro hn
    refine ⟨conjugate u, ?_⟩
    rw [mul_conjugate,hn]
    rfl

theorem isUnit_iff (u : QuadraticOrder163) : IsUnit u ↔ u=one ∨ u=neg one :=
  (isUnit_iff_norm_one u).trans (norm_one_iff u)

end ComputableAnalysis.ModularForms.QuadraticOrder163
