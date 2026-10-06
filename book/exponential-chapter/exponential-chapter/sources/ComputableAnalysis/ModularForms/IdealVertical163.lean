import ComputableAnalysis.ModularForms.IdealHorizontal163

/-! Least positive ordinate and ordinate divisibility for arbitrary nonzero ideals. -/
namespace ComputableAnalysis.ModularForms.OrderIdeal163
open QuadraticOrder163

theorem exists_least_positive_ordinate (I : OrderIdeal163)
    (hn : ∃ u, I.contains u ∧ u≠zero) :
    ∃ B d : Int, 0<d ∧ I.contains ⟨B,d⟩ ∧
      ∀ z, I.contains z → 0<z.y → d≤z.y := by
  classical
  obtain ⟨N,hN,_,hmem⟩ := I.nonzero_contains_positive_axes hn
  let P (n : Nat) := 0<n ∧ ∃ B : Int, I.contains ⟨B,(n:Int)⟩
  have hex : ∃ n, P n := by
    refine ⟨N.toNat,by omega,0,?_⟩
    have he : (N.toNat:Int)=N := by omega
    rw [he]
    exact hmem
  have hleast : ∀ n, P n → ∃ k, P k ∧ ∀ m, P m → k≤m := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro hp
      by_cases hsmall : ∃ m, m<n ∧ P m
      · obtain ⟨m,hm,hpm⟩ := hsmall
        exact ih m hm hpm
      · refine ⟨n,hp,?_⟩
        intro m hpm
        by_cases hle : n≤m
        · exact hle
        · exact False.elim (hsmall ⟨m,by omega,hpm⟩)
  obtain ⟨n,hpn⟩ := hex
  obtain ⟨k,hk,hkmin⟩ := hleast n hpn
  obtain ⟨B,hB⟩ := hk.2
  refine ⟨B,(k:Int),by omega,hB,?_⟩
  intro z hz hzy
  have he : (z.y.toNat:Int)=z.y := by omega
  have hp : P z.y.toNat := by
    refine ⟨by omega,z.x,?_⟩
    rw [he]
    exact hz
  have hle := hkmin _ hp
  omega

theorem ordinate_divisibility (I : OrderIdeal163) (B d : Int) (hd : 0<d)
    (hB : I.contains ⟨B,d⟩)
    (hmin : ∀ z, I.contains z → 0<z.y → d≤z.y)
    (z : QuadraticOrder163) (hz : I.contains z) : d ∣ z.y := by
  have hr := Int.emod_nonneg z.y (show d≠0 by omega)
  have hl := Int.emod_lt_of_pos z.y hd
  have he := Int.mul_ediv_add_emod z.y d
  let w := add z (neg (scale (z.y/d) ⟨B,d⟩))
  have hw : I.contains w := I.add_mem _ _ hz (I.neg_mem _ (I.scale_mem _ hB (z.y/d)))
  have hwy : w.y=z.y%d := by simp only [w,add,neg,scale]; grind
  have hre : z.y%d=0 := by
    by_cases h : z.y%d=0
    · exact h
    · have hm := hmin w hw (by rw [hwy]; omega)
      rw [hwy] at hm
      omega
  exact ⟨z.y/d,by omega⟩

end ComputableAnalysis.ModularForms.OrderIdeal163
