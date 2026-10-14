import ComputableAnalysis.ModularForms.OrderIdeal163

/-! Least positive horizontal element and horizontal divisibility in arbitrary ideals. -/
namespace ComputableAnalysis.ModularForms.OrderIdeal163
open QuadraticOrder163

theorem exists_least_positive_horizontal (I : OrderIdeal163)
    (hn : ∃ u, I.contains u ∧ u≠zero) :
    ∃ A : Int, 0<A ∧ I.contains ⟨A,0⟩ ∧
      ∀ x : Int, 0<x → I.contains ⟨x,0⟩ → A≤x := by
  classical
  obtain ⟨N,hN,hmem,_⟩ := I.nonzero_contains_positive_axes hn
  let P (n : Nat) := 0<n ∧ I.contains ⟨(n:Int),0⟩
  have hex : ∃ n, P n := by
    refine ⟨N.toNat,?_,?_⟩
    · omega
    · have he : (N.toNat:Int)=N := by omega
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
  refine ⟨(k:Int),by omega,hk.2,?_⟩
  intro x hx hxm
  have he : (x.toNat:Int)=x := by omega
  have hp : P x.toNat := ⟨by omega,by rw [he]; exact hxm⟩
  have hle : k≤x.toNat := hkmin _ hp
  omega

theorem horizontal_divisibility (I : OrderIdeal163) (A : Int) (hA : 0<A)
    (hAmem : I.contains ⟨A,0⟩)
    (hmin : ∀ x : Int, 0<x → I.contains ⟨x,0⟩ → A≤x)
    (x : Int) (hx : I.contains ⟨x,0⟩) : A ∣ x := by
  have hr := Int.emod_nonneg x (show A≠0 by omega)
  have hl := Int.emod_lt_of_pos x hA
  have he := Int.mul_ediv_add_emod x A
  have hmem : I.contains ⟨x%A,0⟩ := by
    have hm := I.add_mem _ _ hx (I.neg_mem _ (I.scale_mem _ hAmem (x/A)))
    have hid : add ⟨x,0⟩ (neg (scale (x/A) ⟨A,0⟩))=⟨x%A,0⟩ := by
      apply QuadraticOrder163.ext <;> simp only [add,neg,scale] <;> grind
    rw [hid] at hm
    exact hm
  have hz : x%A=0 := by
    by_cases h : x%A=0
    · exact h
    · have hm := hmin (x%A) (by omega) hmem
      omega
  exact ⟨x/A,by omega⟩

end ComputableAnalysis.ModularForms.OrderIdeal163
