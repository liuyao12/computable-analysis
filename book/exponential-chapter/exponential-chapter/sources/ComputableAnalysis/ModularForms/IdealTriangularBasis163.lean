import ComputableAnalysis.ModularForms.IdealVertical163

/-! Triangular lattice bases for arbitrary nonzero ideals. -/
namespace ComputableAnalysis.ModularForms.OrderIdeal163
open QuadraticOrder163

theorem triangular_membership (I : OrderIdeal163) (A B d : Int)
    (hA : 0<A) (hd : 0<d) (hAmem : I.contains ⟨A,0⟩) (hBmem : I.contains ⟨B,d⟩)
    (hAmin : ∀ x : Int, 0<x → I.contains ⟨x,0⟩ → A≤x)
    (hdmin : ∀ z, I.contains z → 0<z.y → d≤z.y)
    (z : QuadraticOrder163) :
    I.contains z ↔ ∃ m n : Int, z=⟨A*m+B*n,d*n⟩ := by
  constructor
  · intro hz
    obtain ⟨n,hn⟩ := I.ordinate_divisibility B d hd hBmem hdmin z hz
    have hw : I.contains ⟨z.x-B*n,0⟩ := by
      have hm := I.add_mem _ _ hz (I.neg_mem _ (I.scale_mem _ hBmem n))
      have he : add z (neg (scale n ⟨B,d⟩))=⟨z.x-B*n,0⟩ := by
        apply QuadraticOrder163.ext <;> simp only [add,neg,scale] <;> grind
      rw [he] at hm
      exact hm
    obtain ⟨m,hm⟩ := I.horizontal_divisibility A hA hAmem hAmin (z.x-B*n) hw
    refine ⟨m,n,?_⟩
    apply QuadraticOrder163.ext <;> grind
  · rintro ⟨m,n,hz⟩
    have hm := I.add_mem _ _ (I.scale_mem _ hAmem m) (I.scale_mem _ hBmem n)
    have he : add (scale m ⟨A,0⟩) (scale n ⟨B,d⟩)=⟨A*m+B*n,d*n⟩ := by
      apply QuadraticOrder163.ext <;> simp only [add,scale] <;> grind
    rw [he,← hz] at hm
    exact hm

theorem exists_triangular_basis (I : OrderIdeal163)
    (hn : ∃ u, I.contains u ∧ u≠zero) :
    ∃ A B d : Int, 0<A ∧ 0<d ∧ d ∣ A ∧ d ∣ B ∧
      ∀ z, I.contains z ↔ ∃ m n : Int, z=⟨A*m+B*n,d*n⟩ := by
  obtain ⟨A,hA,hAmem,hAmin⟩ := I.exists_least_positive_horizontal hn
  obtain ⟨B,d,hd,hBmem,hdmin⟩ := I.exists_least_positive_ordinate hn
  have hAomega := I.mul_mem ⟨A,0⟩ omega hAmem
  have hBomega := I.mul_mem ⟨B,d⟩ omega hBmem
  have hdivA := I.ordinate_divisibility B d hd hBmem hdmin _ hAomega
  have hdivB := I.ordinate_divisibility B d hd hBmem hdmin _ hBomega
  change d ∣ A*1+0*0+0*1 at hdivA
  change d ∣ B*1+d*0+d*1 at hdivB
  have ha : d ∣ A := by simpa using hdivA
  have hb : d ∣ B := by
    obtain ⟨q,hq⟩ := hdivB
    refine ⟨q-1,?_⟩
    grind
  exact ⟨A,B,d,hA,hd,ha,hb,I.triangular_membership A B d hA hd hAmem hBmem hAmin hdmin⟩

end ComputableAnalysis.ModularForms.OrderIdeal163
