import ComputableAnalysis.ModularForms.ScaledIdeal163

/-! Arbitrary ideals of the concrete quadratic order, with supplied closure evidence. -/
namespace ComputableAnalysis.ModularForms
open QuadraticOrder163

structure OrderIdeal163 where
  contains : QuadraticOrder163 → Prop
  zero_mem : contains zero
  add_mem : ∀ u v, contains u → contains v → contains (add u v)
  neg_mem : ∀ u, contains u → contains (neg u)
  mul_mem : ∀ u v, contains u → contains (mul u v)

namespace OrderIdeal163

theorem norm_mem (I : OrderIdeal163) (u : QuadraticOrder163) (hu : I.contains u) :
    I.contains ⟨norm u,0⟩ := by
  have h := I.mul_mem u (conjugate u) hu
  rw [mul_conjugate] at h
  exact h

theorem norm_omega_mem (I : OrderIdeal163) (u : QuadraticOrder163) (hu : I.contains u) :
    I.contains ⟨0,norm u⟩ := by
  have h := I.mul_mem ⟨norm u,0⟩ omega (I.norm_mem u hu)
  have he : mul ⟨norm u,0⟩ omega=⟨0,norm u⟩ := by
    apply QuadraticOrder163.ext <;> simp [mul,omega]
  rw [he] at h
  exact h

theorem scale_mem (I : OrderIdeal163) (u : QuadraticOrder163) (hu : I.contains u) (n : Int) :
    I.contains (scale n u) := by
  have h := I.mul_mem u ⟨n,0⟩ hu
  have he : mul u ⟨n,0⟩=scale n u := by
    apply QuadraticOrder163.ext <;> simp only [mul,scale] <;> grind
  rw [he] at h
  exact h

theorem norm_lattice_mem (I : OrderIdeal163) (u : QuadraticOrder163)
    (hu : I.contains u) (m n : Int) : I.contains ⟨norm u*m,norm u*n⟩ := by
  have h := I.add_mem _ _ (I.scale_mem _ (I.norm_mem u hu) m)
    (I.scale_mem _ (I.norm_omega_mem u hu) n)
  have he : add (scale m ⟨norm u,0⟩) (scale n ⟨0,norm u⟩)=⟨norm u*m,norm u*n⟩ := by
    apply QuadraticOrder163.ext <;> simp only [add,scale] <;> grind
  rw [he] at h
  exact h

theorem nonzero_contains_positive_axes (I : OrderIdeal163)
    (hnonzero : ∃ u, I.contains u ∧ u≠zero) :
    ∃ N : Int, 0<N ∧ I.contains ⟨N,0⟩ ∧ I.contains ⟨0,N⟩ := by
  obtain ⟨u,hu,huz⟩ := hnonzero
  exact ⟨norm u,norm_positive u huz,I.norm_mem u hu,I.norm_omega_mem u hu⟩

end OrderIdeal163
end ComputableAnalysis.ModularForms
