import ComputableAnalysis.ModularForms.CMOrderEmbedding163

/-! Explicit principal-ideal lattices in the quadratic order. -/
namespace ComputableAnalysis.ModularForms.QuadraticOrder163

def InPrincipalIdeal (u z : QuadraticOrder163) : Prop := ∃ v, z=mul u v

def scale (n : Int) (u : QuadraticOrder163) : QuadraticOrder163 := ⟨n*u.x,n*u.y⟩

def principalLattice (u : QuadraticOrder163) (m n : Int) : QuadraticOrder163 :=
  add (scale m u) (scale n (mul u omega))

theorem principalLattice_eq_mul (u : QuadraticOrder163) (m n : Int) :
    principalLattice u m n=mul u ⟨m,n⟩ := by
  apply ext <;> simp only [principalLattice,scale,add,mul,omega] <;> grind

theorem inPrincipalIdeal_iff_lattice (u z : QuadraticOrder163) :
    InPrincipalIdeal u z ↔ ∃ m n : Int, z=principalLattice u m n := by
  constructor
  · rintro ⟨v,hv⟩
    refine ⟨v.x,v.y,?_⟩
    rw [principalLattice_eq_mul]
    exact hv
  · rintro ⟨m,n,h⟩
    refine ⟨⟨m,n⟩,?_⟩
    rw [h,principalLattice_eq_mul]

theorem principalLattice_determinant (u : QuadraticOrder163) :
    u.x*(mul u omega).y-(mul u omega).x*u.y=norm u := by
  simp only [mul,omega,norm]
  grind

theorem principalLattice_independent (u : QuadraticOrder163) (hu : u≠zero)
    (m n : Int) (h : principalLattice u m n=zero) : m=0 ∧ n=0 := by
  rw [principalLattice_eq_mul] at h
  have hz := (mul_eq_zero_iff u ⟨m,n⟩).mp h
  rcases hz with hz | hz
  · exact False.elim (hu hz)
  · exact ⟨congrArg QuadraticOrder163.x hz,congrArg QuadraticOrder163.y hz⟩

theorem principalIdeal_add (u z w : QuadraticOrder163)
    (hz : InPrincipalIdeal u z) (hw : InPrincipalIdeal u w) :
    InPrincipalIdeal u (add z w) := by
  obtain ⟨v,hv⟩ := hz
  obtain ⟨t,ht⟩ := hw
  refine ⟨add v t,?_⟩
  rw [mul_add,← hv,← ht]

theorem principalIdeal_mul (u z w : QuadraticOrder163)
    (hz : InPrincipalIdeal u z) : InPrincipalIdeal u (mul z w) := by
  obtain ⟨v,hv⟩ := hz
  refine ⟨mul v w,?_⟩
  rw [hv,mul_assoc]

theorem principalLattice_norm (u : QuadraticOrder163) (m n : Int) :
    norm (principalLattice u m n)=norm u*(m*m+m*n+41*n*n) := by
  rw [principalLattice_eq_mul,norm_mul]
  rfl

end ComputableAnalysis.ModularForms.QuadraticOrder163
