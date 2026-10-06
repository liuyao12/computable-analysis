import ComputableAnalysis.ModularForms.FormIdealPrincipal163

/-! Principality of normalized integral ideal lattices from their closure equation. -/
namespace ComputableAnalysis.ModularForms
open QuadraticOrder163

def normalizedIdealLattice163 (a t m n : Int) : QuadraticOrder163 := ⟨a*m+t*n,n⟩

def InNormalizedIdeal163 (a t : Int) (z : QuadraticOrder163) : Prop :=
  ∃ m n : Int, z=normalizedIdealLattice163 a t m n

theorem normalizedIdeal163_divisibility_of_omega (a t : Int)
    (h : InNormalizedIdeal163 a t (mul ⟨t,1⟩ omega)) : a ∣ t*t+t+41 := by
  obtain ⟨m,n,h⟩ := h
  have hx := congrArg QuadraticOrder163.x h
  have hy := congrArg QuadraticOrder163.y h
  simp only [mul,omega,normalizedIdealLattice163] at hx hy
  refine ⟨-m,?_⟩
  grind

/-- The norm divisibility equation is precisely the arithmetic needed for this lattice. -/
def normalizedIdealForm163 (a t c : Int) (ha : 0<a)
    (hc : t*t+t+41=a*c) : IntegralForm163 where
  a := a
  b := 2*t+1
  c := c
  positive := ha
  discriminant := by grind

theorem normalizedIdealForm163_shift (a t c : Int) (ha : 0<a)
    (hc : t*t+t+41=a*c) : (normalizedIdealForm163 a t c ha hc).idealShift=t := by
  have h := (normalizedIdealForm163 a t c ha hc).middle_odd
  change 2*t+1=2*(normalizedIdealForm163 a t c ha hc).idealShift+1 at h
  omega

theorem normalizedIdealForm163_lattice (a t c m n : Int) (ha : 0<a)
    (hc : t*t+t+41=a*c) :
    (normalizedIdealForm163 a t c ha hc).idealLattice m n=normalizedIdealLattice163 a t m n := by
  unfold IntegralForm163.idealLattice
  rw [normalizedIdealForm163_shift]
  rfl

theorem normalizedIdeal163_principal (a t c : Int) (ha : 0<a)
    (hc : t*t+t+41=a*c) (z : QuadraticOrder163) :
    InNormalizedIdeal163 a t z ↔
      InPrincipalIdeal (normalizedIdealForm163 a t c ha hc).idealGenerator z := by
  rw [← IntegralForm163.ideal_principal]
  unfold InNormalizedIdeal163 IntegralForm163.InIdeal
  simp only [normalizedIdealForm163_lattice]

theorem normalizedIdeal163_exists_generator (a t : Int) (ha : 0<a)
    (hdiv : a ∣ t*t+t+41) :
    ∃ u : QuadraticOrder163, norm u=a ∧
      ∀ z, InNormalizedIdeal163 a t z ↔ InPrincipalIdeal u z := by
  obtain ⟨c,hc⟩ := hdiv
  let f := normalizedIdealForm163 a t c ha hc
  refine ⟨f.idealGenerator, f.idealGenerator_norm, ?_⟩
  intro z
  exact normalizedIdeal163_principal a t c ha hc z

theorem normalizedIdeal163_principal_of_closure (a t : Int) (ha : 0<a)
    (hclosed : ∀ z w, InNormalizedIdeal163 a t z → InNormalizedIdeal163 a t (mul z w)) :
    ∃ u : QuadraticOrder163, norm u=a ∧
      ∀ z, InNormalizedIdeal163 a t z ↔ InPrincipalIdeal u z := by
  apply normalizedIdeal163_exists_generator a t ha
  apply normalizedIdeal163_divisibility_of_omega
  apply hclosed ⟨t,1⟩ omega
  exact ⟨0,1,by apply QuadraticOrder163.ext <;> simp [normalizedIdealLattice163]⟩

end ComputableAnalysis.ModularForms
