import ComputableAnalysis.ModularForms.IdealTriangularBasis163

/-! Every arbitrary nonzero integral ideal of the concrete order is principal. -/
namespace ComputableAnalysis.ModularForms.OrderIdeal163
open QuadraticOrder163

theorem exists_principal_generator (I : OrderIdeal163)
    (hn : ∃ v, I.contains v ∧ v≠zero) :
    ∃ u : QuadraticOrder163, u≠zero ∧ ∀ z, I.contains z ↔ InPrincipalIdeal u z := by
  obtain ⟨A,B,d,hA,hd,hdivA,hdivB,hbasis⟩ := I.exists_triangular_basis hn
  obtain ⟨a,ha⟩ := hdivA
  obtain ⟨t,ht⟩ := hdivB
  have hap : 0<a := by
    by_cases hp : 0<a
    · exact hp
    · have hm := Int.mul_nonpos_of_nonneg_of_nonpos (show 0≤d by omega) (show a≤0 by omega)
      rw [← ha] at hm
      omega
  have hsecond : I.contains ⟨B,d⟩ := (hbasis _).mpr ⟨0,1,by
    apply QuadraticOrder163.ext <;> simp⟩
  have hprod := I.mul_mem ⟨B,d⟩ omega hsecond
  obtain ⟨m,n,hmn⟩ := (hbasis _).mp hprod
  have hx := congrArg QuadraticOrder163.x hmn
  have hy := congrArg QuadraticOrder163.y hmn
  simp only [mul,omega] at hx hy
  rw [ha,ht] at hx
  rw [ht] at hy
  have hnval : n=t+1 := by
    apply Int.eq_of_mul_eq_mul_left (show d≠0 by omega)
    calc
      d*n = d*t*1+d*0+d*1 := hy.symm
      _ = d*(t+1) := by grind
  have hdiv : a ∣ t*t+t+41 := by
    refine ⟨-m,?_⟩
    rw [hnval] at hx
    apply Int.eq_of_mul_eq_mul_left (show d≠0 by omega)
    calc
      d*(t*t+t+41) = -(d*a*m+d*t*(t+1))+d*t*t+d*t := by grind
      _ = d*(a*(-m)) := by grind
  have hequiv (z : QuadraticOrder163) :
      I.contains z ↔ InScaledNormalizedIdeal163 d a t z := by
    rw [hbasis]
    unfold InScaledNormalizedIdeal163
    have he (m n : Int) : (⟨A*m+B*n,d*n⟩ : QuadraticOrder163)=
        scale d (normalizedIdealLattice163 a t m n) := by
      rw [ha,ht]
      apply QuadraticOrder163.ext <;> simp only [scale,normalizedIdealLattice163] <;> grind
    simp only [he]
  obtain ⟨u,hu,hprincipal⟩ := scaledNormalizedIdeal163_exists_generator d a t hap hdiv
  have huz : u≠zero := by
    intro hz
    rw [hz] at hu
    change 0=d*d*a at hu
    have hp := Int.mul_pos (Int.mul_pos hd hd) hap
    omega
  exact ⟨u,huz,fun z => (hequiv z).trans (hprincipal z)⟩

end ComputableAnalysis.ModularForms.OrderIdeal163
