import ComputableAnalysis.ModularForms.PrincipalIdeal163

/-! Explicit order-ideal lattice attached to an integral quadratic form. -/
namespace ComputableAnalysis.ModularForms

def IntegralForm163.idealShift (f : IntegralForm163) : Int := f.b/2

theorem IntegralForm163.middle_odd (f : IntegralForm163) :
    f.b=2*f.idealShift+1 := by
  have hr := Int.emod_nonneg f.b (by decide : (2:Int)≠0)
  have hu := Int.emod_lt_of_pos f.b (by decide : (0:Int)<2)
  have he := Int.mul_ediv_add_emod f.b 2
  have hd := f.discriminant
  have hrem : f.b%2=1 := by
    by_cases h : f.b%2=0
    · have hb : f.b=2*(f.b/2) := by omega
      rw [hb] at hd
      have hm : 4*(f.a*f.c-(f.b/2)*(f.b/2))=163 := by grind
      omega
    · omega
  unfold idealShift
  omega

theorem IntegralForm163.idealShift_norm (f : IntegralForm163) :
    f.idealShift*f.idealShift+f.idealShift+41=f.a*f.c := by
  have hb := f.middle_odd
  have hd := f.discriminant
  rw [hb] at hd
  grind

def IntegralForm163.idealLattice (f : IntegralForm163) (m n : Int) : QuadraticOrder163 :=
  ⟨f.a*m+f.idealShift*n,n⟩

def IntegralForm163.InIdeal (f : IntegralForm163) (z : QuadraticOrder163) : Prop :=
  ∃ m n : Int, z=f.idealLattice m n

theorem IntegralForm163.idealLattice_norm (f : IntegralForm163) (m n : Int) :
    QuadraticOrder163.norm (f.idealLattice m n)=f.a*f.eval m n := by
  have hb := f.middle_odd
  have ht := f.idealShift_norm
  unfold idealLattice QuadraticOrder163.norm eval
  grind

theorem IntegralForm163.idealLattice_mul_omega (f : IntegralForm163) (m n : Int) :
    QuadraticOrder163.mul (f.idealLattice m n) QuadraticOrder163.omega=
      f.idealLattice (-f.idealShift*m-f.c*n) (f.a*m+(f.idealShift+1)*n) := by
  have ht := f.idealShift_norm
  apply QuadraticOrder163.ext <;>
    simp only [idealLattice,QuadraticOrder163.mul,QuadraticOrder163.omega] <;> grind

theorem IntegralForm163.ideal_add (f : IntegralForm163) (z w : QuadraticOrder163)
    (hz : f.InIdeal z) (hw : f.InIdeal w) : f.InIdeal (QuadraticOrder163.add z w) := by
  obtain ⟨m,n,hz⟩ := hz
  obtain ⟨p,q,hw⟩ := hw
  refine ⟨m+p,n+q,?_⟩
  rw [hz,hw]
  apply QuadraticOrder163.ext <;> simp only [idealLattice,QuadraticOrder163.add] <;> grind

theorem IntegralForm163.ideal_mul (f : IntegralForm163) (z w : QuadraticOrder163)
    (hz : f.InIdeal z) : f.InIdeal (QuadraticOrder163.mul z w) := by
  obtain ⟨m,n,hz⟩ := hz
  refine ⟨w.x*m+w.y*(-f.idealShift*m-f.c*n),
    w.x*n+w.y*(f.a*m+(f.idealShift+1)*n),?_⟩
  rw [hz]
  have ht := f.idealShift_norm
  apply QuadraticOrder163.ext <;> simp only [idealLattice,QuadraticOrder163.mul] <;> grind

end ComputableAnalysis.ModularForms
