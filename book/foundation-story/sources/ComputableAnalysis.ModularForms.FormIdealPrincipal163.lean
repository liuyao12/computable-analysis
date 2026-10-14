import ComputableAnalysis.ModularForms.ReducedIdealBasis163

/-! Principality of the concrete ideals attached to discriminant -163 forms. -/
namespace ComputableAnalysis.ModularForms
open QuadraticOrder163

theorem IntegralForm163.idealSecondBasis_eq (f : IntegralForm163) :
    f.idealSecondBasis=mul f.idealGenerator omega := by
  let u := f.idealGenerator
  let v := f.idealSecondBasis
  have hu := f.idealGenerator_norm
  have hv := f.reducedIdealLattice_norm 0 1
  have hs := f.reducedIdealLattice_norm 1 1
  have hd := f.reducedIdealBasis_determinant
  have he : f.reducedIdealLattice 1 1=add u v := by
    apply QuadraticOrder163.ext <;>
      simp only [u,v,idealGenerator,idealSecondBasis,reducedIdealLattice,
        idealLattice,add] <;> grind
  rw [he] at hs
  change norm u=f.a at hu
  change norm v=f.a*(0*0+0*1+41*1*1) at hv
  change u.x*v.y-v.x*u.y=f.a at hd
  have hc : mul (conjugate u) v=⟨0,f.a⟩ := by
    unfold norm at hu hv hs
    simp only [add] at hs
    apply QuadraticOrder163.ext <;> simp only [mul,conjugate] <;> grind
  have ht : mul (conjugate u) (mul u omega)=⟨0,f.a⟩ := by
    rw [← mul_assoc,mul_comm (conjugate u) u,mul_conjugate,hu]
    apply QuadraticOrder163.ext <;> simp [mul,omega]
  have hnonzero : conjugate u≠zero := by
    intro hz
    have h := congrArg conjugate hz
    rw [conjugate_involution] at h
    have huz : u=zero := h
    rw [huz] at hu
    change 0=f.a at hu
    have hp := f.positive
    omega
  exact mul_left_cancel (conjugate u) v (mul u omega) hnonzero (hc.trans ht.symm)

theorem IntegralForm163.reducedIdealLattice_eq_generator_mul (f : IntegralForm163) (m n : Int) :
    f.reducedIdealLattice m n=mul f.idealGenerator ⟨m,n⟩ := by
  have he : f.reducedIdealLattice m n=
      add (scale m f.idealGenerator) (scale n f.idealSecondBasis) := by
    apply QuadraticOrder163.ext <;>
      simp only [idealGenerator,idealSecondBasis,reducedIdealLattice,idealLattice,add,scale] <;> grind
  rw [he,idealSecondBasis_eq]
  exact principalLattice_eq_mul f.idealGenerator m n

theorem IntegralForm163.ideal_principal (f : IntegralForm163) (z : QuadraticOrder163) :
    f.InIdeal z ↔ InPrincipalIdeal f.idealGenerator z := by
  rw [inIdeal_iff_reducedLattice,inPrincipalIdeal_iff_lattice]
  constructor <;> rintro ⟨m,n,h⟩ <;> refine ⟨m,n,?_⟩
  · rw [h,reducedIdealLattice_eq_generator_mul,principalLattice_eq_mul]
  · rw [h,principalLattice_eq_mul,reducedIdealLattice_eq_generator_mul]

end ComputableAnalysis.ModularForms
