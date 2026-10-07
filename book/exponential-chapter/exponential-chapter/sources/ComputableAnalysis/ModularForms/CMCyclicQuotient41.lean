import ComputableAnalysis.ModularForms.PrincipalIdeal163

/-! The concrete cyclic quotient of order 41 from multiplication by the CM point. -/
namespace ComputableAnalysis.ModularForms.QuadraticOrder163

/-- The residue detecting the quotient of the CM order by the principal ideal of omega. -/
def omegaResidue41 (u : QuadraticOrder163) : Int := u.x % 41

/-- Multiplication by the actual CM basis element has determinant 41. -/
theorem omega_multiplication_coordinates (u : QuadraticOrder163) :
    mul omega u=⟨-41*u.y,u.x+u.y⟩ := by
  apply ext <;> simp [mul,omega] <;> grind only

/-- The principal ideal of omega consists exactly of the elements with x coordinate divisible by 41. -/
theorem inPrincipalIdeal_omega_iff (u : QuadraticOrder163) :
    InPrincipalIdeal omega u ↔ (41:Int) ∣ u.x := by
  constructor
  · rintro ⟨v,hv⟩
    refine ⟨-v.y,?_⟩
    have h := congrArg QuadraticOrder163.x hv
    simp only [mul,omega] at h
    grind only
  · rintro ⟨k,hk⟩
    refine ⟨⟨u.y+k,-k⟩,?_⟩
    apply ext <;> simp only [mul,omega] <;> grind only

/-- The omega ideal is the kernel of the executable residue map. -/
theorem inPrincipalIdeal_omega_iff_residue_zero (u : QuadraticOrder163) :
    InPrincipalIdeal omega u ↔ omegaResidue41 u=0 := by
  rw [inPrincipalIdeal_omega_iff,Int.dvd_iff_emod_eq_zero]
  rfl

/-- Two elements have the same residue precisely when their difference belongs to the omega ideal. -/
theorem omegaResidue41_eq_iff (u v : QuadraticOrder163) :
    omegaResidue41 u=omegaResidue41 v ↔ InPrincipalIdeal omega (add u (neg v)) := by
  rw [inPrincipalIdeal_omega_iff,Int.dvd_iff_emod_eq_zero]
  exact Int.emod_eq_emod_iff_emod_sub_eq_zero

/-- Every residue lies in the finite interval of 41 canonical representatives. -/
theorem omegaResidue41_range (u : QuadraticOrder163) :
    0≤omegaResidue41 u ∧ omegaResidue41 u<41 :=
  ⟨Int.emod_nonneg _ (by decide +kernel),Int.emod_lt_of_pos _ (by decide +kernel)⟩

/-- Every one of the 41 canonical integer residues is realized by an order element. -/
theorem omegaResidue41_representative (r : Int) (hr : 0≤r) (hb : r<41) :
    omegaResidue41 ⟨r,0⟩=r := Int.emod_eq_of_lt hr hb

/-- Every order element has a canonical representative modulo the omega ideal. -/
theorem omegaResidue41_canonical (u : QuadraticOrder163) :
    InPrincipalIdeal omega (add u (neg ⟨omegaResidue41 u,0⟩)) := by
  apply (omegaResidue41_eq_iff _ _).mp
  exact (omegaResidue41_representative _ (omegaResidue41_range u).1 (omegaResidue41_range u).2).symm

/-- The canonical representative in the finite interval is unique. -/
theorem omegaResidue41_unique (u : QuadraticOrder163) (r : Int) (hr : 0≤r) (hb : r<41)
    (he : InPrincipalIdeal omega (add u (neg ⟨r,0⟩))) : r=omegaResidue41 u := by
  have h := (omegaResidue41_eq_iff _ _).mpr he
  rw [omegaResidue41_representative r hr hb] at h
  exact h.symm

/-- The residue respects addition in the quotient. -/
theorem omegaResidue41_add (u v : QuadraticOrder163) :
    omegaResidue41 (add u v)=(omegaResidue41 u+omegaResidue41 v)%41 :=
  Int.add_emod _ _ _

/-- The norm and lattice determinant of the CM multiplier are exactly 41. -/
theorem omega_norm_and_determinant :
    norm omega=41 ∧ omega.x*(mul omega omega).y-(mul omega omega).x*omega.y=41 := by
  decide +kernel

/-- The quotient residue is generated additively by the class of one. -/
theorem omegaResidue41_generated_by_one (r : Int) :
    omegaResidue41 (scale r one)=r%41 := by
  simp [omegaResidue41,scale,one]

/-- The residue respects multiplication in the quotient. -/
theorem omegaResidue41_mul (u v : QuadraticOrder163) :
    omegaResidue41 (mul u v)=(omegaResidue41 u*omegaResidue41 v)%41 := by
  change (u.x*v.x-41*u.y*v.y)%41=(u.x%41*(v.x%41))%41
  have he : u.x*v.x-41*u.y*v.y=u.x*v.x+41*(-(u.y*v.y)) := by grind only
  rw [he,Int.add_mul_emod_self_left,Int.mul_emod]

/-- The actual represented image of the CM order basis element is the CM point. -/
theorem omega_complexRaw_cm_point : omega.complexRaw.Equiv cmPoint163 := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := omega.complexRaw_valid) (hright := cmPoint163_valid)
  have h := complexValue_formula omega
  simp only [omega] at h
  change (⟨0,1⟩ : QuadraticOrder163).complexValue=cmPoint163Value
  grind

/-- Multiplication by the actual CM point maps every order-lattice point into the same lattice. -/
theorem cmPoint163_multiplication_lattice (u : QuadraticOrder163) :
    (ComplexRaw.mul cmPoint163 u.complexRaw).Equiv (mul omega u).complexRaw := by
  exact ComplexRaw.equiv_trans
    (ComplexRaw.mul_valid cmPoint163_valid u.complexRaw_valid)
    (ComplexRaw.mul_valid omega.complexRaw_valid u.complexRaw_valid) (mul omega u).complexRaw_valid
    (ComplexRaw.mul_equiv cmPoint163_valid omega.complexRaw_valid u.complexRaw_valid u.complexRaw_valid
      (ComplexRaw.equiv_symm omega_complexRaw_cm_point) (ComplexRaw.equiv_refl _ u.complexRaw_valid))
    (ComplexRaw.equiv_symm (complexRaw_mul omega u))

end ComputableAnalysis.ModularForms.QuadraticOrder163
