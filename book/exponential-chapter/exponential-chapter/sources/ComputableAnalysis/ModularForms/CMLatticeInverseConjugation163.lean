import ComputableAnalysis.ModularForms.CMLatticeInverseFormula163

/-! Conjugation of certified reciprocals of integral CM lattice points. -/
namespace ComputableAnalysis.ModularForms.QuadraticOrder163
open RiemannHilbert
set_option maxRecDepth 8192

theorem conjugate_nonzero (u : QuadraticOrder163) (hu : u≠zero) : conjugate u≠zero := by
  intro h
  have h' := congrArg conjugate h
  rw [conjugate_involution] at h'
  exact hu h'

theorem norm_conjugate (u : QuadraticOrder163) : norm (conjugate u)=norm u := by
  unfold norm conjugate
  grind

private theorem conjugate_scale (r : Rat) (z : ComplexRaw) (hz : z.Valid) :
    (ComplexRaw.conj (ComplexRaw.scaleRat r z)).Equiv
      (ComplexRaw.scaleRat r (ComplexRaw.conj z)) := by
  have he (n : Nat) : (ComplexRaw.conj (ComplexRaw.scaleRat r z)).compute n=
      (ComplexRaw.scaleRat r (ComplexRaw.conj z)).compute n := by
    simp only [ComplexRaw.conj,ComplexRaw.scaleRat,QBox.conj,QBox.scaleRat]
    split <;> congr 1 <;> congr 1 <;> grind
  intro n
  apply (ComplexRaw.compareAt_overlap_iff _ _ n n).mpr
  rw [he]
  have ho := ComplexRaw.valid_ordered
    (ComplexRaw.scaleRat_valid (r := r) (ComplexRaw.conj_valid _ hz)) n
  exact ⟨⟨ho.1,ho.2⟩,⟨ho.1,ho.2⟩⟩

theorem normInverseRaw_conjugate (u : QuadraticOrder163) :
    (ComplexRaw.conj u.normInverseRaw).Equiv (conjugate u).normInverseRaw := by
  have hn : 0≤(norm u:Rat)⁻¹ := by
    by_cases hu : u=zero
    · subst u
      decide +kernel
    · exact Rat.le_of_lt (Rat.inv_pos.mpr (by exact_mod_cast norm_positive u hu))
  have h1 := conjugate_scale ((norm u:Rat)⁻¹) (conjugate u).complexRaw
    (conjugate u).complexRaw_valid
  have h2 := ComplexRaw.scaleRat_equiv_of_nonneg hn (complexRaw_conjugate (conjugate u))
  have h3 : (ComplexRaw.scaleRat ((norm u:Rat)⁻¹)
      (conjugate (conjugate u)).complexRaw)=(conjugate u).normInverseRaw := by
    simp only [normInverseRaw,norm_conjugate]
  exact ComplexRaw.equiv_trans (ComplexRaw.conj_valid _ u.normInverseRaw_valid)
    (ComplexRaw.scaleRat_valid (ComplexRaw.conj_valid _ (conjugate u).complexRaw_valid))
    (by rw [← h3]; exact ComplexRaw.scaleRat_valid (conjugate (conjugate u)).complexRaw_valid)
    h1 (by rw [← h3]; exact h2)

/-- The actual reciprocal construction respects the order's conjugation map. -/
theorem complexInverse_conjugate (u : QuadraticOrder163) (hu : u≠zero) :
    (ComplexRaw.conj (complexInverse u hu).val).Equiv
      (complexInverse (conjugate u) (conjugate_nonzero u hu)).val := by
  exact ComplexRaw.equiv_trans
    (ComplexRaw.conj_valid _ (complexInverse u hu).property)
    (ComplexRaw.conj_valid _ u.normInverseRaw_valid)
    (complexInverse (conjugate u) (conjugate_nonzero u hu)).property
    (ComplexRaw.conj_equiv (complexInverse_norm_formula u hu))
    (ComplexRaw.equiv_trans (ComplexRaw.conj_valid _ u.normInverseRaw_valid)
      (conjugate u).normInverseRaw_valid
      (complexInverse (conjugate u) (conjugate_nonzero u hu)).property
      (normInverseRaw_conjugate u)
      (ComplexRaw.equiv_symm (complexInverse_norm_formula _ _)))

/-- Conjugation of a square prefix fits inside the square of twice its radius.
Together with involution, this supplies the two-way enclosure for reindexing. -/
theorem conjugate_square_bounds (u : QuadraticOrder163) (r : Int)
    (hx : -r≤u.x ∧ u.x≤r) (hy : -r≤u.y ∧ u.y≤r) :
    (-2*r≤(conjugate u).x ∧ (conjugate u).x≤2*r) ∧
    (-r≤(conjugate u).y ∧ (conjugate u).y≤r) := by
  simp only [conjugate]
  omega

end ComputableAnalysis.ModularForms.QuadraticOrder163
