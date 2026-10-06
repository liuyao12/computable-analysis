import ComputableAnalysis.ModularForms.CMLatticeBounds163

/-! Quantitative bounds for the explicit and certified CM lattice reciprocals. -/
namespace ComputableAnalysis.ModularForms.QuadraticOrder163
open RiemannHilbert FunctionTheory

theorem conjugate_complexRaw_small (u : QuadraticOrder163) (r : Rat) (hr : 0≤r)
    (hx : -r≤(u.x:Rat) ∧ (u.x:Rat)≤r)
    (hy : -r≤(u.y:Rat) ∧ (u.y:Rat)≤r) :
    Small (conjugate u).complexRaw (164*r) := by
  have hc : Small (conjugate u).complexRaw (82*(2*r)) := by
    apply complexRaw_small (conjugate u) (2*r) (by grind)
    · change -(2*r)≤((u.x+u.y:Int):Rat) ∧ ((u.x+u.y:Int):Rat)≤2*r
      grind
    · change -(2*r)≤((-u.y:Int):Rat) ∧ ((-u.y:Int):Rat)≤2*r
      grind
  have he : (82:Rat)*(2*r)=164*r := by grind
  rw [he] at hc
  exact hc

theorem normInverseRaw_small (u : QuadraticOrder163) (hu : u≠zero)
    (r : Rat) (hr : 0≤r)
    (hx : -r≤(u.x:Rat) ∧ (u.x:Rat)≤r)
    (hy : -r≤(u.y:Rat) ∧ (u.y:Rat)≤r) :
    Small u.normInverseRaw ((norm u:Rat)⁻¹*(164*r)) := by
  have hp : (0:Rat)<(norm u:Rat) := by exact_mod_cast norm_positive u hu
  have hi : (0:Rat)≤(norm u:Rat)⁻¹ := Rat.le_of_lt ((Rat.inv_pos).mpr hp)
  exact LocalODE.small_scale hi (conjugate_complexRaw_small u r hr hx hy)

theorem complexInverse_small (u : QuadraticOrder163) (hu : u≠zero)
    (r : Rat) (hr : 0≤r)
    (hx : -r≤(u.x:Rat) ∧ (u.x:Rat)≤r)
    (hy : -r≤(u.y:Rat) ∧ (u.y:Rat)≤r) :
    Small (complexInverse u hu).val ((norm u:Rat)⁻¹*(164*r)) :=
  Small.congr u.normInverseRaw_valid (complexInverse u hu).property
    (ComplexRaw.equiv_symm (complexInverse_norm_formula u hu))
    (normInverseRaw_small u hu r hr hx hy)

end ComputableAnalysis.ModularForms.QuadraticOrder163
