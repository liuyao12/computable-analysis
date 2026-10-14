import ComputableAnalysis.ModularForms.CMLatticeInverseBounds163

/-! Reciprocal and inverse-power decay on square coordinate shells. -/
namespace ComputableAnalysis.ModularForms.QuadraticOrder163
open RiemannHilbert FunctionTheory

theorem complexInverse_shell_small (u : QuadraticOrder163) (hu : u≠zero)
    (r : Int) (hr : 0<r)
    (hx : -r≤u.x ∧ u.x≤r) (hy : -r≤u.y ∧ u.y≤r)
    (hout : r≤u.x ∨ u.x≤ -r ∨ r≤u.y ∨ u.y≤ -r) :
    Small (complexInverse u hu).val (328/(r:Rat)) := by
  have hnorm := norm_lower_outside_box u r (by omega) hout
  have hq : (r:Rat)*(r:Rat)≤2*(norm u:Rat) := by exact_mod_cast hnorm
  have hrq : (0:Rat)<(r:Rat) := by exact_mod_cast hr
  have hnq : (0:Rat)<(norm u:Rat) := by exact_mod_cast norm_positive u hu
  have hs := complexInverse_small u hu (r:Rat) (Rat.le_of_lt hrq)
    (by exact_mod_cast hx) (by exact_mod_cast hy)
  apply hs.mono
  apply Rat.le_of_mul_le_mul_right (c := (norm u:Rat)*(r:Rat))
  · have hnz : (norm u:Rat)≠0 := Rat.ne_of_gt hnq
    have hrz : (r:Rat)≠0 := Rat.ne_of_gt hrq
    have hcN := Rat.mul_inv_cancel (norm u:Rat) hnz
    have hcr := Rat.mul_inv_cancel (r:Rat) hrz
    have hm := Rat.mul_le_mul_of_nonneg_left hq (show (0:Rat)≤164 by decide +kernel)
    calc
      _ = 164*(r:Rat)*(r:Rat) := by grind
      _ ≤ 328*(norm u:Rat) := by grind
      _ = _ := by grind [Rat.div_def]
  · exact Rat.mul_pos hnq hrq

theorem complexInverse_shell_power_small (u : QuadraticOrder163) (hu : u≠zero)
    (r : Int) (hr : 0<r)
    (hx : -r≤u.x ∧ u.x≤r) (hy : -r≤u.y ∧ u.y≤r)
    (hout : r≤u.x ∨ u.x≤ -r ∨ r≤u.y ∨ u.y≤ -r) (k : Nat) :
    Small (LocalODE.power (complexInverse u hu).val k) ((2*(328/(r:Rat)))^k) := by
  apply LocalODE.power_small _ (complexInverse u hu).property
    (328/(r:Rat)) _ (complexInverse_shell_small u hu r hr hx hy hout) k
  have hp : (0:Rat)<(r:Rat) := by exact_mod_cast hr
  have hi := Rat.le_of_lt ((Rat.inv_pos).mpr hp)
  change 0≤328*(r:Rat)⁻¹
  exact Rat.mul_nonneg (by decide +kernel) hi

end ComputableAnalysis.ModularForms.QuadraticOrder163
