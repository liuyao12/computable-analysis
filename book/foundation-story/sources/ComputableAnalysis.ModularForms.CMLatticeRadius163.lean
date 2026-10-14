import ComputableAnalysis.ModularForms.CMLatticeShellEnumeration163
import ComputableAnalysis.ModularForms.CMLatticeInverseConjugation163

/-! Executable square-shell radius and conjugation enclosure. -/
namespace ComputableAnalysis.ModularForms.QuadraticOrder163

private def coordinateRadius (x : Int) : Nat := if x<0 then (-x).toNat else x.toNat

def shellRadius (u : QuadraticOrder163) : Nat := max (coordinateRadius u.x) (coordinateRadius u.y)

private theorem coordinateRadius_bounds (x : Int) :
    -(coordinateRadius x:Int)≤x ∧ x≤(coordinateRadius x:Int) ∧
    (x=(coordinateRadius x:Int) ∨ x= -(coordinateRadius x:Int)) := by
  unfold coordinateRadius
  split <;> omega

theorem shellRadius_bounds (u : QuadraticOrder163) :
    -(shellRadius u:Int)≤u.x ∧ u.x≤(shellRadius u:Int) ∧
    -(shellRadius u:Int)≤u.y ∧ u.y≤(shellRadius u:Int) ∧
    (u.x=(shellRadius u:Int) ∨ u.x= -(shellRadius u:Int) ∨
      u.y=(shellRadius u:Int) ∨ u.y= -(shellRadius u:Int)) := by
  have hx := coordinateRadius_bounds u.x
  have hy := coordinateRadius_bounds u.y
  unfold shellRadius
  rw [Nat.max_def]
  split <;> omega

theorem shellRadius_le_iff (u : QuadraticOrder163) (r : Nat) : shellRadius u≤r ↔
    -(r:Int)≤u.x ∧ u.x≤(r:Int) ∧ -(r:Int)≤u.y ∧ u.y≤(r:Int) := by
  have h := shellRadius_bounds u
  constructor <;> intro hr <;> omega

theorem shellRadius_positive (u : QuadraticOrder163) (hu : u≠zero) : 0<shellRadius u := by
  have h := shellRadius_bounds u
  by_cases hp : 0<shellRadius u
  · exact hp
  · have hx : u.x=0 := by omega
    have hy : u.y=0 := by omega
    exact False.elim (hu (ext hx hy))

theorem shellRadius_enumerated (u : QuadraticOrder163) (hu : u≠zero) :
    ∃ i : Fin (8*shellRadius u), shellPoint (shellRadius u) i=u := by
  have h := shellRadius_bounds u
  exact shellPoint_surjective _ (shellRadius_positive u hu) u ⟨h.1,h.2.1⟩ ⟨h.2.2.1,h.2.2.2.1⟩ h.2.2.2.2

theorem shellRadius_conjugate_le (u : QuadraticOrder163) :
    shellRadius (conjugate u)≤2*shellRadius u := by
  have h := shellRadius_bounds u
  have hc := conjugate_square_bounds u (shellRadius u:Int) ⟨h.1,h.2.1⟩
    ⟨h.2.2.1,h.2.2.2.1⟩
  apply (shellRadius_le_iff _ _).mpr
  constructor
  · exact_mod_cast hc.1.1
  constructor
  · exact_mod_cast hc.1.2
  constructor <;> omega

theorem shellRadius_shellPoint (r : Nat) (i : Fin (8*r)) :
    shellRadius (shellPoint r i)=r := by
  have h := shellPoint_bounds r i
  have hb := shellRadius_bounds (shellPoint r i)
  have hl := (shellRadius_le_iff (shellPoint r i) r).mpr
    ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1⟩
  omega

/-- The reverse enclosure follows from the actual conjugation involution. -/
theorem shellRadius_le_twice_conjugate (u : QuadraticOrder163) :
    shellRadius u≤2*shellRadius (conjugate u) := by
  have h := shellRadius_conjugate_le (conjugate u)
  rw [conjugate_involution] at h
  exact h

/-- A point absent from the conjugated square is already outside the half-radius
square, so its term is eligible for the proved masked-tail estimates. -/
theorem conjugate_outside_inner_square (u : QuadraticOrder163) (N : Nat)
    (h : 2*N<shellRadius (conjugate u)) : N<shellRadius u := by
  have hb := shellRadius_conjugate_le u
  omega

end ComputableAnalysis.ModularForms.QuadraticOrder163
