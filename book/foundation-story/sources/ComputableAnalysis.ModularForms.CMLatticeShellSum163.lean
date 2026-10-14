import ComputableAnalysis.ModularForms.CMLatticeShellEnumeration163

/-! Executable finite inverse-power shell sums and their represented bounds. -/
namespace ComputableAnalysis.ModularForms.QuadraticOrder163
open RiemannHilbert FunctionTheory

def shellTerm (r : Nat) (hr : 0<r) (k i : Nat) : ComplexRaw :=
  if hi : i<8*r then
    LocalODE.power (complexInverse (shellPoint r ⟨i,hi⟩) (shellPoint_nonzero r hr ⟨i,hi⟩)).val k
  else ComplexRaw.zero

theorem shellTerm_valid (r : Nat) (hr : 0<r) (k i : Nat) : (shellTerm r hr k i).Valid := by
  unfold shellTerm
  split
  · exact LocalODE.power_valid _ (complexInverse _ _).property k
  · exact ComplexRaw.ofQComplex_valid _

def shellTermBound (r k : Nat) : Rat := (2*(328/(r:Rat)))^k

theorem shellTermBound_nonnegative (r k : Nat) : 0≤shellTermBound r k := by
  unfold shellTermBound
  have h : (0:Rat)≤(r:Rat) := by exact_mod_cast Nat.zero_le r
  have hi : (0:Rat)≤(r:Rat)⁻¹ := by
    by_cases hz : r=0
    · subst r
      decide +kernel
    · have hp : (0:Rat)<(r:Rat) := by exact_mod_cast (show 0<r by omega)
      exact Rat.le_of_lt ((Rat.inv_pos).mpr hp)
  apply Rat.pow_nonneg
  change 0≤2*(328*(r:Rat)⁻¹)
  exact Rat.mul_nonneg (by decide +kernel) (Rat.mul_nonneg (by decide +kernel) hi)

theorem shellTerm_small (r : Nat) (hr : 0<r) (k i : Nat) :
    Small (shellTerm r hr k i) (shellTermBound r k) := by
  unfold shellTerm
  split
  · rename_i hi
    have h := shellPoint_bounds r ⟨i,hi⟩
    apply complexInverse_shell_power_small _ (shellPoint_nonzero r hr ⟨i,hi⟩)
      (r:Int) (by exact_mod_cast hr) ⟨h.1,h.2.1⟩ ⟨h.2.2.1,h.2.2.2.1⟩
    rcases h.2.2.2.2 with hx | hx | hy | hy <;> omega
  · exact Small.zero (shellTermBound_nonnegative r k)

def shellPrefix (r : Nat) (hr : 0<r) (k : Nat) : Nat → ComplexRaw
  | 0 => ComplexRaw.zero
  | n+1 => ComplexRaw.add (shellPrefix r hr k n) (shellTerm r hr k n)

theorem shellPrefix_valid (r : Nat) (hr : 0<r) (k n : Nat) : (shellPrefix r hr k n).Valid := by
  induction n with
  | zero => exact ComplexRaw.ofQComplex_valid _
  | succ n ih => exact ComplexRaw.add_valid ih (shellTerm_valid r hr k n)

theorem shellPrefix_small (r : Nat) (hr : 0<r) (k n : Nat) :
    Small (shellPrefix r hr k n) ((n:Rat)*shellTermBound r k) := by
  induction n with
  | zero =>
    change Small ComplexRaw.zero ((0:Rat)*shellTermBound r k)
    rw [Rat.zero_mul]
    exact Small.zero (by decide)
  | succ n ih =>
    have h := LocalODE.small_add ih (shellTerm_small r hr k n)
    have he : (n:Rat)*shellTermBound r k+shellTermBound r k=((n+1:Nat):Rat)*shellTermBound r k := by
      rw [Rat.natCast_add]
      grind
    rw [he] at h
    exact h

def shellSum (r : Nat) (hr : 0<r) (k : Nat) : ComplexRaw := shellPrefix r hr k (8*r)

theorem shellSum_valid (r : Nat) (hr : 0<r) (k : Nat) : (shellSum r hr k).Valid :=
  shellPrefix_valid r hr k _

theorem shellSum_small (r : Nat) (hr : 0<r) (k : Nat) :
    Small (shellSum r hr k) (((8*r:Nat):Rat)*shellTermBound r k) := shellPrefix_small r hr k _

end ComputableAnalysis.ModularForms.QuadraticOrder163
