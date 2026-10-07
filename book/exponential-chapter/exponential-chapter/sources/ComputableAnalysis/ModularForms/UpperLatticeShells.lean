import ComputableAnalysis.ModularForms.UpperLatticeInverseBounds

/-! Executable inverse-power square shells at arbitrary represented upper-half-plane inputs. -/
namespace ComputableAnalysis.ModularForms
open RiemannHilbert FunctionTheory QuadraticOrder163

def upperShellTerm (z : Scalar) (hz : InUpperHalfPlane z.val) (r : Nat) (hr : 0<r) (k i : Nat) : ComplexRaw :=
  if hi : i<8*r then
    LocalODE.power (latticeInverse z hz (shellPoint r ⟨i,hi⟩) (shellPoint_nonzero r hr ⟨i,hi⟩)).val k
  else ComplexRaw.zero

theorem upperShellTerm_valid (z : Scalar) (hz : InUpperHalfPlane z.val) (r : Nat) (hr : 0<r) (k i : Nat) : (upperShellTerm z hz r hr k i).Valid := by
  unfold upperShellTerm
  split
  · exact LocalODE.power_valid _ (latticeInverse z hz _ _).property k
  · exact ComplexRaw.ofQComplex_valid _

def upperShellTermBound (z : Scalar) (hz : InUpperHalfPlane z.val) (r k : Nat) : Rat := (2*(latticeReciprocalConstant z hz/(r:Rat)))^k

theorem upperShellTermBound_nonnegative (z : Scalar) (hz : InUpperHalfPlane z.val) (r k : Nat) : 0≤upperShellTermBound z hz r k := by
  unfold upperShellTermBound
  have hi : (0:Rat)≤(r:Rat)⁻¹ := by
    by_cases hz : r=0
    · subst r
      decide +kernel
    · have hp : (0:Rat)<(r:Rat) := by exact_mod_cast (show 0<r by omega)
      exact Rat.le_of_lt ((Rat.inv_pos).mpr hp)
  apply Rat.pow_nonneg
  change 0≤2*(latticeReciprocalConstant z hz*(r:Rat)⁻¹)
  exact Rat.mul_nonneg (by decide +kernel) (Rat.mul_nonneg (latticeReciprocalConstant_nonnegative z hz) hi)

theorem upperShellTerm_small (z : Scalar) (hz : InUpperHalfPlane z.val) (r : Nat) (hr : 0<r) (k i : Nat) :
    Small (upperShellTerm z hz r hr k i) (upperShellTermBound z hz r k) := by
  unfold upperShellTerm
  split
  · rename_i hi
    have hrq : 0<(r:Rat) := by exact_mod_cast hr
    have hb := latticeInverse_radius_bound z hz (shellPoint r ⟨i,hi⟩)
      (shellPoint_nonzero r hr ⟨i,hi⟩)
    rw [shellRadius_shellPoint] at hb
    exact LocalODE.power_small _ (latticeInverse z hz _ _).property
      (latticeReciprocalConstant z hz/(r:Rat))
      (Rat.mul_nonneg (latticeReciprocalConstant_nonnegative z hz)
        (Rat.le_of_lt (Rat.inv_pos.mpr hrq))) hb k
  · exact Small.zero (upperShellTermBound_nonnegative z hz r k)

def upperShellPrefix (z : Scalar) (hz : InUpperHalfPlane z.val) (r : Nat) (hr : 0<r) (k : Nat) : Nat → ComplexRaw
  | 0 => ComplexRaw.zero
  | n+1 => ComplexRaw.add (upperShellPrefix z hz r hr k n) (upperShellTerm z hz r hr k n)

theorem upperShellPrefix_valid (z : Scalar) (hz : InUpperHalfPlane z.val) (r : Nat) (hr : 0<r) (k n : Nat) : (upperShellPrefix z hz r hr k n).Valid := by
  induction n with
  | zero => exact ComplexRaw.ofQComplex_valid _
  | succ n ih => exact ComplexRaw.add_valid ih (upperShellTerm_valid z hz r hr k n)

theorem upperShellPrefix_small (z : Scalar) (hz : InUpperHalfPlane z.val) (r : Nat) (hr : 0<r) (k n : Nat) :
    Small (upperShellPrefix z hz r hr k n) ((n:Rat)*upperShellTermBound z hz r k) := by
  induction n with
  | zero =>
    change Small ComplexRaw.zero ((0:Rat)*upperShellTermBound z hz r k)
    rw [Rat.zero_mul]
    exact Small.zero (by decide)
  | succ n ih =>
    have h := LocalODE.small_add ih (upperShellTerm_small z hz r hr k n)
    have he : (n:Rat)*upperShellTermBound z hz r k+upperShellTermBound z hz r k=((n+1:Nat):Rat)*upperShellTermBound z hz r k := by
      rw [Rat.natCast_add]
      grind
    rw [he] at h
    exact h

def upperShellSum (z : Scalar) (hz : InUpperHalfPlane z.val) (r : Nat) (hr : 0<r) (k : Nat) : ComplexRaw := upperShellPrefix z hz r hr k (8*r)

theorem upperShellSum_valid (z : Scalar) (hz : InUpperHalfPlane z.val) (r : Nat) (hr : 0<r) (k : Nat) : (upperShellSum z hz r hr k).Valid :=
  upperShellPrefix_valid z hz r hr k _

theorem upperShellSum_small (z : Scalar) (hz : InUpperHalfPlane z.val) (r : Nat) (hr : 0<r) (k : Nat) :
    Small (upperShellSum z hz r hr k) (((8*r:Nat):Rat)*upperShellTermBound z hz r k) := upperShellPrefix_small z hz r hr k _

end ComputableAnalysis.ModularForms
