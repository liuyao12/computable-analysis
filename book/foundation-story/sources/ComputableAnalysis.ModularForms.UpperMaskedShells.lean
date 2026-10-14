import ComputableAnalysis.ModularForms.UpperWeightFourTails
import ComputableAnalysis.ModularForms.UpperWeightSixTails

/-! Bounds for arbitrary executable subsets of general upper-half-plane lattice shells. -/
namespace ComputableAnalysis.ModularForms
open RiemannHilbert FunctionTheory QuadraticOrder163

def upperMaskedShellPrefix (z : Scalar) (hz : InUpperHalfPlane z.val) (r : Nat) (hr : 0<r) (k : Nat) (keep : Nat → Bool) : Nat → ComplexRaw
  | 0 => ComplexRaw.zero
  | n+1 => ComplexRaw.add (upperMaskedShellPrefix z hz r hr k keep n)
      (if keep n then upperShellTerm z hz r hr k n else ComplexRaw.zero)

theorem upperMaskedShellPrefix_valid (z : Scalar) (hz : InUpperHalfPlane z.val) (r : Nat) (hr : 0<r) (k : Nat) (keep : Nat → Bool)
    (n : Nat) : (upperMaskedShellPrefix z hz r hr k keep n).Valid := by
  induction n with
  | zero => exact ComplexRaw.ofQComplex_valid _
  | succ n ih =>
    apply ComplexRaw.add_valid ih
    split
    · exact upperShellTerm_valid z hz r hr k n
    · exact ComplexRaw.ofQComplex_valid _

theorem upperMaskedShellPrefix_small (z : Scalar) (hz : InUpperHalfPlane z.val) (r : Nat) (hr : 0<r) (k : Nat) (keep : Nat → Bool)
    (n : Nat) : Small (upperMaskedShellPrefix z hz r hr k keep n) ((n:Rat)*upperShellTermBound z hz r k) := by
  induction n with
  | zero =>
    change Small ComplexRaw.zero ((0:Rat)*upperShellTermBound z hz r k)
    rw [Rat.zero_mul]
    exact Small.zero (by decide)
  | succ n ih =>
    have ht : Small (if keep n then upperShellTerm z hz r hr k n else ComplexRaw.zero)
        (upperShellTermBound z hz r k) := by
      split
      · exact upperShellTerm_small z hz r hr k n
      · exact Small.zero (upperShellTermBound_nonnegative z hz r k)
    have hs := LocalODE.small_add ih ht
    have he : (n:Rat)*upperShellTermBound z hz r k+upperShellTermBound z hz r k=
        ((n+1:Nat):Rat)*upperShellTermBound z hz r k := by
      rw [Rat.natCast_add]
      grind
    rw [he] at hs
    exact hs

def upperMaskedShellSum (z : Scalar) (hz : InUpperHalfPlane z.val) (r : Nat) (hr : 0<r) (k : Nat) (keep : Nat → Bool) : ComplexRaw :=
  upperMaskedShellPrefix z hz r hr k keep (8*r)

theorem upperMaskedShellSum_valid (z : Scalar) (hz : InUpperHalfPlane z.val) (r : Nat) (hr : 0<r) (k : Nat) (keep : Nat → Bool) :
    (upperMaskedShellSum z hz r hr k keep).Valid := upperMaskedShellPrefix_valid z hz r hr k keep _

theorem upperMaskedShellSum_small (z : Scalar) (hz : InUpperHalfPlane z.val) (r : Nat) (hr : 0<r) (k : Nat) (keep : Nat → Bool) :
    Small (upperMaskedShellSum z hz r hr k keep) (((8*r:Nat):Rat)*upperShellTermBound z hz r k) :=
  upperMaskedShellPrefix_small z hz r hr k keep _

theorem upperMaskedWeightFourShell_small (z : Scalar) (hz : InUpperHalfPlane z.val)
    (r : Nat) (hr : 0<r) (keep : Nat → Bool) :
    Small (upperMaskedShellSum z hz r hr 4 keep)
      (upperWeightFourTailConstant z hz*reciprocalCube r) := by
  have h := upperMaskedShellSum_small z hz r hr 4 keep
  have hp : (0:Rat)<(r:Rat) := by exact_mod_cast hr
  have hc := Rat.mul_inv_cancel (r:Rat) (Rat.ne_of_gt hp)
  have hp3 : (r:Rat)*(r:Rat)*(r:Rat)≠0 :=
    Rat.ne_of_gt (Rat.mul_pos (Rat.mul_pos hp hp) hp)
  have hc3 := Rat.mul_inv_cancel _ hp3
  have he : (((8*r:Nat):Rat)*upperShellTermBound z hz r 4)=upperWeightFourTailConstant z hz*reciprocalCube r := by
    unfold upperShellTermBound upperWeightFourTailConstant reciprocalCube
    rw [Rat.natCast_mul]
    simp only [Rat.pow_succ,Rat.pow_zero]
    grind [Rat.div_def]
  rw [he] at h
  exact h

theorem upperMaskedWeightSixShell_small (z : Scalar) (hz : InUpperHalfPlane z.val)
    (r : Nat) (hr : 0<r) (keep : Nat → Bool) :
    Small (upperMaskedShellSum z hz r hr 6 keep)
      (upperWeightSixTailConstant z hz*reciprocalCube r) := by
  have h := upperMaskedShellSum_small z hz r hr 6 keep
  apply h.mono
  let a : Rat := r
  have hp : 0<a := by dsimp [a]; exact_mod_cast hr
  have h1 : (1:Rat)≤a := by dsimp [a]; exact_mod_cast hr
  have hc := Rat.mul_inv_cancel a (Rat.ne_of_gt hp)
  have hc3 := Rat.mul_inv_cancel (a*a*a)
    (Rat.ne_of_gt (Rat.mul_pos (Rat.mul_pos hp hp) hp))
  have h2 : 1≤a*a := by
    have hm := Rat.mul_le_mul_of_nonneg_left h1 (Rat.le_of_lt hp)
    grind
  have h3 : a≤a*a*a := by
    have hm := Rat.mul_le_mul_of_nonneg_left h2 (Rat.le_of_lt hp)
    grind
  unfold upperShellTermBound upperWeightSixTailConstant reciprocalCube
  rw [Rat.natCast_mul]
  apply Rat.le_of_mul_le_mul_right (c := a*a*a*a*a*a)
  · calc
      _ = 8*(2*latticeReciprocalConstant z hz)^6*a := by
        simp only [Rat.pow_succ,Rat.pow_zero]
        grind [Rat.div_def]
      _ ≤ 8*(2*latticeReciprocalConstant z hz)^6*(a*a*a) := by
        exact Rat.mul_le_mul_of_nonneg_left h3 (Rat.mul_nonneg (by decide) (Rat.pow_nonneg (Rat.mul_nonneg (by decide) (latticeReciprocalConstant_nonnegative z hz))))
      _ = _ := by
        simp only [Rat.pow_succ,Rat.pow_zero]
        grind
  · exact Rat.mul_pos (Rat.mul_pos (Rat.mul_pos (Rat.mul_pos (Rat.mul_pos hp hp) hp) hp) hp) hp

end ComputableAnalysis.ModularForms
