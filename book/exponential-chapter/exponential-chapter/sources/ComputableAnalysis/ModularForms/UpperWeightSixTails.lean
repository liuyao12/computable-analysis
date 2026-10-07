import ComputableAnalysis.ModularForms.UpperLatticeShells
import ComputableAnalysis.ModularForms.CMWeightSixTailRate163

/-! Summable weight-six shell bounds at every represented upper-half-plane input. -/
namespace ComputableAnalysis.ModularForms
open RiemannHilbert FunctionTheory QuadraticOrder163

def upperWeightSixTailConstant (z : Scalar) (hz : InUpperHalfPlane z.val) : Rat := 8*(2*latticeReciprocalConstant z hz)^6

theorem upperWeightSixShell_small (z : Scalar) (hz : InUpperHalfPlane z.val) (r : Nat) (hr : 0<r) :
    Small (upperShellSum z hz r hr 6) (upperWeightSixTailConstant z hz*reciprocalCube r) := by
  have h := upperShellSum_small z hz r hr 6
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

def upperWeightSixTailBlock (z : Scalar) (hz : InUpperHalfPlane z.val) (N : Nat) : Nat → ComplexRaw
  | 0 => ComplexRaw.zero
  | k+1 => ComplexRaw.add (upperWeightSixTailBlock z hz N k)
      (upperShellSum z hz (N+k+1) (by omega) 6)

theorem upperWeightSixTailBlock_valid (z : Scalar) (hz : InUpperHalfPlane z.val) (N k : Nat) : (upperWeightSixTailBlock z hz N k).Valid := by
  induction k with
  | zero => exact ComplexRaw.ofQComplex_valid _
  | succ k ih => exact ComplexRaw.add_valid ih (upperShellSum_valid z hz _ _ _)

theorem upperWeightSixTailBlock_small (z : Scalar) (hz : InUpperHalfPlane z.val) (N k : Nat) (hN : 0<N) :
    Small (upperWeightSixTailBlock z hz N k)
      (upperWeightSixTailConstant z hz*(reciprocalSquare N-reciprocalSquare (N+k))) := by
  have hC : 0≤upperWeightSixTailConstant z hz := by
    unfold upperWeightSixTailConstant
    exact Rat.mul_nonneg (by decide) (Rat.pow_nonneg
      (Rat.mul_nonneg (by decide) (latticeReciprocalConstant_nonnegative z hz)))
  induction k with
  | zero =>
    have he : upperWeightSixTailConstant z hz*(reciprocalSquare N-reciprocalSquare (N+0))=0 := by grind
    rw [he]
    exact Small.zero (by decide)
  | succ k ih =>
    have hs := upperWeightSixShell_small z hz (N+k+1) (by omega)
    have ht := reciprocalCube_step (N+k) (by omega)
    have hm := Rat.mul_le_mul_of_nonneg_left ht hC
    have hsum := LocalODE.small_add ih hs
    apply hsum.mono
    have he : N+(k+1)=N+k+1 := by omega
    rw [he]
    grind

theorem upperWeightSixTailBlock_uniform_small (z : Scalar) (hz : InUpperHalfPlane z.val) (N k : Nat) (hN : 0<N) :
    Small (upperWeightSixTailBlock z hz N k) (upperWeightSixTailConstant z hz*reciprocalSquare N) := by
  apply (upperWeightSixTailBlock_small z hz N k hN).mono
  have hp : (0:Rat)<((N+k:Nat):Rat) := by exact_mod_cast (show 0<N+k by omega)
  have hi := Rat.le_of_lt ((Rat.inv_pos).mpr (Rat.mul_pos hp hp))
  have hC : 0≤upperWeightSixTailConstant z hz := by
    unfold upperWeightSixTailConstant
    exact Rat.mul_nonneg (by decide) (Rat.pow_nonneg
      (Rat.mul_nonneg (by decide) (latticeReciprocalConstant_nonnegative z hz)))
  have hm := Rat.mul_nonneg hC hi
  change 0≤upperWeightSixTailConstant z hz*reciprocalSquare (N+k) at hm
  grind

end ComputableAnalysis.ModularForms
