import ComputableAnalysis.ModularForms.UpperLatticeShells
import ComputableAnalysis.ModularForms.CMWeightFourTailRate163

/-! Summable weight-four shell bounds at every represented upper-half-plane input. -/
namespace ComputableAnalysis.ModularForms
open RiemannHilbert FunctionTheory QuadraticOrder163

def upperWeightFourTailConstant (z : Scalar) (hz : InUpperHalfPlane z.val) : Rat := 8*(2*latticeReciprocalConstant z hz)^4

theorem upperWeightFourShell_small (z : Scalar) (hz : InUpperHalfPlane z.val) (r : Nat) (hr : 0<r) :
    Small (upperShellSum z hz r hr 4) (upperWeightFourTailConstant z hz*reciprocalCube r) := by
  have h := upperShellSum_small z hz r hr 4
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

def upperWeightFourTailBlock (z : Scalar) (hz : InUpperHalfPlane z.val) (N : Nat) : Nat → ComplexRaw
  | 0 => ComplexRaw.zero
  | k+1 => ComplexRaw.add (upperWeightFourTailBlock z hz N k)
      (upperShellSum z hz (N+k+1) (by omega) 4)

theorem upperWeightFourTailBlock_valid (z : Scalar) (hz : InUpperHalfPlane z.val) (N k : Nat) : (upperWeightFourTailBlock z hz N k).Valid := by
  induction k with
  | zero => exact ComplexRaw.ofQComplex_valid _
  | succ k ih => exact ComplexRaw.add_valid ih (upperShellSum_valid z hz _ _ _)

theorem upperWeightFourTailBlock_small (z : Scalar) (hz : InUpperHalfPlane z.val) (N k : Nat) (hN : 0<N) :
    Small (upperWeightFourTailBlock z hz N k)
      (upperWeightFourTailConstant z hz*(reciprocalSquare N-reciprocalSquare (N+k))) := by
  have hC : 0≤upperWeightFourTailConstant z hz := by
    unfold upperWeightFourTailConstant
    exact Rat.mul_nonneg (by decide) (Rat.pow_nonneg
      (Rat.mul_nonneg (by decide) (latticeReciprocalConstant_nonnegative z hz)))
  induction k with
  | zero =>
    have he : upperWeightFourTailConstant z hz*(reciprocalSquare N-reciprocalSquare (N+0))=0 := by grind
    rw [he]
    exact Small.zero (by decide)
  | succ k ih =>
    have hs := upperWeightFourShell_small z hz (N+k+1) (by omega)
    have ht := reciprocalCube_step (N+k) (by omega)
    have hm := Rat.mul_le_mul_of_nonneg_left ht hC
    have hsum := LocalODE.small_add ih hs
    apply hsum.mono
    have he : N+(k+1)=N+k+1 := by omega
    rw [he]
    grind

theorem upperWeightFourTailBlock_uniform_small (z : Scalar) (hz : InUpperHalfPlane z.val) (N k : Nat) (hN : 0<N) :
    Small (upperWeightFourTailBlock z hz N k) (upperWeightFourTailConstant z hz*reciprocalSquare N) := by
  apply (upperWeightFourTailBlock_small z hz N k hN).mono
  have hp : (0:Rat)<((N+k:Nat):Rat) := by exact_mod_cast (show 0<N+k by omega)
  have hi := Rat.le_of_lt ((Rat.inv_pos).mpr (Rat.mul_pos hp hp))
  have hC : 0≤upperWeightFourTailConstant z hz := by
    unfold upperWeightFourTailConstant
    exact Rat.mul_nonneg (by decide) (Rat.pow_nonneg
      (Rat.mul_nonneg (by decide) (latticeReciprocalConstant_nonnegative z hz)))
  have hm := Rat.mul_nonneg hC hi
  change 0≤upperWeightFourTailConstant z hz*reciprocalSquare (N+k) at hm
  grind

end ComputableAnalysis.ModularForms
