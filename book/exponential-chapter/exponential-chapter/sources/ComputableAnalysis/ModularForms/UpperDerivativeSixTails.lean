import ComputableAnalysis.ModularForms.UpperDerivativeShells
import ComputableAnalysis.ModularForms.UpperWeightSixTails
import ComputableAnalysis.ModularForms.CMWeightSixTailRate163

/-! Summable weight-six shell bounds at every represented upper-half-plane input. -/
namespace ComputableAnalysis.ModularForms
open RiemannHilbert FunctionTheory QuadraticOrder163

def regionalDerivativeSixTailConstant (R H eta : Rat) : Rat := 96*(2*latticeRegionReciprocalConstant R H eta)^7

theorem derivativeWeightSixShell_small (z : Scalar) (hz : InUpperHalfPlane z.val)
    (R H eta : Rat) (S : Nat) (hR : 0≤R) (hH : 0≤H) (heta : 0<eta)
    (hregion : LatticeRegionBox z R eta S) (hheight : (z.val.compute S).hi.im≤H) (r : Nat) (hr : 0<r) :
    Small (derivativeShellSum z hz r hr 6) (regionalDerivativeSixTailConstant R H eta*reciprocalCube r) := by
  have h := derivativeShellSum_region_bound z hz R H eta S hR hH heta hregion hheight r hr 6
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
  have h4 : a*a≤a*a*a*a := by
    have hm := Rat.mul_le_mul_of_nonneg_left h2 (Rat.le_of_lt (Rat.mul_pos hp hp))
    grind
  change (((8*r:Nat):Rat)*(2*((6:Rat)*(r:Rat))*(2*(latticeRegionReciprocalConstant R H eta/(r:Rat)))^7)) ≤ _
  unfold regionalDerivativeSixTailConstant reciprocalCube
  rw [Rat.natCast_mul]
  apply Rat.le_of_mul_le_mul_right (c := a*a*a*a*a*a*a)
  · calc
      _ = 96*(2*latticeRegionReciprocalConstant R H eta)^7*(a*a) := by
        simp only [Rat.pow_succ,Rat.pow_zero]
        grind [Rat.div_def]
      _ ≤ 96*(2*latticeRegionReciprocalConstant R H eta)^7*(a*a*a*a) := by
        exact Rat.mul_le_mul_of_nonneg_left h4 (Rat.mul_nonneg (by decide)
          (Rat.pow_nonneg (Rat.mul_nonneg (by decide)
            (latticeRegionReciprocalConstant_nonnegative R H eta hR hH heta))))
      _ = _ := by
        simp only [Rat.pow_succ,Rat.pow_zero]
        grind
  · exact Rat.mul_pos (Rat.mul_pos (Rat.mul_pos (Rat.mul_pos (Rat.mul_pos (Rat.mul_pos hp hp) hp) hp) hp) hp) hp

def derivativeWeightSixTailBlock (z : Scalar) (hz : InUpperHalfPlane z.val) (N : Nat) : Nat → ComplexRaw
  | 0 => ComplexRaw.zero
  | k+1 => ComplexRaw.add (derivativeWeightSixTailBlock z hz N k)
      (derivativeShellSum z hz (N+k+1) (by omega) 6)

theorem derivativeWeightSixTailBlock_valid (z : Scalar) (hz : InUpperHalfPlane z.val) (N k : Nat) :
    (derivativeWeightSixTailBlock z hz N k).Valid := by
  induction k with
  | zero => exact ComplexRaw.ofQComplex_valid _
  | succ k ih => exact ComplexRaw.add_valid ih (derivativeShellPrefix_valid z hz _ _ 6 _)

theorem derivativeWeightSixTailBlock_small (z : Scalar) (hz : InUpperHalfPlane z.val)
    (R H eta : Rat) (S : Nat) (hR : 0≤R) (hH : 0≤H) (heta : 0<eta)
    (hregion : LatticeRegionBox z R eta S) (hheight : (z.val.compute S).hi.im≤H) (N k : Nat) (hN : 0<N) :
    Small (derivativeWeightSixTailBlock z hz N k)
      (regionalDerivativeSixTailConstant R H eta*(reciprocalSquare N-reciprocalSquare (N+k))) := by
  have hC : 0≤regionalDerivativeSixTailConstant R H eta := by
    unfold regionalDerivativeSixTailConstant
    exact Rat.mul_nonneg (by decide) (Rat.pow_nonneg
      (Rat.mul_nonneg (by decide) (latticeRegionReciprocalConstant_nonnegative R H eta hR hH heta)))
  induction k with
  | zero =>
    have he : regionalDerivativeSixTailConstant R H eta*(reciprocalSquare N-reciprocalSquare (N+0))=0 := by grind
    rw [he]
    exact Small.zero (by decide)
  | succ k ih =>
    have hs := derivativeWeightSixShell_small z hz R H eta S hR hH heta hregion hheight (N+k+1) (by omega)
    have ht := reciprocalCube_step (N+k) (by omega)
    have hm := Rat.mul_le_mul_of_nonneg_left ht hC
    have hsum := LocalODE.small_add ih hs
    apply hsum.mono
    have he : N+(k+1)=N+k+1 := by omega
    rw [he]
    grind

theorem derivativeWeightSixTailBlock_uniform_small (z : Scalar) (hz : InUpperHalfPlane z.val)
    (R H eta : Rat) (S : Nat) (hR : 0≤R) (hH : 0≤H) (heta : 0<eta)
    (hregion : LatticeRegionBox z R eta S) (hheight : (z.val.compute S).hi.im≤H) (N k : Nat) (hN : 0<N) :
    Small (derivativeWeightSixTailBlock z hz N k) (regionalDerivativeSixTailConstant R H eta*reciprocalSquare N) := by
  apply (derivativeWeightSixTailBlock_small z hz R H eta S hR hH heta hregion hheight N k hN).mono
  have hp : (0:Rat)<((N+k:Nat):Rat) := by exact_mod_cast (show 0<N+k by omega)
  have hi := Rat.le_of_lt ((Rat.inv_pos).mpr (Rat.mul_pos hp hp))
  have hC : 0≤regionalDerivativeSixTailConstant R H eta := by
    unfold regionalDerivativeSixTailConstant
    exact Rat.mul_nonneg (by decide) (Rat.pow_nonneg
      (Rat.mul_nonneg (by decide) (latticeRegionReciprocalConstant_nonnegative R H eta hR hH heta)))
  have hm := Rat.mul_nonneg hC hi
  change 0≤regionalDerivativeSixTailConstant R H eta*reciprocalSquare (N+k) at hm
  grind

end ComputableAnalysis.ModularForms
