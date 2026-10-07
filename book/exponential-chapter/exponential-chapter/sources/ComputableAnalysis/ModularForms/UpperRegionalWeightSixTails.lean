import ComputableAnalysis.ModularForms.UpperRegionalShellBounds
import ComputableAnalysis.ModularForms.UpperWeightSixTails
import ComputableAnalysis.ModularForms.CMWeightSixTailRate163

/-! Summable weight-six shell bounds at every represented upper-half-plane input. -/
namespace ComputableAnalysis.ModularForms
open RiemannHilbert FunctionTheory QuadraticOrder163

def regionalWeightSixTailConstant (R H eta : Rat) : Rat := 8*(2*latticeRegionReciprocalConstant R H eta)^6

theorem regionalWeightSixShell_small (z : Scalar) (hz : InUpperHalfPlane z.val)
    (R H eta : Rat) (S : Nat) (hR : 0≤R) (hH : 0≤H) (heta : 0<eta)
    (hregion : LatticeRegionBox z R eta S) (hheight : (z.val.compute S).hi.im≤H) (r : Nat) (hr : 0<r) :
    Small (upperShellSum z hz r hr 6) (regionalWeightSixTailConstant R H eta*reciprocalCube r) := by
  have h := upperShellSum_region_bound z hz R H eta S hR hH heta hregion hheight r hr 6
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
  unfold regionalWeightSixTailConstant reciprocalCube
  rw [Rat.natCast_mul]
  apply Rat.le_of_mul_le_mul_right (c := a*a*a*a*a*a)
  · calc
      _ = 8*(2*latticeRegionReciprocalConstant R H eta)^6*a := by
        simp only [Rat.pow_succ,Rat.pow_zero]
        grind [Rat.div_def]
      _ ≤ 8*(2*latticeRegionReciprocalConstant R H eta)^6*(a*a*a) := by
        exact Rat.mul_le_mul_of_nonneg_left h3 (Rat.mul_nonneg (by decide) (Rat.pow_nonneg (Rat.mul_nonneg (by decide) (latticeRegionReciprocalConstant_nonnegative R H eta hR hH heta))))
      _ = _ := by
        simp only [Rat.pow_succ,Rat.pow_zero]
        grind
  · exact Rat.mul_pos (Rat.mul_pos (Rat.mul_pos (Rat.mul_pos (Rat.mul_pos hp hp) hp) hp) hp) hp

theorem regionalWeightSixTailBlock_small (z : Scalar) (hz : InUpperHalfPlane z.val)
    (R H eta : Rat) (S : Nat) (hR : 0≤R) (hH : 0≤H) (heta : 0<eta)
    (hregion : LatticeRegionBox z R eta S) (hheight : (z.val.compute S).hi.im≤H) (N k : Nat) (hN : 0<N) :
    Small (upperWeightSixTailBlock z hz N k)
      (regionalWeightSixTailConstant R H eta*(reciprocalSquare N-reciprocalSquare (N+k))) := by
  have hC : 0≤regionalWeightSixTailConstant R H eta := by
    unfold regionalWeightSixTailConstant
    exact Rat.mul_nonneg (by decide) (Rat.pow_nonneg
      (Rat.mul_nonneg (by decide) (latticeRegionReciprocalConstant_nonnegative R H eta hR hH heta)))
  induction k with
  | zero =>
    have he : regionalWeightSixTailConstant R H eta*(reciprocalSquare N-reciprocalSquare (N+0))=0 := by grind
    rw [he]
    exact Small.zero (by decide)
  | succ k ih =>
    have hs := regionalWeightSixShell_small z hz R H eta S hR hH heta hregion hheight (N+k+1) (by omega)
    have ht := reciprocalCube_step (N+k) (by omega)
    have hm := Rat.mul_le_mul_of_nonneg_left ht hC
    have hsum := LocalODE.small_add ih hs
    apply hsum.mono
    have he : N+(k+1)=N+k+1 := by omega
    rw [he]
    grind

theorem regionalWeightSixTailBlock_uniform_small (z : Scalar) (hz : InUpperHalfPlane z.val)
    (R H eta : Rat) (S : Nat) (hR : 0≤R) (hH : 0≤H) (heta : 0<eta)
    (hregion : LatticeRegionBox z R eta S) (hheight : (z.val.compute S).hi.im≤H) (N k : Nat) (hN : 0<N) :
    Small (upperWeightSixTailBlock z hz N k) (regionalWeightSixTailConstant R H eta*reciprocalSquare N) := by
  apply (regionalWeightSixTailBlock_small z hz R H eta S hR hH heta hregion hheight N k hN).mono
  have hp : (0:Rat)<((N+k:Nat):Rat) := by exact_mod_cast (show 0<N+k by omega)
  have hi := Rat.le_of_lt ((Rat.inv_pos).mpr (Rat.mul_pos hp hp))
  have hC : 0≤regionalWeightSixTailConstant R H eta := by
    unfold regionalWeightSixTailConstant
    exact Rat.mul_nonneg (by decide) (Rat.pow_nonneg
      (Rat.mul_nonneg (by decide) (latticeRegionReciprocalConstant_nonnegative R H eta hR hH heta)))
  have hm := Rat.mul_nonneg hC hi
  change 0≤regionalWeightSixTailConstant R H eta*reciprocalSquare (N+k) at hm
  grind

end ComputableAnalysis.ModularForms
