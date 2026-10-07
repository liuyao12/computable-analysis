import ComputableAnalysis.ModularForms.UpperRegionalShellBounds
import ComputableAnalysis.ModularForms.UpperWeightFourTails
import ComputableAnalysis.ModularForms.CMWeightFourTailRate163

/-! Summable weight-four shell bounds at every represented upper-half-plane input. -/
namespace ComputableAnalysis.ModularForms
open RiemannHilbert FunctionTheory QuadraticOrder163

def regionalWeightFourTailConstant (R H eta : Rat) : Rat := 8*(2*latticeRegionReciprocalConstant R H eta)^4

theorem regionalWeightFourShell_small (z : Scalar) (hz : InUpperHalfPlane z.val)
    (R H eta : Rat) (S : Nat) (hR : 0≤R) (hH : 0≤H) (heta : 0<eta)
    (hregion : LatticeRegionBox z R eta S) (hheight : (z.val.compute S).hi.im≤H) (r : Nat) (hr : 0<r) :
    Small (upperShellSum z hz r hr 4) (regionalWeightFourTailConstant R H eta*reciprocalCube r) := by
  have h := upperShellSum_region_bound z hz R H eta S hR hH heta hregion hheight r hr 4
  have hp : (0:Rat)<(r:Rat) := by exact_mod_cast hr
  have hc := Rat.mul_inv_cancel (r:Rat) (Rat.ne_of_gt hp)
  have hp3 : (r:Rat)*(r:Rat)*(r:Rat)≠0 :=
    Rat.ne_of_gt (Rat.mul_pos (Rat.mul_pos hp hp) hp)
  have hc3 := Rat.mul_inv_cancel _ hp3
  have he : (((8*r:Nat):Rat)*((2*(latticeRegionReciprocalConstant R H eta/(r:Rat)))^4))=regionalWeightFourTailConstant R H eta*reciprocalCube r := by
    unfold regionalWeightFourTailConstant reciprocalCube
    rw [Rat.natCast_mul]
    simp only [Rat.pow_succ,Rat.pow_zero]
    grind [Rat.div_def]
  rw [he] at h
  exact h

theorem regionalWeightFourTailBlock_small (z : Scalar) (hz : InUpperHalfPlane z.val)
    (R H eta : Rat) (S : Nat) (hR : 0≤R) (hH : 0≤H) (heta : 0<eta)
    (hregion : LatticeRegionBox z R eta S) (hheight : (z.val.compute S).hi.im≤H) (N k : Nat) (hN : 0<N) :
    Small (upperWeightFourTailBlock z hz N k)
      (regionalWeightFourTailConstant R H eta*(reciprocalSquare N-reciprocalSquare (N+k))) := by
  have hC : 0≤regionalWeightFourTailConstant R H eta := by
    unfold regionalWeightFourTailConstant
    exact Rat.mul_nonneg (by decide) (Rat.pow_nonneg
      (Rat.mul_nonneg (by decide) (latticeRegionReciprocalConstant_nonnegative R H eta hR hH heta)))
  induction k with
  | zero =>
    have he : regionalWeightFourTailConstant R H eta*(reciprocalSquare N-reciprocalSquare (N+0))=0 := by grind
    rw [he]
    exact Small.zero (by decide)
  | succ k ih =>
    have hs := regionalWeightFourShell_small z hz R H eta S hR hH heta hregion hheight (N+k+1) (by omega)
    have ht := reciprocalCube_step (N+k) (by omega)
    have hm := Rat.mul_le_mul_of_nonneg_left ht hC
    have hsum := LocalODE.small_add ih hs
    apply hsum.mono
    have he : N+(k+1)=N+k+1 := by omega
    rw [he]
    grind

theorem regionalWeightFourTailBlock_uniform_small (z : Scalar) (hz : InUpperHalfPlane z.val)
    (R H eta : Rat) (S : Nat) (hR : 0≤R) (hH : 0≤H) (heta : 0<eta)
    (hregion : LatticeRegionBox z R eta S) (hheight : (z.val.compute S).hi.im≤H) (N k : Nat) (hN : 0<N) :
    Small (upperWeightFourTailBlock z hz N k) (regionalWeightFourTailConstant R H eta*reciprocalSquare N) := by
  apply (regionalWeightFourTailBlock_small z hz R H eta S hR hH heta hregion hheight N k hN).mono
  have hp : (0:Rat)<((N+k:Nat):Rat) := by exact_mod_cast (show 0<N+k by omega)
  have hi := Rat.le_of_lt ((Rat.inv_pos).mpr (Rat.mul_pos hp hp))
  have hC : 0≤regionalWeightFourTailConstant R H eta := by
    unfold regionalWeightFourTailConstant
    exact Rat.mul_nonneg (by decide) (Rat.pow_nonneg
      (Rat.mul_nonneg (by decide) (latticeRegionReciprocalConstant_nonnegative R H eta hR hH heta)))
  have hm := Rat.mul_nonneg hC hi
  change 0≤regionalWeightFourTailConstant R H eta*reciprocalSquare (N+k) at hm
  grind

end ComputableAnalysis.ModularForms
