import ComputableAnalysis.ModularForms.UpperPowerRemainderBounds
import ComputableAnalysis.ModularForms.UpperRegionalShellBounds

/-! Regional quadratic remainder estimates for the actual inverse-power maps. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory QuadraticOrder163

theorem latticePower_remainder_region_bound
    (a z : Scalar) (ha : InUpperHalfPlane a.val) (hz : InUpperHalfPlane z.val)
    (R U eta : Rat) (A Z : Nat) (hR : 0≤R) (hU : 0≤U) (heta : 0<eta)
    (hregionA : LatticeRegionBox a R eta A) (hheightA : (a.val.compute A).hi.im≤U)
    (hregionZ : LatticeRegionBox z R eta Z) (hheightZ : (z.val.compute Z).hi.im≤U)
    (H : Rat) (hH : 0≤H) (hza : Small (sub z.val a.val) H)
    (u : QuadraticOrder163) (hu : u≠QuadraticOrder163.zero) (k : Nat) :
    Small (latticePowerRemainder u hu a z ha hz k)
      (powerRemainderCoefficient (latticeRegionReciprocalConstant R U eta/(shellRadius u:Rat)) k*
        (shellRadius u:Rat)*(shellRadius u:Rat)*H*H) := by
  let r : Rat := shellRadius u
  have hr : 0<r := by dsimp [r]; exact_mod_cast shellRadius_positive u hu
  have hy := shellRadius_bounds u
  have hyl : -r≤(u.y:Rat) := by
    simpa only [Rat.intCast_neg,Rat.intCast_natCast] using Rat.intCast_le_intCast.mpr hy.2.2.1
  have hyh : (u.y:Rat)≤r := by
    simpa only [Rat.intCast_natCast] using Rat.intCast_le_intCast.mpr hy.2.2.2.1
  have hs : Small (ofQComplex ⟨(u.y:Rat),0⟩) r := by
    refine ⟨?_,?_,?_,?_⟩
    · intro n m; exact hyl
    · intro n m; exact hyh
    · intro n m; change -r≤0; grind only
    · intro n m; exact Rat.le_of_lt hr
  have hC := latticeRegionReciprocalConstant_nonnegative R U eta hR hU heta
  have hB : 0≤latticeRegionReciprocalConstant R U eta/r :=
    Rat.mul_nonneg hC (Rat.le_of_lt (Rat.inv_pos.mpr hr))
  exact latticePower_remainder_bound u hu a z ha hz _ r H hB (Rat.le_of_lt hr) hH
    (latticeInverse_region_radius_bound a ha R U eta A hR hU heta hregionA hheightA u hu)
    (latticeInverse_region_radius_bound z hz R U eta Z hR hU heta hregionZ hheightZ u hu) hs hza k

theorem latticePower_remainder_region_scaled_bound
    (a z : Scalar) (ha : InUpperHalfPlane a.val) (hz : InUpperHalfPlane z.val)
    (R U eta : Rat) (A Z : Nat) (hR : 0≤R) (hU : 0≤U) (heta : 0<eta)
    (hregionA : LatticeRegionBox a R eta A) (hheightA : (a.val.compute A).hi.im≤U)
    (hregionZ : LatticeRegionBox z R eta Z) (hheightZ : (z.val.compute Z).hi.im≤U)
    (H : Rat) (hH : 0≤H) (hza : Small (sub z.val a.val) H)
    (u : QuadraticOrder163) (hu : u≠QuadraticOrder163.zero) (k : Nat) :
    Small (latticePowerRemainder u hu a z ha hz k)
      (powerRemainderCoefficient (latticeRegionReciprocalConstant R U eta) k*
        ((shellRadius u:Rat)⁻¹)^(k+2)*(shellRadius u:Rat)*(shellRadius u:Rat)*H*H) := by
  have h := latticePower_remainder_region_bound a z ha hz R U eta A Z hR hU heta
    hregionA hheightA hregionZ hheightZ H hH hza u hu k
  rw [Rat.div_def,powerRemainderCoefficient_scale] at h
  exact h

theorem latticePower_remainder_region_decay_bound
    (a z : Scalar) (ha : InUpperHalfPlane a.val) (hz : InUpperHalfPlane z.val)
    (R U eta : Rat) (A Z : Nat) (hR : 0≤R) (hU : 0≤U) (heta : 0<eta)
    (hregionA : LatticeRegionBox a R eta A) (hheightA : (a.val.compute A).hi.im≤U)
    (hregionZ : LatticeRegionBox z R eta Z) (hheightZ : (z.val.compute Z).hi.im≤U)
    (H : Rat) (hH : 0≤H) (hza : Small (sub z.val a.val) H)
    (u : QuadraticOrder163) (hu : u≠QuadraticOrder163.zero) (k : Nat) :
    Small (latticePowerRemainder u hu a z ha hz k)
      (powerRemainderCoefficient (latticeRegionReciprocalConstant R U eta) k*
        ((shellRadius u:Rat)⁻¹)^k*H*H) := by
  have h := latticePower_remainder_region_scaled_bound a z ha hz R U eta A Z hR hU heta
    hregionA hheightA hregionZ hheightZ H hH hza u hu k
  have hr : (0:Rat)<(shellRadius u:Rat) := by exact_mod_cast shellRadius_positive u hu
  have hc := Rat.mul_inv_cancel (shellRadius u:Rat) (Rat.ne_of_gt hr)
  have he : powerRemainderCoefficient (latticeRegionReciprocalConstant R U eta) k*
      ((shellRadius u:Rat)⁻¹)^(k+2)*(shellRadius u:Rat)*(shellRadius u:Rat)*H*H =
      powerRemainderCoefficient (latticeRegionReciprocalConstant R U eta) k*
      ((shellRadius u:Rat)⁻¹)^k*H*H := by
    simp only [Rat.pow_succ]
    grind only
  rw [he] at h
  exact h

end ComputableAnalysis.ModularForms
