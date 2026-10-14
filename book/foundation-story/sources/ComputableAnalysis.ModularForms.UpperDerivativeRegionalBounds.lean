import ComputableAnalysis.ModularForms.UpperPowerDerivative
import ComputableAnalysis.ModularForms.UpperRegionalShellBounds

/-! Regional majorants for the actual holomorphic inverse-power derivatives. -/
namespace ComputableAnalysis.ModularForms
open RiemannHilbert FunctionTheory ComplexRaw QuadraticOrder163

theorem latticePower_derivative_region_bound (z : Scalar) (hz : InUpperHalfPlane z.val)
    (R H eta : Rat) (N : Nat) (hR : 0≤R) (hH : 0≤H) (heta : 0<eta)
    (hregion : LatticeRegionBox z R eta N) (hheight : (z.val.compute N).hi.im≤H)
    (u : QuadraticOrder163) (hu : u≠QuadraticOrder163.zero) (k : Nat) :
    Small ((latticePowerMap_holomorphic u hu k).derivative z hz).val
      (2*((k:Rat)*(shellRadius u:Rat))*
        (2*(latticeRegionReciprocalConstant R H eta/(shellRadius u:Rat)))^(k+1)) := by
  let r : Rat := shellRadius u
  have hr : 0<r := by dsimp [r]; exact_mod_cast shellRadius_positive u hu
  have hk : 0≤(k:Rat) := by exact_mod_cast Nat.zero_le k
  have hy := shellRadius_bounds u
  have hyl : -r≤(u.y:Rat) := by
    simpa only [Rat.intCast_neg,Rat.intCast_natCast] using
      Rat.intCast_le_intCast.mpr hy.2.2.1
  have hyh : (u.y:Rat)≤r := by
    simpa only [Rat.intCast_natCast] using Rat.intCast_le_intCast.mpr hy.2.2.2.1
  have hlo := Rat.mul_le_mul_of_nonneg_left hyl hk
  have hhi := Rat.mul_le_mul_of_nonneg_left hyh hk
  have hkr := Rat.mul_nonneg hk (Rat.le_of_lt hr)
  have hs : Small (ofQComplex ⟨((- (k:Int)*u.y):Rat),0⟩) ((k:Rat)*r) := by
    simp only [Rat.intCast_mul,Rat.intCast_neg,Rat.intCast_natCast]
    refine ⟨?_,?_,?_,?_⟩
    · intro n m; change -((k:Rat)*r)≤ -(k:Rat)*(u.y:Rat); grind only
    · intro n m; change -(k:Rat)*(u.y:Rat)≤(k:Rat)*r; grind only
    · intro n m; change -((k:Rat)*r)≤0; grind only
    · intro n m; change (0:Rat)≤(k:Rat)*r; exact hkr
  have hC := latticeRegionReciprocalConstant_nonnegative R H eta hR hH heta
  have hp : 0≤(2*(latticeRegionReciprocalConstant R H eta/r))^(k+1) := Rat.pow_nonneg (Rat.mul_nonneg (by decide)
    (Rat.mul_nonneg hC (Rat.le_of_lt (Rat.inv_pos.mpr hr))))
  have hb := Small.mul (ofQComplex_valid _)
    (LocalODE.power_valid _ (latticeInverse z hz u hu).property (k+1)) hkr hp hs
    (latticePower_region_bound z hz R H eta N hR hH heta hregion hheight u hu (k+1))
  exact Small.congr
    (mul_valid (ofQComplex_valid _) (LocalODE.power_valid _ (latticeInverse z hz u hu).property (k+1)))
    ((latticePowerMap_holomorphic u hu k).derivative z hz).property
    (equiv_symm (latticePower_derivative u hu z hz k)) hb

end ComputableAnalysis.ModularForms
