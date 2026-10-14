import ComputableAnalysis.ModularForms.UpperLatticeRegionalBounds
import ComputableAnalysis.ModularForms.UpperLatticeShells

/-! Shared regional bounds for actual reciprocal powers and finite shells. -/
namespace ComputableAnalysis.ModularForms
open RiemannHilbert FunctionTheory QuadraticOrder163

theorem latticePower_region_bound (z : Scalar) (hz : InUpperHalfPlane z.val)
    (R H eta : Rat) (N : Nat) (hR : 0≤R) (hH : 0≤H) (heta : 0<eta)
    (hregion : LatticeRegionBox z R eta N) (hheight : (z.val.compute N).hi.im≤H)
    (u : QuadraticOrder163) (hu : u≠QuadraticOrder163.zero) (k : Nat) :
    Small (LocalODE.power (latticeInverse z hz u hu).val k)
      ((2*(latticeRegionReciprocalConstant R H eta/(shellRadius u:Rat)))^k) := by
  have hr : 0<(shellRadius u:Rat) := by exact_mod_cast shellRadius_positive u hu
  exact LocalODE.power_small _ (latticeInverse z hz u hu).property _
    (Rat.mul_nonneg (latticeRegionReciprocalConstant_nonnegative R H eta hR hH heta)
      (Rat.le_of_lt (Rat.inv_pos.mpr hr)))
    (latticeInverse_region_radius_bound z hz R H eta N hR hH heta hregion hheight u hu) k

theorem upperShellTerm_region_bound (z : Scalar) (hz : InUpperHalfPlane z.val)
    (R H eta : Rat) (N : Nat) (hR : 0≤R) (hH : 0≤H) (heta : 0<eta)
    (hregion : LatticeRegionBox z R eta N) (hheight : (z.val.compute N).hi.im≤H)
    (r : Nat) (hr : 0<r) (k i : Nat) :
    Small (upperShellTerm z hz r hr k i)
      ((2*(latticeRegionReciprocalConstant R H eta/(r:Rat)))^k) := by
  unfold upperShellTerm
  split
  · rename_i hi
    have hb := latticePower_region_bound z hz R H eta N hR hH heta hregion hheight
      (shellPoint r ⟨i,hi⟩) (shellPoint_nonzero r hr ⟨i,hi⟩) k
    rw [shellRadius_shellPoint] at hb
    exact hb
  · have hrq : 0<(r:Rat) := by exact_mod_cast hr
    exact Small.zero (Rat.pow_nonneg (Rat.mul_nonneg (by decide)
      (Rat.mul_nonneg (latticeRegionReciprocalConstant_nonnegative R H eta hR hH heta)
        (Rat.le_of_lt (Rat.inv_pos.mpr hrq)))))

theorem upperShellPrefix_region_bound (z : Scalar) (hz : InUpperHalfPlane z.val)
    (R H eta : Rat) (N : Nat) (hR : 0≤R) (hH : 0≤H) (heta : 0<eta)
    (hregion : LatticeRegionBox z R eta N) (hheight : (z.val.compute N).hi.im≤H)
    (r : Nat) (hr : 0<r) (k n : Nat) :
    Small (upperShellPrefix z hz r hr k n)
      ((n:Rat)*(2*(latticeRegionReciprocalConstant R H eta/(r:Rat)))^k) := by
  induction n with
  | zero =>
    change Small ComplexRaw.zero ((0:Rat)*(2*(latticeRegionReciprocalConstant R H eta/(r:Rat)))^k)
    rw [Rat.zero_mul]
    exact Small.zero (by decide)
  | succ n ih =>
    have hb := LocalODE.small_add ih
      (upperShellTerm_region_bound z hz R H eta N hR hH heta hregion hheight r hr k n)
    have he : (n:Rat)*(2*(latticeRegionReciprocalConstant R H eta/(r:Rat)))^k+
        (2*(latticeRegionReciprocalConstant R H eta/(r:Rat)))^k=
        ((n+1:Nat):Rat)*(2*(latticeRegionReciprocalConstant R H eta/(r:Rat)))^k := by
      rw [Rat.natCast_add]
      grind only
    rw [he] at hb
    exact hb

theorem upperShellSum_region_bound (z : Scalar) (hz : InUpperHalfPlane z.val)
    (R H eta : Rat) (N : Nat) (hR : 0≤R) (hH : 0≤H) (heta : 0<eta)
    (hregion : LatticeRegionBox z R eta N) (hheight : (z.val.compute N).hi.im≤H)
    (r : Nat) (hr : 0<r) (k : Nat) :
    Small (upperShellSum z hz r hr k)
      (((8*r:Nat):Rat)*(2*(latticeRegionReciprocalConstant R H eta/(r:Rat)))^k) :=
  upperShellPrefix_region_bound z hz R H eta N hR hH heta hregion hheight r hr k _

end ComputableAnalysis.ModularForms
