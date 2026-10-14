import ComputableAnalysis.ModularForms.UpperDerivativeRegionalBounds

/-! Executable derivative shells and their shared regional majorants. -/
namespace ComputableAnalysis.ModularForms
open RiemannHilbert FunctionTheory QuadraticOrder163

def derivativeShellTerm (z : Scalar) (hz : InUpperHalfPlane z.val)
    (r : Nat) (hr : 0<r) (k i : Nat) : ComplexRaw :=
  if hi : i<8*r then
    ((latticePowerMap_holomorphic (shellPoint r ⟨i,hi⟩)
      (shellPoint_nonzero r hr ⟨i,hi⟩) k).derivative z hz).val
  else ComplexRaw.zero

theorem derivativeShellTerm_valid (z : Scalar) (hz : InUpperHalfPlane z.val)
    (r : Nat) (hr : 0<r) (k i : Nat) : (derivativeShellTerm z hz r hr k i).Valid := by
  unfold derivativeShellTerm
  split
  · exact ((latticePowerMap_holomorphic _ _ k).derivative z hz).property
  · exact ComplexRaw.ofQComplex_valid _

theorem derivativeShellTerm_region_bound (z : Scalar) (hz : InUpperHalfPlane z.val)
    (R H eta : Rat) (N : Nat) (hR : 0≤R) (hH : 0≤H) (heta : 0<eta)
    (hregion : LatticeRegionBox z R eta N) (hheight : (z.val.compute N).hi.im≤H)
    (r : Nat) (hr : 0<r) (k i : Nat) :
    Small (derivativeShellTerm z hz r hr k i)
      (2*((k:Rat)*(r:Rat))*(2*(latticeRegionReciprocalConstant R H eta/(r:Rat)))^(k+1)) := by
  unfold derivativeShellTerm
  split
  · rename_i hi
    have hb := latticePower_derivative_region_bound z hz R H eta N hR hH heta hregion hheight
      (shellPoint r ⟨i,hi⟩) (shellPoint_nonzero r hr ⟨i,hi⟩) k
    rw [shellRadius_shellPoint] at hb
    exact hb
  · have hrq : 0<(r:Rat) := by exact_mod_cast hr
    have hk : 0≤(k:Rat) := by exact_mod_cast Nat.zero_le k
    have hC := latticeRegionReciprocalConstant_nonnegative R H eta hR hH heta
    exact Small.zero (Rat.mul_nonneg
      (Rat.mul_nonneg (by decide) (Rat.mul_nonneg hk (Rat.le_of_lt hrq)))
      (Rat.pow_nonneg (Rat.mul_nonneg (by decide)
        (Rat.mul_nonneg hC (Rat.le_of_lt (Rat.inv_pos.mpr hrq))))))

def derivativeShellPrefix (z : Scalar) (hz : InUpperHalfPlane z.val)
    (r : Nat) (hr : 0<r) (k : Nat) : Nat → ComplexRaw
  | 0 => ComplexRaw.zero
  | n+1 => ComplexRaw.add (derivativeShellPrefix z hz r hr k n) (derivativeShellTerm z hz r hr k n)

theorem derivativeShellPrefix_valid (z : Scalar) (hz : InUpperHalfPlane z.val)
    (r : Nat) (hr : 0<r) (k n : Nat) : (derivativeShellPrefix z hz r hr k n).Valid := by
  induction n with
  | zero => exact ComplexRaw.ofQComplex_valid _
  | succ n ih => exact ComplexRaw.add_valid ih (derivativeShellTerm_valid z hz r hr k n)

theorem derivativeShellPrefix_region_bound (z : Scalar) (hz : InUpperHalfPlane z.val)
    (R H eta : Rat) (N : Nat) (hR : 0≤R) (hH : 0≤H) (heta : 0<eta)
    (hregion : LatticeRegionBox z R eta N) (hheight : (z.val.compute N).hi.im≤H)
    (r : Nat) (hr : 0<r) (k n : Nat) :
    Small (derivativeShellPrefix z hz r hr k n)
      ((n:Rat)*(2*((k:Rat)*(r:Rat))*(2*(latticeRegionReciprocalConstant R H eta/(r:Rat)))^(k+1))) := by
  induction n with
  | zero =>
    change Small ComplexRaw.zero ((0:Rat)*_)
    rw [Rat.zero_mul]
    exact Small.zero (by decide)
  | succ n ih =>
    have hb := LocalODE.small_add ih
      (derivativeShellTerm_region_bound z hz R H eta N hR hH heta hregion hheight r hr k n)
    have he : (n:Rat)*(2*((k:Rat)*(r:Rat))*(2*(latticeRegionReciprocalConstant R H eta/(r:Rat)))^(k+1))+
        (2*((k:Rat)*(r:Rat))*(2*(latticeRegionReciprocalConstant R H eta/(r:Rat)))^(k+1))=
        ((n+1:Nat):Rat)*(2*((k:Rat)*(r:Rat))*(2*(latticeRegionReciprocalConstant R H eta/(r:Rat)))^(k+1)) := by
      rw [Rat.natCast_add]
      grind only
    rw [he] at hb
    exact hb

def derivativeShellSum (z : Scalar) (hz : InUpperHalfPlane z.val)
    (r : Nat) (hr : 0<r) (k : Nat) : ComplexRaw := derivativeShellPrefix z hz r hr k (8*r)

theorem derivativeShellSum_region_bound (z : Scalar) (hz : InUpperHalfPlane z.val)
    (R H eta : Rat) (N : Nat) (hR : 0≤R) (hH : 0≤H) (heta : 0<eta)
    (hregion : LatticeRegionBox z R eta N) (hheight : (z.val.compute N).hi.im≤H)
    (r : Nat) (hr : 0<r) (k : Nat) :
    Small (derivativeShellSum z hz r hr k)
      (((8*r:Nat):Rat)*(2*((k:Rat)*(r:Rat))*(2*(latticeRegionReciprocalConstant R H eta/(r:Rat)))^(k+1))) :=
  derivativeShellPrefix_region_bound z hz R H eta N hR hH heta hregion hheight r hr k _

end ComputableAnalysis.ModularForms
