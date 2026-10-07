import ComputableAnalysis.ModularForms.GeometricRotationEulerStability

/-! Executable mesh iteration and finite errors for the geometric rotation chart. -/
namespace ComputableAnalysis.ModularForms
open GeometricRotationODE

def geometricMeshStep (N : Nat) : Rat := 1/((N+1:Nat):Rat)

def geometricEulerMesh (N : Nat) : Nat → QComplex
  | 0 => QComplex.one
  | k+1 => geometricRotationEulerAt ((k:Rat)*geometricMeshStep N) (geometricMeshStep N)
      (geometricEulerMesh N k)

def geometricEulerMeshError (N : Nat) : Nat → Rat
  | 0 => 0
  | k+1 => (1+2*geometricMeshStep N)*geometricEulerMeshError N k+
      12*geometricMeshStep N*geometricMeshStep N

theorem geometricMeshStep_positive (N : Nat) : 0<geometricMeshStep N := by
  unfold geometricMeshStep
  rw [Rat.div_def,Rat.one_mul]
  exact Rat.inv_pos.mpr (by exact_mod_cast Nat.succ_pos N)

theorem geometricMeshStep_identity (N : Nat) : ((N+1:Nat):Rat)*geometricMeshStep N=1 := by
  unfold geometricMeshStep
  rw [Rat.div_def,Rat.one_mul]
  exact Rat.mul_inv_cancel _ (Rat.ne_of_gt (by exact_mod_cast Nat.succ_pos N))

theorem geometricEulerMeshError_nonnegative (N k : Nat) : 0≤geometricEulerMeshError N k := by
  have hh := Rat.le_of_lt (geometricMeshStep_positive N)
  induction k with
  | zero => exact Rat.le_refl
  | succ k ih =>
    change 0≤(1+2*geometricMeshStep N)*geometricEulerMeshError N k+12*geometricMeshStep N*geometricMeshStep N
    exact Rat.add_nonneg
      (Rat.mul_nonneg (Rat.add_nonneg (by decide) (Rat.mul_nonneg (by decide) hh)) ih)
      (Rat.mul_nonneg (Rat.mul_nonneg (by decide) hh) hh)

private theorem meshTime_bounds (N k : Nat) (hk : k≤N+1) :
    0≤(k:Rat)*geometricMeshStep N ∧ (k:Rat)*geometricMeshStep N≤1 := by
  have hh := Rat.le_of_lt (geometricMeshStep_positive N)
  have hk0 : (0:Rat)≤(k:Rat) := by exact_mod_cast Nat.zero_le k
  have hkd : (k:Rat)≤((N+1:Nat):Rat) := by exact_mod_cast hk
  have hm := Rat.mul_le_mul_of_nonneg_right hkd hh
  rw [geometricMeshStep_identity] at hm
  exact ⟨Rat.mul_nonneg hk0 hh,hm⟩

theorem geometricEulerMesh_error (N k : Nat) (hk : k≤N+1) :
    qabs ((geometricEulerMesh N k).re-(pointComplex ((k:Rat)*geometricMeshStep N)).re)≤geometricEulerMeshError N k ∧
    qabs ((geometricEulerMesh N k).im-(pointComplex ((k:Rat)*geometricMeshStep N)).im)≤geometricEulerMeshError N k := by
  induction k with
  | zero =>
    change qabs (QComplex.one.re-(pointComplex ((0:Rat)*geometricMeshStep N)).re)≤0 ∧
      qabs (QComplex.one.im-(pointComplex ((0:Rat)*geometricMeshStep N)).im)≤0
    rw [Rat.zero_mul,pointComplex_zero]
    constructor <;> rw [Rat.sub_self] <;> decide +kernel
  | succ k ih =>
    have hprev := ih (by omega)
    have htime := meshTime_bounds N k (by omega)
    have hnext := meshTime_bounds N (k+1) hk
    have he : ((k+1:Nat):Rat)*geometricMeshStep N=(k:Rat)*geometricMeshStep N+geometricMeshStep N := by
      rw [Rat.natCast_add]
      grind
    rw [he] at hnext
    have hb := geometricRotationEulerAt_error_step ((k:Rat)*geometricMeshStep N) (geometricMeshStep N)
      (geometricEulerMesh N k) (geometricEulerMeshError N k) htime.1 htime.2 hnext.1 hnext.2
      (geometricEulerMeshError_nonnegative N k) hprev.1 hprev.2
    rw [qabs_eq_self_of_nonneg (Rat.le_of_lt (geometricMeshStep_positive N))] at hb
    change qabs ((geometricRotationEulerAt ((k:Rat)*geometricMeshStep N) (geometricMeshStep N)
      (geometricEulerMesh N k)).re-(pointComplex (((k+1:Nat):Rat)*geometricMeshStep N)).re)≤_ ∧
      qabs ((geometricRotationEulerAt ((k:Rat)*geometricMeshStep N) (geometricMeshStep N)
      (geometricEulerMesh N k)).im-(pointComplex (((k+1:Nat):Rat)*geometricMeshStep N)).im)≤_
    rw [he]
    exact hb

theorem geometricEulerMesh_endpoint_error (N : Nat) :
    qabs ((geometricEulerMesh N (N+1)).re)≤geometricEulerMeshError N (N+1) ∧
    qabs ((geometricEulerMesh N (N+1)).im-1)≤geometricEulerMeshError N (N+1) := by
  have h := geometricEulerMesh_error N (N+1) (Nat.le_refl _)
  rw [geometricMeshStep_identity,pointComplex_one] at h
  simpa only [RotationSeries.imaginaryUnit,Rat.sub_eq_add_neg,Rat.neg_zero,Rat.add_zero] using h

end ComputableAnalysis.ModularForms
