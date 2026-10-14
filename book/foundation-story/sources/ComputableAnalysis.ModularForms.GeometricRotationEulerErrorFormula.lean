import ComputableAnalysis.ModularForms.GeometricRotationEulerMesh

/-! Closed rational formula for the geometric Euler mesh error majorant. -/
namespace ComputableAnalysis.ModularForms

theorem geometricEulerMeshError_closed (N k : Nat) :
    geometricEulerMeshError N k=
      6*geometricMeshStep N*((1+2*geometricMeshStep N)^k-1) := by
  induction k with
  | zero => simp only [geometricEulerMeshError,Rat.pow_zero,Rat.sub_self,Rat.mul_zero]
  | succ k ih =>
    rw [geometricEulerMeshError,ih,Rat.pow_succ]
    grind

theorem geometricEulerMesh_endpoint_closed_bound (N : Nat) :
    qabs ((geometricEulerMesh N (N+1)).re)≤
      6*geometricMeshStep N*((1+2*geometricMeshStep N)^(N+1)-1) ∧
    qabs ((geometricEulerMesh N (N+1)).im-1)≤
      6*geometricMeshStep N*((1+2*geometricMeshStep N)^(N+1)-1) := by
  have h := geometricEulerMesh_endpoint_error N
  rw [geometricEulerMeshError_closed] at h
  exact h

/-- A uniform amplification estimate turns the actual finite endpoint bound
into an inverse-mesh bound; the amplification estimate is separate evidence. -/
theorem geometricEulerMesh_endpoint_bound_of_amplification (N : Nat) (C : Rat)
    (hC : (1+2*geometricMeshStep N)^(N+1)≤C) :
    qabs ((geometricEulerMesh N (N+1)).re)≤6*(C-1)*geometricMeshStep N ∧
    qabs ((geometricEulerMesh N (N+1)).im-1)≤6*(C-1)*geometricMeshStep N := by
  have hb := geometricEulerMesh_endpoint_closed_bound N
  have hm := Rat.mul_le_mul_of_nonneg_left
    (show (1+2*geometricMeshStep N)^(N+1)-1≤C-1 by grind)
    (Rat.mul_nonneg (by decide : (0:Rat)≤6) (Rat.le_of_lt (geometricMeshStep_positive N)))
  have he : 6*geometricMeshStep N*(C-1)=6*(C-1)*geometricMeshStep N := by grind
  rw [he] at hm
  exact ⟨Rat.le_trans hb.1 hm,Rat.le_trans hb.2 hm⟩

theorem rationalEulerGrowth_product_bound (x : Rat) (hx : 0≤x) (k : Nat) :
    (1+x)^k*(1-(k:Rat)*x)≤1 := by
  induction k with
  | zero =>
    have he : ((0:Nat):Rat)=0 := by decide +kernel
    rw [he,Rat.pow_zero]
    grind
  | succ k ih =>
    have hp := Rat.pow_nonneg (Rat.add_nonneg (by decide : (0:Rat)≤1) hx) (n := k)
    have hk : (0:Rat)≤((k+1:Nat):Rat) := by exact_mod_cast Nat.zero_le (k+1)
    have herror := Rat.mul_nonneg hk (Rat.mul_nonneg hx hx)
    have hm := Rat.mul_nonneg hp herror
    rw [Rat.pow_succ,Rat.natCast_add]
    grind

theorem rationalEulerGrowth_short_bound (x : Rat) (hx : 0≤x) (k : Nat)
    (hk : (k:Rat)*x≤(1:Rat)/2) : (1+x)^k≤2 := by
  have hb := rationalEulerGrowth_product_bound x hx k
  have hp := Rat.pow_nonneg (Rat.add_nonneg (by decide : (0:Rat)≤1) hx) (n := k)
  have hm := Rat.mul_le_mul_of_nonneg_left
    (show (1:Rat)/2≤1-(k:Rat)*x by grind) hp
  grind

end ComputableAnalysis.ModularForms
