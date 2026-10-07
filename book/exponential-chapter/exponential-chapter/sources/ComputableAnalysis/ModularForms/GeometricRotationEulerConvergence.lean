import ComputableAnalysis.ModularForms.GeometricRotationEulerErrorFormula

/-! A shrinking error rate for executable geometric Euler endpoints. -/
namespace ComputableAnalysis.ModularForms

/-- Four equal blocks keep each growth estimate in its proved short range. -/
def geometricConvergenceMesh (N : Nat) : Nat := 4*(N+1)-1

theorem geometricConvergenceMesh_count (N : Nat) : geometricConvergenceMesh N+1=4*(N+1) := by
  unfold geometricConvergenceMesh
  omega

private theorem ratPower_add (x : Rat) (m n : Nat) : x^(m+n)=x^m*x^n := by
  induction n with
  | zero => simp only [Nat.add_zero,Rat.pow_zero,Rat.mul_one]
  | succ n ih =>
    rw [show m+(n+1)=(m+n)+1 by omega,Rat.pow_succ,ih,Rat.pow_succ]
    grind

theorem geometricEulerMesh_amplification_bound (N : Nat) :
    (1+2*geometricMeshStep (geometricConvergenceMesh N))^(geometricConvergenceMesh N+1)≤16 := by
  let h := geometricMeshStep (geometricConvergenceMesh N)
  have hh : 0≤h := Rat.le_of_lt (geometricMeshStep_positive _)
  have hc := geometricMeshStep_identity (geometricConvergenceMesh N)
  rw [geometricConvergenceMesh_count,Rat.natCast_mul] at hc
  have hblock : ((N+1:Nat):Rat)*(2*h)≤(1:Rat)/2 := by
    change ((4:Nat):Rat)*((N+1:Nat):Rat)*h=1 at hc
    have h4 : ((4:Nat):Rat)=4 := by decide +kernel
    rw [h4] at hc
    grind
  have hb := rationalEulerGrowth_short_bound (2*h) (Rat.mul_nonneg (by decide) hh) (N+1) hblock
  have hp : 0≤(1+2*h)^(N+1) := Rat.pow_nonneg (Rat.add_nonneg (by decide : (0:Rat)≤1)
    (Rat.mul_nonneg (by decide) hh)) (n := N+1)
  have hs1 := Rat.mul_le_mul_of_nonneg_left hb hp
  have hs2 := Rat.mul_le_mul_of_nonneg_right hb (by decide : (0:Rat)≤2)
  have hs : ((1+2*h)^(N+1))*((1+2*h)^(N+1))≤4 := by grind
  have hsp := Rat.mul_nonneg hp hp
  have ht1 := Rat.mul_le_mul_of_nonneg_left hs hsp
  have ht2 := Rat.mul_le_mul_of_nonneg_right hs (by decide : (0:Rat)≤4)
  rw [geometricConvergenceMesh_count]
  have hidx : 4*(N+1)=((N+1)+(N+1))+((N+1)+(N+1)) := by omega
  rw [hidx,ratPower_add,ratPower_add]
  change (((1+2*h)^(N+1))*((1+2*h)^(N+1)))*
    (((1+2*h)^(N+1))*((1+2*h)^(N+1)))≤16
  grind

def geometricEulerEndpointRate (N : Nat) : Rat := 90*geometricMeshStep (geometricConvergenceMesh N)

theorem geometricEulerEndpointRate_shrinks : ShrinksToZero geometricEulerEndpointRate := by
  apply shrinksToZero_of_natOverSuccBound (C := 90)
  intro N
  have hh := Rat.le_of_lt (geometricMeshStep_positive (geometricConvergenceMesh N))
  have hc := geometricMeshStep_identity (geometricConvergenceMesh N)
  rw [geometricConvergenceMesh_count,Rat.natCast_mul] at hc
  have h4 : ((4:Nat):Rat)=4 := by decide +kernel
  rw [h4] at hc
  have hp : (0:Rat)<((N+1:Nat):Rat) := by exact_mod_cast Nat.succ_pos N
  have hi := Rat.mul_inv_cancel ((N+1:Nat):Rat) (Rat.ne_of_gt hp)
  unfold geometricEulerEndpointRate
  apply Rat.le_of_mul_le_mul_right (c := ((N+1:Nat):Rat))
  · grind [Rat.div_def]
  · exact hp

theorem geometricEulerEndpoint_error (N : Nat) :
    qabs ((geometricEulerMesh (geometricConvergenceMesh N) (geometricConvergenceMesh N+1)).re)≤
      geometricEulerEndpointRate N ∧
    qabs ((geometricEulerMesh (geometricConvergenceMesh N) (geometricConvergenceMesh N+1)).im-1)≤
      geometricEulerEndpointRate N := by
  have hb := geometricEulerMesh_endpoint_bound_of_amplification (geometricConvergenceMesh N) 16
    (geometricEulerMesh_amplification_bound N)
  have he : (6:Rat)*(16-1)=90 := by decide +kernel
  rw [he] at hb
  exact hb

end ComputableAnalysis.ModularForms
