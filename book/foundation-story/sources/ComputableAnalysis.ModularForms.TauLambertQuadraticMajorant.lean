import ComputableAnalysis.ModularForms.TauLambertCubicMajorant

/-! Pure geometric majorants for weighted Lambert quadratic errors. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

private theorem power_le_one (t : Rat) (ht : 0≤t) (hmax : t≤1) (N : Nat) : t^N≤1 := by
  induction N with
  | zero => rw [Rat.pow_zero]; exact Rat.le_refl
  | succ N ih =>
    have h := Rat.mul_le_mul_of_nonneg_right ih ht
    rw [Rat.pow_succ]
    grind only

/-- The full higher-term quadratic coefficient has a summable geometric bound. -/
theorem tauLambertQuadratic_coefficient_bound (H : Rat) (N : Nat) :
    ((N+2:Nat):Rat)*(1024*(2*((N+2:Nat):Rat)*(2*(1/1024:Rat))^(N+1)*H)^2+
      64*(2*((N+2:Nat):Rat)*((N+1:Nat):Rat)*(2*(1/1024:Rat))^N*H^2)) ≤
      33792*(1/64:Rat)^N*H^2 := by
  let t : Rat := 2*(1/1024)
  let x : Rat := t^N
  let u : Rat := ((N+2:Nat):Rat)
  let v : Rat := ((N+1:Nat):Rat)
  have ht : 0≤t := by decide +kernel
  have ht1 : t≤1 := by decide +kernel
  have hx : 0≤x := Rat.pow_nonneg ht
  have hx1 : x≤1 := power_le_one t ht ht1 N
  have hu : 0≤u := Rat.natCast_nonneg
  have hv : 0≤v := Rat.natCast_nonneg
  have hvu : v≤u := by
    dsimp [u,v]
    simp only [Rat.natCast_add]
    grind only
  have hxt := Rat.mul_le_mul_of_nonneg_left ht1 hx
  have hxt0 : 0≤x*t := Rat.mul_nonneg hx ht
  have hxt1 : x*t≤1 := by grind only
  have hs1 := Rat.mul_le_mul_of_nonneg_left hxt1 hxt0
  have hs : (x*t)*(x*t)≤x := by grind only
  have hH : 0≤H^2 := by
    rw [Rat.pow_succ, Rat.pow_one]
    by_cases h : 0≤H
    · exact Rat.mul_nonneg h h
    · have hn : 0≤-H := by grind only
      have hh := Rat.mul_nonneg hn hn
      grind only
  have hc0 : 0≤4096*u^3*H^2 := Rat.mul_nonneg
    (Rat.mul_nonneg (by decide +kernel) (Rat.pow_nonneg hu)) hH
  have h1 := Rat.mul_le_mul_of_nonneg_left hs hc0
  have hc1 : 0≤128*u^2*x*H^2 := Rat.mul_nonneg
    (Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) (Rat.pow_nonneg hu)) hx) hH
  have h2 := Rat.mul_le_mul_of_nonneg_left hvu hc1
  have hg := tauLambertIndex_cube_geometric_bound t ht N
  have h3 := Rat.mul_le_mul_of_nonneg_right hg (Rat.mul_nonneg (by decide +kernel : (0:Rat)≤4224) hH)
  have he : 8*t=(1/64:Rat) := by decide +kernel
  rw [he] at h3
  change u*(1024*(2*u*t^(N+1)*H)^2+64*(2*u*v*x*H^2))≤33792*(1/64:Rat)^N*H^2
  rw [Rat.pow_succ t N]
  change u*(1024*(2*u*(x*t)*H)^2+64*(2*u*v*x*H^2))≤33792*(1/64:Rat)^N*H^2
  simp only [Rat.pow_succ, Rat.pow_zero, Rat.mul_one] at h1 h2 h3 ⊢
  grind only

/-- Actual higher weighted term remainders satisfy the geometric majorant. -/
theorem tauWeightedLambertOne_geometric_remainder_bound (a z : Scalar)
    (ha : tauEulerNomeDomain a) (hz : tauEulerNomeDomain z)
    (H : Rat) (hH : 0≤H) (hd : Small (sub z.val a.val) H) (N : Nat) :
    Small (SeriesLimitLaws.remainder ((tauWeightedLambertMap 1 (N+1)).eval z hz).val
      ((tauWeightedLambertMap 1 (N+1)).eval a ha).val
      ((tauWeightedLambertMap_holomorphic 1 (N+1)).derivative a ha).val (sub z.val a.val))
      (33792*(1/64:Rat)^N*H^2) :=
  (tauWeightedLambertOne_actual_remainder_bound a z ha hz H hH hd N).mono
    (tauLambertQuadratic_coefficient_bound H N)

end ComputableAnalysis.ModularForms
