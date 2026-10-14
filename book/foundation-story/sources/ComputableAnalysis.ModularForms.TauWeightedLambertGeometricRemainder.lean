import ComputableAnalysis.ModularForms.TauWeightedLambertHigherRemainder
import ComputableAnalysis.ModularForms.TauLambertQuadraticMajorant

/-! Geometric majorants for actual higher weighted Lambert remainders. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

private theorem product_power (a b : Rat) (N : Nat) : a^N*b^N=(a*b)^N := by
  induction N with
  | zero => simp only [Rat.pow_zero]; grind only
  | succ N ih => rw [Rat.pow_succ,Rat.pow_succ,Rat.pow_succ]; grind only

private theorem power_commute (a : Rat) (N k : Nat) : (a^N)^k=(a^k)^N := by
  induction N with
  | zero =>
    rw [Rat.pow_zero,Rat.pow_zero]
    induction k with
    | zero => rfl
    | succ k ih => rw [Rat.pow_succ,ih]; exact Rat.one_mul 1
  | succ N ih => rw [Rat.pow_succ,←product_power,ih,Rat.pow_succ]

/-- Any fixed index power is controlled by an explicit geometric sequence. -/
theorem tauLambertIndex_power_bound (N k : Nat) :
    ((N+2:Nat):Rat)^k≤2^k*(2^k:Rat)^N := by
  have hi := lambertIndex_bound (N+1)
  have hx : 0≤((N+2:Nat):Rat) := Rat.natCast_nonneg
  have hy : 0≤(2:Rat)^(N+1) := Rat.pow_nonneg (by decide +kernel)
  have hp : ((N+2:Nat):Rat)^k≤((2:Rat)^(N+1))^k := by
    induction k with
    | zero => simp only [Rat.pow_zero]; exact Rat.le_refl
    | succ k ih =>
      rw [Rat.pow_succ,Rat.pow_succ]
      exact Rat.le_trans (Rat.mul_le_mul_of_nonneg_right ih hx)
        (Rat.mul_le_mul_of_nonneg_left hi (Rat.pow_nonneg hy))
  rw [power_commute,Rat.pow_succ] at hp
  have he : ((2:Rat)^k)^N*2^k=2^k*(2^k:Rat)^N := by grind only
  rw [he] at hp
  exact hp

/-- The full higher-degree quadratic coefficient has an explicit geometric majorant. -/
theorem tauWeightedLambertQuadratic_coefficient_bound (k N : Nat) (H : Rat) :
    (((N+2:Nat):Rat)^k)*(1024*(2*((N+2:Nat):Rat)*(2*(1/1024:Rat))^(N+1)*H)^2+
      64*(2*((N+2:Nat):Rat)*((N+1:Nat):Rat)*(2*(1/1024:Rat))^N*H^2))≤
      (33792*2^k)*(2^k*(1/64:Rat))^N*H^2 := by
  let u : Rat := ((N+2:Nat):Rat)
  let b : Rat := 1024*(2*u*(2*(1/1024:Rat))^(N+1)*H)^2+
    64*(2*u*((N+1:Nat):Rat)*(2*(1/1024:Rat))^N*H^2)
  have hu : 0≤u := Rat.natCast_nonneg
  have hu1 : 1≤u := by
    dsimp [u]
    have h : 1≤N+2 := by omega
    exact_mod_cast h
  have square_nonneg (x : Rat) : 0≤x^2 := by
    rw [Rat.pow_succ,Rat.pow_one]
    by_cases h : 0≤x
    · exact Rat.mul_nonneg h h
    · have hn : 0≤-x := by grind only
      have he := Rat.mul_nonneg hn hn
      grind only
  have hs := square_nonneg H
  have hb : 0≤b := by
    dsimp [b]
    have hfirst := Rat.mul_nonneg (show (0:Rat)≤1024 by decide +kernel)
      (square_nonneg (2*u*(2*(1/1024:Rat))^(N+1)*H))
    have hsecond : 0≤64*(2*u*((N+1:Nat):Rat)*(2*(1/1024:Rat))^N*H^2) := Rat.mul_nonneg (show (0:Rat)≤64 by decide +kernel)
      (Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg
        (Rat.mul_nonneg (show (0:Rat)≤2 by decide +kernel) hu) Rat.natCast_nonneg)
        (Rat.pow_nonneg (show (0:Rat)≤2*(1/1024) by decide +kernel))) hs)
    exact Rat.add_nonneg hfirst hsecond
  have h0 : b≤u*b := by
    have h := Rat.mul_le_mul_of_nonneg_right hu1 hb
    grind only
  have h1 := tauLambertQuadratic_coefficient_bound H N
  change u*b≤33792*(1/64:Rat)^N*H^2 at h1
  have h2 := Rat.mul_le_mul_of_nonneg_left (Rat.le_trans h0 h1) (Rat.pow_nonneg hu (n := k))
  have h3 := Rat.mul_le_mul_of_nonneg_right (tauLambertIndex_power_bound N k)
    (Rat.mul_nonneg (Rat.mul_nonneg (show (0:Rat)≤33792 by decide +kernel)
      (Rat.pow_nonneg (show (0:Rat)≤1/64 by decide +kernel) (n := N))) hs)
  have he : (2^k*(2^k:Rat)^N)*(33792*(1/64:Rat)^N*H^2)=
      (33792*2^k)*(2^k*(1/64:Rat))^N*H^2 := by
    rw [←product_power]
    grind only
  rw [he] at h3
  exact Rat.le_trans h2 h3

/-- Actual higher weighted remainders satisfy the geometric coefficient bound. -/
theorem tauWeightedLambert_geometric_remainder_bound (k : Nat) (a z : Scalar)
    (ha : tauEulerNomeDomain a) (hz : tauEulerNomeDomain z)
    (H : Rat) (hH : 0≤H) (hd : Small (sub z.val a.val) H) (N : Nat) :
    Small (SeriesLimitLaws.remainder ((tauWeightedLambertMap k (N+1)).eval z hz).val
      ((tauWeightedLambertMap k (N+1)).eval a ha).val
      ((tauWeightedLambertMap_holomorphic k (N+1)).derivative a ha).val (sub z.val a.val))
      ((33792*2^k)*(2^k*(1/64:Rat))^N*H^2) :=
  (tauWeightedLambert_actual_remainder_bound k a z ha hz H hH hd N).mono
    (tauWeightedLambertQuadratic_coefficient_bound k N H)

/-- The higher remainder ratio is summable throughout the degrees required here. -/
theorem tauWeightedLambert_remainder_ratio_local (k : Nat) (hk : k≤5) :
    (2^k:Rat)*(1/64)≤(1:Rat)/2 := by
  have hc : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 := by omega
  rcases hc with h | h | h | h | h | h <;> subst k <;> decide +kernel

end ComputableAnalysis.ModularForms
