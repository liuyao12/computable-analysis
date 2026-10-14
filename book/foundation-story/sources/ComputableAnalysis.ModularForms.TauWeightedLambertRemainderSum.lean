import ComputableAnalysis.ModularForms.TauWeightedLambertGeometricRemainder

/-! Uniform finite sums of actual weighted Lambert remainders. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

def tauWeightedLambertTermRemainder (k : Nat) (a z : Scalar) (ha : tauEulerNomeDomain a)
    (hz : tauEulerNomeDomain z) (N : Nat) : Scalar :=
  ⟨SeriesLimitLaws.remainder ((tauWeightedLambertMap k N).eval z hz).val
    ((tauWeightedLambertMap k N).eval a ha).val
    ((tauWeightedLambertMap_holomorphic k N).derivative a ha).val (sub z.val a.val),
    SeriesLimitLaws.remainder_valid _ _ _ _ ((tauWeightedLambertMap k N).eval z hz).property
      ((tauWeightedLambertMap k N).eval a ha).property
      ((tauWeightedLambertMap_holomorphic k N).derivative a ha).property (sub_valid z.property a.property)⟩

/-- The sum of all higher term remainders has a cutoff-independent quadratic bound. -/
theorem tauWeightedLambertHigherRemainder_block_bound (k : Nat) (hk : k≤5) (a z : Scalar)
    (ha : tauEulerNomeDomain a) (hz : tauEulerNomeDomain z)
    (H : Rat) (hH : 0≤H) (hd : Small (sub z.val a.val) H) (K : Nat) :
    Small (ScalarSeries.block (fun n => (tauWeightedLambertTermRemainder k a z ha hz (n+1)).val) 0 K)
      ((67584*2^k)*H^2) := by
  have hsq : 0≤H^2 := Rat.pow_nonneg hH
  have hterm : ∀ n, Small (tauWeightedLambertTermRemainder k a z ha hz (n+1)).val
      (2*((16896*2^k)*H^2)*(2^k*(1/64:Rat))^n) := by
    intro n
    have h := tauWeightedLambert_geometric_remainder_bound k a z ha hz H hH hd n
    have he : (33792*2^k)*(2^k*(1/64:Rat))^n*H^2=2*((16896*2^k)*H^2)*(2^k*(1/64:Rat))^n := by grind only
    rw [he] at h
    exact h
  have h := ScalarSeries.block_bound _ ((16896*2^k)*H^2) (2^k*(1/64:Rat))
    (Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) (Rat.pow_nonneg (by decide +kernel))) hsq)
    (Rat.mul_nonneg (Rat.pow_nonneg (by decide +kernel)) (by decide +kernel))
    (tauWeightedLambert_remainder_ratio_local k hk) hterm 0 K
  have he : 4*((16896*2^k)*H^2)*(2^k*(1/64:Rat))^0=(67584*2^k)*H^2 := by rw [Rat.pow_zero]; grind only
  rw [he] at h
  exact h

/-- Adding the first remainder gives a uniform bound for the entire finite sum. -/
theorem tauWeightedLambertRemainder_sum_bound (k : Nat) (hk : k≤5) (a z : Scalar)
    (ha : tauEulerNomeDomain a) (hz : tauEulerNomeDomain z)
    (H : Rat) (hH : 0≤H) (hd : Small (sub z.val a.val) H) (K : Nat) :
    Small (add (tauWeightedLambertTermRemainder k a z ha hz 0).val
      (ScalarSeries.block (fun n => (tauWeightedLambertTermRemainder k a z ha hz (n+1)).val) 0 K))
      ((4096+67584*2^k)*H^2) := by
  have h := LocalODE.small_add (tauWeightedLambert_first_remainder_bound k a z ha hz H hH hd)
    (tauWeightedLambertHigherRemainder_block_bound k hk a z ha hz H hH hd K)
  have he : 4096*H^2+(67584*2^k)*H^2=(4096+67584*2^k)*H^2 := by grind only
  rw [he] at h
  exact h

end ComputableAnalysis.ModularForms
