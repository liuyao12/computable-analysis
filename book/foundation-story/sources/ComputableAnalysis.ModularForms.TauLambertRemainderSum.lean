import ComputableAnalysis.ModularForms.TauLambertQuadraticMajorant

/-! Uniform finite sums of actual weighted Lambert remainders. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

def tauLambertTermRemainder (a z : Scalar) (ha : tauEulerNomeDomain a)
    (hz : tauEulerNomeDomain z) (N : Nat) : Scalar :=
  ⟨SeriesLimitLaws.remainder ((tauWeightedLambertMap 1 N).eval z hz).val
    ((tauWeightedLambertMap 1 N).eval a ha).val
    ((tauWeightedLambertMap_holomorphic 1 N).derivative a ha).val (sub z.val a.val),
    SeriesLimitLaws.remainder_valid _ _ _ _ ((tauWeightedLambertMap 1 N).eval z hz).property
      ((tauWeightedLambertMap 1 N).eval a ha).property
      ((tauWeightedLambertMap_holomorphic 1 N).derivative a ha).property (sub_valid z.property a.property)⟩

/-- The sum of all higher term remainders has a cutoff-independent quadratic bound. -/
theorem tauLambertHigherRemainder_block_bound (a z : Scalar)
    (ha : tauEulerNomeDomain a) (hz : tauEulerNomeDomain z)
    (H : Rat) (hH : 0≤H) (hd : Small (sub z.val a.val) H) (K : Nat) :
    Small (ScalarSeries.block (fun n => (tauLambertTermRemainder a z ha hz (n+1)).val) 0 K)
      (67584*H^2) := by
  have hsq : 0≤H^2 := Rat.pow_nonneg hH
  have hterm : ∀ n, Small (tauLambertTermRemainder a z ha hz (n+1)).val
      (2*(16896*H^2)*(1/64:Rat)^n) := by
    intro n
    have h := tauWeightedLambertOne_geometric_remainder_bound a z ha hz H hH hd n
    have he : 33792*(1/64:Rat)^n*H^2=2*(16896*H^2)*(1/64:Rat)^n := by grind only
    rw [he] at h
    exact h
  have h := ScalarSeries.block_bound _ (16896*H^2) (1/64)
    (Rat.mul_nonneg (by decide +kernel) hsq) (by decide +kernel) (by decide +kernel) hterm 0 K
  have he : 4*(16896*H^2)*(1/64:Rat)^0=67584*H^2 := by rw [Rat.pow_zero]; grind only
  rw [he] at h
  exact h

/-- Adding the first remainder gives a uniform bound for the entire finite sum. -/
theorem tauLambertRemainder_sum_bound (a z : Scalar)
    (ha : tauEulerNomeDomain a) (hz : tauEulerNomeDomain z)
    (H : Rat) (hH : 0≤H) (hd : Small (sub z.val a.val) H) (K : Nat) :
    Small (add (tauLambertTermRemainder a z ha hz 0).val
      (ScalarSeries.block (fun n => (tauLambertTermRemainder a z ha hz (n+1)).val) 0 K))
      (71680*H^2) := by
  have h := LocalODE.small_add (tauWeightedLambertOne_first_remainder_bound a z ha hz H hH hd)
    (tauLambertHigherRemainder_block_bound a z ha hz H hH hd K)
  have he : 4096*H^2+67584*H^2=71680*H^2 := by grind only
  rw [he] at h
  exact h

end ComputableAnalysis.ModularForms
