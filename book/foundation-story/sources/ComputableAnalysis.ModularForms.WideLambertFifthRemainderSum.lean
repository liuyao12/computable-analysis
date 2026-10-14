import ComputableAnalysis.ModularForms.LambertWideQuadraticMajorant
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

/-- Literal first-order remainder of the actual weighted term and its actual slope. -/
def wideLambertFifthTermRemainder (a z : Scalar)
    (ha : Small a.val ((1:Rat)/64)) (hz : Small z.val ((1:Rat)/64)) (n : Nat) : Scalar :=
  ⟨SeriesLimitLaws.remainder (weightedLambertTerm z (1/64) 5 n) (weightedLambertTerm a (1/64) 5 n)
      (weightedLambertSlope a (1/64) 5 (by decide +kernel) (by decide +kernel) ha n).val (sub z.val a.val),
    SeriesLimitLaws.remainder_valid _ _ _ _
      (weightedLambertTerm_valid z (1/64) 5 (by decide +kernel) (by decide +kernel) hz n)
      (weightedLambertTerm_valid a (1/64) 5 (by decide +kernel) (by decide +kernel) ha n)
      (weightedLambertSlope a (1/64) 5 (by decide +kernel) (by decide +kernel) ha n).property
      (sub_valid z.property a.property)⟩

/-- Every term, including the first, has a summable uniform quadratic majorant. -/
theorem wideLambertFifthTermRemainder_geometric_bound (a z : Scalar)
    (ha : Small a.val ((1:Rat)/64)) (hz : Small z.val ((1:Rat)/64))
    (H : Rat) (hH : 0≤H) (hd : Small (sub z.val a.val) H) (n : Nat) :
    Small (wideLambertFifthTermRemainder a z ha hz n).val (2*(33792*H^2)*((1:Rat)/2)^n) := by
  cases n with
  | zero =>
    have h := weightedLambertTerm_wide_first_remainder_bound 5 a z (1/64) H
      (by decide +kernel) (by decide +kernel) hH ha hz hd
    apply h.mono
    have hs : 0≤H^2 := Rat.pow_nonneg hH
    rw [Rat.pow_zero]
    grind only
  | succ n =>
    have h := weightedLambertTerm_wide_remainder_bound 5 a z (1/64) H
      (by decide +kernel) (by decide +kernel) hH ha hz hd n
    have hb := h.mono (lambertFifthWide_quadratic_coefficient_bound n H hH)
    have he : 33792*((1:Rat)/2)^n*H^2=2*(33792*H^2)*((1:Rat)/2)^(n+1) := by
      rw [Rat.pow_succ ((1:Rat)/2) n]
      grind only
    rw [he] at hb
    exact hb

/-- Finite sums of the actual term remainders have one cutoff-independent quadratic bound. -/
theorem wideLambertFifthRemainder_block_bound (a z : Scalar)
    (ha : Small a.val ((1:Rat)/64)) (hz : Small z.val ((1:Rat)/64))
    (H : Rat) (hH : 0≤H) (hd : Small (sub z.val a.val) H) (K : Nat) :
    Small (ScalarSeries.block (fun n => (wideLambertFifthTermRemainder a z ha hz n).val) 0 K)
      (135168*H^2) := by
  have h := ScalarSeries.block_bound (fun n => (wideLambertFifthTermRemainder a z ha hz n).val)
    (33792*H^2) (1/2) (Rat.mul_nonneg (by decide +kernel) (Rat.pow_nonneg hH))
    (by decide +kernel) (by decide +kernel)
    (wideLambertFifthTermRemainder_geometric_bound a z ha hz H hH hd) 0 K
  have he : 4*(33792*H^2)*((1:Rat)/2)^0=135168*H^2 := by rw [Rat.pow_zero]; grind only
  rw [he] at h
  exact h
end ComputableAnalysis.ModularForms
