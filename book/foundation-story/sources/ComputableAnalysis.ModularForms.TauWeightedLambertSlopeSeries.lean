import ComputableAnalysis.ModularForms.TauWeightedLambertSlopeBounds
import ComputableAnalysis.ModularForms.TauEulerNomeMap

/-! A convergent executable series of weighted Lambert slope candidates. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert

def weightedSlopeRatio (k : Nat) : Rat := 2^(k+1)*(2*(1/1024:Rat))

private theorem weightedSlopeRatio_nonneg (k : Nat) : 0≤weightedSlopeRatio k :=
  Rat.mul_nonneg (Rat.pow_nonneg (by decide +kernel)) (by decide +kernel)

private theorem weightedSlopeRatio_local (k : Nat) (hk : k≤5) : weightedSlopeRatio k≤(1:Rat)/2 := by
  have hc : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 := by omega
  rcases hc with h | h | h | h | h | h <;> subst k <;> decide +kernel

private def slope (q : Scalar) (hq : tauEulerNomeDomain q) (k : Nat) (_hk : k≤5) (N : Nat) : Scalar :=
  weightedLambertSlope q (1/1024) k (by decide +kernel) (by decide +kernel)
    (LocalODE.interior_bound _ q hq) N

private theorem slope_bound (q : Scalar) (hq : tauEulerNomeDomain q) (k : Nat) (hk : k≤5) (N : Nat) :
    Small (slope q hq k hk N).val (2*32*(weightedSlopeRatio k)^N) := by
  have h := weightedLambertSlope_geometric_bound q (1/1024) k
    (by decide +kernel) (by decide +kernel) (LocalODE.interior_bound _ q hq) N
  simpa only [slope,weightedSlopeRatio,show (2:Rat)*32=64 by decide +kernel] using h

/-- A valid represented candidate; differentiation of the sum is separate. -/
def tauWeightedLambertSlopeValue (q : Scalar) (hq : tauEulerNomeDomain q) (k : Nat) (hk : k≤5) : Scalar :=
  ⟨ScalarSeries.value (fun N => (slope q hq k hk N).val) (fun N => (slope q hq k hk N).property) 32 (weightedSlopeRatio k),
    ScalarSeries.value_valid _ _ _ _ (by decide +kernel) (weightedSlopeRatio_nonneg k)
      (weightedSlopeRatio_local k hk) (slope_bound q hq k hk)⟩

def tauWeightedLambertSlopePrefix (q : Scalar) (hq : tauEulerNomeDomain q) (k : Nat) (hk : k≤5) (N : Nat) : Scalar :=
  ⟨ScalarSeries.block (fun n => (slope q hq k hk n).val) 0 N,
    ScalarSeries.block_valid _ (fun n => (slope q hq k hk n).property) 0 N⟩

theorem tauWeightedLambertSlopeValue_close_prefix (q : Scalar) (hq : tauEulerNomeDomain q) (k : Nat) (hk : k≤5) (N : Nat) :
    Small (sub (tauWeightedLambertSlopeValue q hq k hk).val (tauWeightedLambertSlopePrefix q hq k hk N).val)
      (128*(weightedSlopeRatio k)^N) :=
  by
  simpa only [tauWeightedLambertSlopeValue, tauWeightedLambertSlopePrefix, show (4:Rat)*32=128 by decide +kernel] using ScalarSeries.value_close (fun n => (slope q hq k hk n).val) (fun n => (slope q hq k hk n).property) _ _ (by decide +kernel) (weightedSlopeRatio_nonneg k)
    (weightedSlopeRatio_local k hk) (slope_bound q hq k hk) N

theorem tauWeightedLambertSlopeValue_bound (q : Scalar) (hq : tauEulerNomeDomain q) (k : Nat) (hk : k≤5) :
    Small (tauWeightedLambertSlopeValue q hq k hk).val 128 :=
  by
  simpa only [tauWeightedLambertSlopeValue, tauWeightedLambertSlopePrefix, show (4:Rat)*32=128 by decide +kernel] using ScalarSeries.value_bound (fun n => (slope q hq k hk n).val) (fun n => (slope q hq k hk n).property) _ _ (by decide +kernel) (weightedSlopeRatio_nonneg k)
    (weightedSlopeRatio_local k hk) (slope_bound q hq k hk)

theorem tauWeightedLambertSlopeSeries_tail_shrinks (k : Nat) (hk : k≤5) :
    ShrinksToZero (fun N => 128*(weightedSlopeRatio k)^N) :=
  by
  simpa only [tauWeightedLambertSlopeValue, tauWeightedLambertSlopePrefix, show (4:Rat)*32=128 by decide +kernel] using LocalODE.tail_bound_shrinks 32 (weightedSlopeRatio k) (by decide +kernel) (weightedSlopeRatio_nonneg k) (weightedSlopeRatio_local k hk)

/-- The candidate sum depends only on the represented nome value. -/
theorem tauWeightedLambertSlopeValue_congr (q w : Scalar) (k : Nat) (hk : k≤5) (hq : tauEulerNomeDomain q)
    (hw : tauEulerNomeDomain w) (he : q.val.Equiv w.val) :
    (tauWeightedLambertSlopeValue q hq k hk).val.Equiv (tauWeightedLambertSlopeValue w hw k hk).val := by
  apply ScalarSeries.value_congr
    (fun n => (slope q hq k hk n).val) (fun n => (slope w hw k hk n).val)
    (fun n => (slope q hq k hk n).property) (fun n => (slope w hw k hk n).property)
    32 (weightedSlopeRatio k) 32 (weightedSlopeRatio k)
    (by decide +kernel) (weightedSlopeRatio_nonneg k) (by decide +kernel) (weightedSlopeRatio_nonneg k)
    (weightedSlopeRatio_local k hk) (weightedSlopeRatio_local k hk) (slope_bound q hq k hk) (slope_bound w hw k hk)
  intro n
  exact weightedLambertSlope_congr q w (1/1024) (1/1024) k
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (LocalODE.interior_bound _ q hq) (LocalODE.interior_bound _ w hw) he n

end ComputableAnalysis.ModularForms
