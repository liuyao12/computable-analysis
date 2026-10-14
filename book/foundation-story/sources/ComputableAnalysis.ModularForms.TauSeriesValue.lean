import ComputableAnalysis.ModularForms.TauSeriesTail

/-! An executable represented sum of the ordinary tau-series prefixes. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert

def tauSeriesPrefix (q : Scalar) (N : Nat) : Scalar :=
  integerCoefficientPrefix (fun n => tau (n+1)) q N

def tauSeriesTail (N : Nat) : Rat := 4*(1/2:Rat)^N

theorem tauSeriesTail_nonnegative (N : Nat) : 0≤tauSeriesTail N :=
  Rat.mul_nonneg (by decide +kernel) (Rat.pow_nonneg (by decide +kernel))

theorem tauSeriesTail_shrinks : ShrinksToZero tauSeriesTail := by
  change ShrinksToZero (fun N => 4*(1/2:Rat)^N)
  simpa only [Rat.mul_one] using
    LocalODE.tail_bound_shrinks 1 (1/2) (by decide +kernel) (by decide +kernel) Rat.le_refl

theorem tauSeriesPrefix_cauchy (q : Scalar) (hq : Small q.val (1/1024)) (K N : Nat) (hKN : K≤N) :
    Small (sub (tauSeriesPrefix q N).val (tauSeriesPrefix q K).val) (tauSeriesTail K) := by
  have h := tauSeries_complex_tail q hq K (N-K)
  have he : K+(N-K)=N := by omega
  rw [he] at h
  exact h

/-- The sum is computed from ordinary prefixes with a proved geometric tail. -/
def tauSeriesValue (q : Scalar) (hq : Small q.val (1/1024)) : Scalar :=
  ⟨RepresentedCauchySum.value (fun N => (tauSeriesPrefix q N).val)
    (fun N => (tauSeriesPrefix q N).property) tauSeriesTail,
    RepresentedCauchySum.value_valid _ _ _ tauSeriesTail_shrinks (tauSeriesPrefix_cauchy q hq)⟩

theorem tauSeriesValue_close_prefix (q : Scalar) (hq : Small q.val (1/1024)) (N : Nat) :
    Small (sub (tauSeriesValue q hq).val (tauSeriesPrefix q N).val) (tauSeriesTail N) :=
  RepresentedCauchySum.value_close_prefix _ _ _ (tauSeriesPrefix_cauchy q hq) N

/-- The constructed sum depends only on the represented nome value. -/
theorem tauSeriesValue_congr (q w : Scalar) (hq : Small q.val (1/1024))
    (hw : Small w.val (1/1024)) (he : q.val.Equiv w.val) :
    (tauSeriesValue q hq).val.Equiv (tauSeriesValue w hw).val := by
  apply RepresentedCauchySum.value_congr _ _ _ _ _ _ tauSeriesTail_shrinks tauSeriesTail_shrinks
    tauSeriesTail_nonnegative tauSeriesTail_nonnegative (tauSeriesPrefix_cauchy q hq)
    (tauSeriesPrefix_cauchy w hw)
  exact integerCoefficientPrefix_congr _ q w he

end ComputableAnalysis.ModularForms
