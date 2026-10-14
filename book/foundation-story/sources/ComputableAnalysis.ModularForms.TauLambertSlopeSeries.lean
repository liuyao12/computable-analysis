import ComputableAnalysis.ModularForms.TauLambertSlopeBounds
import ComputableAnalysis.ModularForms.TauEulerNomeMap

/-! A convergent executable series of weighted Lambert slope candidates. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert

private def slope (q : Scalar) (hq : tauEulerNomeDomain q) (N : Nat) : Scalar :=
  weightedLambertOneSlope q (1/1024) (by decide +kernel) (by decide +kernel)
    (LocalODE.interior_bound _ q hq) N

private theorem slope_bound (q : Scalar) (hq : tauEulerNomeDomain q) (N : Nat) :
    Small (slope q hq N).val (2*32*(1/128:Rat)^N) := by
  have h := weightedLambertOneSlope_geometric_bound q (1/1024)
    (by decide +kernel) (by decide +kernel) (LocalODE.interior_bound _ q hq) N
  simpa only [slope, show (8:Rat)*(1/1024)=1/128 by decide +kernel,
    show (2:Rat)*32=64 by decide +kernel] using h

/-- A valid represented candidate; differentiation of the sum is separate. -/
def tauLambertSlopeValue (q : Scalar) (hq : tauEulerNomeDomain q) : Scalar :=
  ⟨ScalarSeries.value (fun N => (slope q hq N).val) (fun N => (slope q hq N).property) 32 (1/128),
    ScalarSeries.value_valid _ _ _ _ (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (slope_bound q hq)⟩

def tauLambertSlopePrefix (q : Scalar) (hq : tauEulerNomeDomain q) (N : Nat) : Scalar :=
  ⟨ScalarSeries.block (fun n => (slope q hq n).val) 0 N,
    ScalarSeries.block_valid _ (fun n => (slope q hq n).property) 0 N⟩

theorem tauLambertSlopeValue_close_prefix (q : Scalar) (hq : tauEulerNomeDomain q) (N : Nat) :
    Small (sub (tauLambertSlopeValue q hq).val (tauLambertSlopePrefix q hq N).val)
      (128*(1/128:Rat)^N) :=
  by
  simpa only [tauLambertSlopeValue, tauLambertSlopePrefix, show (4:Rat)*32=128 by decide +kernel] using ScalarSeries.value_close (fun n => (slope q hq n).val) (fun n => (slope q hq n).property) _ _ (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (slope_bound q hq) N

theorem tauLambertSlopeValue_bound (q : Scalar) (hq : tauEulerNomeDomain q) :
    Small (tauLambertSlopeValue q hq).val 128 :=
  by
  simpa only [tauLambertSlopeValue, tauLambertSlopePrefix, show (4:Rat)*32=128 by decide +kernel] using ScalarSeries.value_bound (fun n => (slope q hq n).val) (fun n => (slope q hq n).property) _ _ (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (slope_bound q hq)

theorem tauLambertSlopeSeries_tail_shrinks :
    ShrinksToZero (fun N => 128*(1/128:Rat)^N) :=
  by
  simpa only [tauLambertSlopeValue, tauLambertSlopePrefix, show (4:Rat)*32=128 by decide +kernel] using LocalODE.tail_bound_shrinks 32 (1/128) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- The candidate sum depends only on the represented nome value. -/
theorem tauLambertSlopeValue_congr (q w : Scalar) (hq : tauEulerNomeDomain q)
    (hw : tauEulerNomeDomain w) (he : q.val.Equiv w.val) :
    (tauLambertSlopeValue q hq).val.Equiv (tauLambertSlopeValue w hw).val := by
  apply ScalarSeries.value_congr
    (fun n => (slope q hq n).val) (fun n => (slope w hw n).val)
    (fun n => (slope q hq n).property) (fun n => (slope w hw n).property)
    32 (1/128) 32 (1/128)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (slope_bound q hq) (slope_bound w hw)
  intro n
  exact weightedLambertOneSlope_congr q w (1/1024) (1/1024)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (LocalODE.interior_bound _ q hq) (LocalODE.interior_bound _ w hw) he n

end ComputableAnalysis.ModularForms
