import ComputableAnalysis.ModularForms.LambertSharperWeightBound
import ComputableAnalysis.ModularForms.WeightedLambertSeries
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

private theorem sharp_majorant (z : Scalar) (r : Rat) (hr : 0≤r)
    (hlocal : 4*r≤(1:Rat)/2) (hz : Small z.val r) (n : Nat) :
    Small (weightedLambertTerm z r 5 n) (2*(128*r)*(8*r)^n) := by
  have h := weightedLambertFifthTerm_sharp_bound z r hr hlocal hz n
  have he : 256*r=2*(128*r) := by grind only
  rw [he] at h
  exact h

/-- Executable sum of the actual weight-six Lambert terms with the sharper convergence schedule. -/
def sharperLambertFifthSum (z : Scalar) (r : Rat) (hr : 0≤r)
    (hlocal : 4*r≤(1:Rat)/2) (hz : Small z.val r) : ComplexRaw :=
  ScalarSeries.value (weightedLambertTerm z r 5)
    (weightedLambertTerm_valid z r 5 hr hlocal hz) (128*r) (8*r)

theorem sharperLambertFifthSum_valid (z : Scalar) (r : Rat) (hr : 0≤r)
    (hlocal : 4*r≤(1:Rat)/2) (hz : Small z.val r) (hseries : 8*r≤(1:Rat)/2) :
    (sharperLambertFifthSum z r hr hlocal hz).Valid :=
  ScalarSeries.value_valid _ _ _ _ (Rat.mul_nonneg (by decide +kernel) hr)
    (Rat.mul_nonneg (by decide +kernel) hr) hseries (sharp_majorant z r hr hlocal hz)

theorem sharperLambertFifthSum_close (z : Scalar) (r : Rat) (hr : 0≤r)
    (hlocal : 4*r≤(1:Rat)/2) (hz : Small z.val r) (hseries : 8*r≤(1:Rat)/2) (N : Nat) :
    Small (sub (sharperLambertFifthSum z r hr hlocal hz)
      (ScalarSeries.block (weightedLambertTerm z r 5) 0 N)) (4*(128*r)*(8*r)^N) :=
  ScalarSeries.value_close _ _ _ _ (Rat.mul_nonneg (by decide +kernel) hr)
    (Rat.mul_nonneg (by decide +kernel) hr) hseries (sharp_majorant z r hr hlocal hz) N

theorem sharperLambertFifthSum_tail_shrinks (r : Rat) (hr : 0≤r) (hseries : 8*r≤(1:Rat)/2) :
    ShrinksToZero (fun N => 4*(128*r)*(8*r)^N) :=
  LocalODE.tail_bound_shrinks (128*r) (8*r) (Rat.mul_nonneg (by decide +kernel) hr)
    (Rat.mul_nonneg (by decide +kernel) hr) hseries

/-- The sharper sum is independent of represented names and of its supplied radius. -/
theorem sharperLambertFifthSum_congr (z w : Scalar) (r s : Rat)
    (hr : 0≤r) (hs : 0≤s) (hrlocal : 4*r≤(1:Rat)/2) (hslocal : 4*s≤(1:Rat)/2)
    (hz : Small z.val r) (hw : Small w.val s) (hrseries : 8*r≤(1:Rat)/2)
    (hsseries : 8*s≤(1:Rat)/2) (hzw : z.val.Equiv w.val) :
    (sharperLambertFifthSum z r hr hrlocal hz).Equiv
      (sharperLambertFifthSum w s hs hslocal hw) :=
  ScalarSeries.value_congr (weightedLambertTerm z r 5) (weightedLambertTerm w s 5)
    (weightedLambertTerm_valid z r 5 hr hrlocal hz) (weightedLambertTerm_valid w s 5 hs hslocal hw)
    (128*r) (8*r) (128*s) (8*s)
    (Rat.mul_nonneg (by decide +kernel) hr) (Rat.mul_nonneg (by decide +kernel) hr)
    (Rat.mul_nonneg (by decide +kernel) hs) (Rat.mul_nonneg (by decide +kernel) hs)
    hrseries hsseries (sharp_majorant z r hr hrlocal hz) (sharp_majorant w s hs hslocal hw)
    (weightedLambertTerm_congr z w r s 5 hr hs hrlocal hslocal hz hw hzw)

/-- Exact agreement with the original actual weighted Lambert sum wherever both schedules are justified. -/
theorem sharperLambertFifthSum_agreement (z w : Scalar) (r s : Rat)
    (hr : 0≤r) (hs : 0≤s) (hrlocal : 4*r≤(1:Rat)/2) (hslocal : 4*s≤(1:Rat)/2)
    (hz : Small z.val r) (hw : Small w.val s) (hrseries : 8*r≤(1:Rat)/2)
    (hsseries : weightedLambertRatio s 5≤(1:Rat)/2) (hzw : z.val.Equiv w.val) :
    (sharperLambertFifthSum z r hr hrlocal hz).Equiv
      (weightedLambertSum w s 5 hs hslocal hw) := by
  have old_majorant (n : Nat) :
      Small (weightedLambertTerm w s 5 n) (2*(8*s)*(weightedLambertRatio s 5)^n) := by
    have h := weightedLambertTerm_bound w s 5 hs hslocal hw n
    have he : 16*s=2*(8*s) := by grind only
    rw [he] at h
    exact h
  exact ScalarSeries.value_congr (weightedLambertTerm z r 5) (weightedLambertTerm w s 5)
    (weightedLambertTerm_valid z r 5 hr hrlocal hz) (weightedLambertTerm_valid w s 5 hs hslocal hw)
    (128*r) (8*r) (8*s) (weightedLambertRatio s 5)
    (Rat.mul_nonneg (by decide +kernel) hr) (Rat.mul_nonneg (by decide +kernel) hr)
    (Rat.mul_nonneg (by decide +kernel) hs) (weightedLambertRatio_nonneg s 5 hs)
    hrseries hsseries (sharp_majorant z r hr hrlocal hz) old_majorant
    (weightedLambertTerm_congr z w r s 5 hr hs hrlocal hslocal hz hw hzw)

end ComputableAnalysis.ModularForms
