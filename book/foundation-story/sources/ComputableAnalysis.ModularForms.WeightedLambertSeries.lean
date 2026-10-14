import ComputableAnalysis.ModularForms.LambertWeightBound

/-! Executable weighted Lambert sums with quantitative prefix errors. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

def weightedLambertRatio (r : Rat) (k : Nat) : Rat := 2*r*(2:Rat)^k

theorem weightedLambertRatio_nonneg (r : Rat) (k : Nat) (hr : 0≤r) :
    0≤weightedLambertRatio r k :=
  Rat.mul_nonneg (Rat.mul_nonneg (by decide) hr) (Rat.pow_nonneg (by decide))

def weightedLambertSum (z : Scalar) (r : Rat) (k : Nat) (hr : 0≤r)
    (hlocal : 4*r≤(1:Rat)/2) (hz : Small z.val r) : ComplexRaw :=
  ScalarSeries.value (weightedLambertTerm z r k)
    (weightedLambertTerm_valid z r k hr hlocal hz) (8*r) (weightedLambertRatio r k)

private theorem weightedTerm_majorant (z : Scalar) (r : Rat) (k : Nat) (hr : 0≤r)
    (hlocal : 4*r≤(1:Rat)/2) (hz : Small z.val r) (n : Nat) :
    Small (weightedLambertTerm z r k n) (2*(8*r)*(weightedLambertRatio r k)^n) := by
  have h := weightedLambertTerm_bound z r k hr hlocal hz n
  have he : (16:Rat)*r=2*(8*r) := by grind only
  rw [he] at h
  exact h

theorem weightedLambertSum_valid (z : Scalar) (r : Rat) (k : Nat) (hr : 0≤r)
    (hlocal : 4*r≤(1:Rat)/2) (hz : Small z.val r)
    (hseries : weightedLambertRatio r k≤(1:Rat)/2) :
    (weightedLambertSum z r k hr hlocal hz).Valid :=
  ScalarSeries.value_valid _ _ _ _ (Rat.mul_nonneg (by decide) hr)
    (weightedLambertRatio_nonneg r k hr) hseries (weightedTerm_majorant z r k hr hlocal hz)

theorem weightedLambertSum_close (z : Scalar) (r : Rat) (k : Nat) (hr : 0≤r)
    (hlocal : 4*r≤(1:Rat)/2) (hz : Small z.val r)
    (hseries : weightedLambertRatio r k≤(1:Rat)/2) (N : Nat) :
    Small (sub (weightedLambertSum z r k hr hlocal hz)
      (ScalarSeries.block (weightedLambertTerm z r k) 0 N))
      (4*(8*r)*(weightedLambertRatio r k)^N) :=
  ScalarSeries.value_close _ _ _ _ (Rat.mul_nonneg (by decide) hr)
    (weightedLambertRatio_nonneg r k hr) hseries (weightedTerm_majorant z r k hr hlocal hz) N

theorem weightedLambertSum_tail_shrinks (r : Rat) (k : Nat) (hr : 0≤r)
    (hseries : weightedLambertRatio r k≤(1:Rat)/2) :
    ShrinksToZero (fun N => 4*(8*r)*(weightedLambertRatio r k)^N) :=
  LocalODE.tail_bound_shrinks (8*r) (weightedLambertRatio r k)
    (Rat.mul_nonneg (by decide) hr) (weightedLambertRatio_nonneg r k hr) hseries

theorem weightedLambertTerm_congr (z w : Scalar) (r s : Rat) (k : Nat)
    (hr : 0≤r) (hs : 0≤s) (hrlocal : 4*r≤(1:Rat)/2) (hslocal : 4*s≤(1:Rat)/2)
    (hz : Small z.val r) (hw : Small w.val s) (hzw : z.val.Equiv w.val) (n : Nat) :
    (weightedLambertTerm z r k n).Equiv (weightedLambertTerm w s k n) :=
  scaleRat_equiv (nomeLambertPower_congr z w r s hr hs hrlocal hslocal hz hw hzw n)

theorem weightedLambertSum_congr (z w : Scalar) (r s : Rat) (k : Nat)
    (hr : 0≤r) (hs : 0≤s) (hrlocal : 4*r≤(1:Rat)/2) (hslocal : 4*s≤(1:Rat)/2)
    (hz : Small z.val r) (hw : Small w.val s)
    (hrseries : weightedLambertRatio r k≤(1:Rat)/2)
    (hsseries : weightedLambertRatio s k≤(1:Rat)/2) (hzw : z.val.Equiv w.val) :
    (weightedLambertSum z r k hr hrlocal hz).Equiv
      (weightedLambertSum w s k hs hslocal hw) :=
  ScalarSeries.value_congr (weightedLambertTerm z r k) (weightedLambertTerm w s k)
    (weightedLambertTerm_valid z r k hr hrlocal hz)
    (weightedLambertTerm_valid w s k hs hslocal hw)
    (8*r) (weightedLambertRatio r k) (8*s) (weightedLambertRatio s k)
    (Rat.mul_nonneg (by decide) hr) (weightedLambertRatio_nonneg r k hr)
    (Rat.mul_nonneg (by decide) hs) (weightedLambertRatio_nonneg s k hs)
    hrseries hsseries (weightedTerm_majorant z r k hr hrlocal hz)
    (weightedTerm_majorant w s k hs hslocal hw)
    (weightedLambertTerm_congr z w r s k hr hs hrlocal hslocal hz hw hzw)

theorem weightedLambertSum_bound (z : Scalar) (r : Rat) (k : Nat) (hr : 0≤r)
    (hlocal : 4*r≤(1:Rat)/2) (hz : Small z.val r)
    (hseries : weightedLambertRatio r k≤(1:Rat)/2) :
    Small (weightedLambertSum z r k hr hlocal hz) (4*(8*r)) :=
  ScalarSeries.value_bound (weightedLambertTerm z r k)
    (weightedLambertTerm_valid z r k hr hlocal hz) (8*r) (weightedLambertRatio r k)
    (Rat.mul_nonneg (by decide) hr) (weightedLambertRatio_nonneg r k hr)
    hseries (weightedTerm_majorant z r k hr hlocal hz)

end ComputableAnalysis.ModularForms
