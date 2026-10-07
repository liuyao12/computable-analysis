import ComputableAnalysis.ModularForms.NomeMomentRectangles

/-! A constructed sum of nome moments over the positive powers of the nome. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

private theorem two_pow_ge_one (k : Nat) : 1≤(2:Rat)^k := by
  induction k with
  | zero => rw [Rat.pow_zero]; exact Rat.le_refl
  | succ k ih =>
    rw [Rat.pow_succ]
    have h := Rat.mul_le_mul_of_nonneg_right ih (show (0:Rat)≤2 by decide)
    grind only

/-- Bound on the actual constructed moment, obtained from its geometric tails. -/
theorem polynomialNomeMomentSum_bound (z : Scalar) (r : Rat) (k : Nat) (hr : 0≤r)
    (hlocal : polynomialNomeMomentRatio r k≤(1:Rat)/2) (hz : Small z.val r) :
    Small (polynomialNomeMomentSum z r k) (4*r) :=
  ScalarSeries.value_bound _ _ r _ hr (polynomialNomeMomentRatio_nonneg r k hr) hlocal
    (polynomialNomeMomentTerm_bound z r k hr hz)

/-- A single guard controls every moment at every positive nome power. -/
theorem nomePowerMomentRatio_le (r : Rat) (k : Nat) (hr : 0≤r)
    (hlocal : 4*r*(2:Rat)^k≤(1:Rat)/2) (n : Nat) :
    polynomialNomeMomentRatio (nomePowerRadius r n) k≤(1:Rat)/2 := by
  have hpow : 1≤(2:Rat)^k := two_pow_ge_one k
  have hsmall : 2*r≤1 := by
    have h := Rat.mul_le_mul_of_nonneg_left hpow (show 0≤4*r from Rat.mul_nonneg (by decide) hr)
    grind only
  have h := Rat.mul_le_mul_of_nonneg_right (nomePowerRadius_le r hr hsmall n)
    (Rat.pow_nonneg (a := (2:Rat)) (n := k) (by decide))
  unfold polynomialNomeMomentRatio
  grind only

def nomeMomentOuterTerm (z : Scalar) (r : Rat) (k n : Nat) : ComplexRaw :=
  polynomialNomeMomentSum (nomePowerScalar z n) (nomePowerRadius r n) k

theorem nomeMomentOuterTerm_valid (z : Scalar) (r : Rat) (k : Nat) (hr : 0≤r)
    (hlocal : 4*r*(2:Rat)^k≤(1:Rat)/2) (hz : Small z.val r) (n : Nat) :
    (nomeMomentOuterTerm z r k n).Valid :=
  polynomialNomeMomentSum_valid _ _ k (nomePowerRadius_nonneg r hr n)
    (nomePowerMomentRatio_le r k hr hlocal n) (nomePowerScalar_small z r hr hz n)

theorem nomeMomentOuterTerm_bound (z : Scalar) (r : Rat) (k : Nat) (hr : 0≤r)
    (hlocal : 4*r*(2:Rat)^k≤(1:Rat)/2) (hz : Small z.val r) (n : Nat) :
    Small (nomeMomentOuterTerm z r k n) (2*(4*r)*(2*r)^n) := by
  have h := polynomialNomeMomentSum_bound (nomePowerScalar z n) (nomePowerRadius r n) k
    (nomePowerRadius_nonneg r hr n) (nomePowerMomentRatio_le r k hr hlocal n)
    (nomePowerScalar_small z r hr hz n)
  have he : 4*nomePowerRadius r n=2*(4*r)*(2*r)^n := by
    unfold nomePowerRadius
    rw [Rat.pow_succ]
    grind only
  rw [he] at h
  exact h

def nomeMomentOuterSum (z : Scalar) (r : Rat) (k : Nat) (hr : 0≤r)
    (hlocal : 4*r*(2:Rat)^k≤(1:Rat)/2) (hz : Small z.val r) : ComplexRaw :=
  ScalarSeries.value (nomeMomentOuterTerm z r k) (nomeMomentOuterTerm_valid z r k hr hlocal hz)
    (4*r) (2*r)

theorem nomeMomentOuterRatio_le (r : Rat) (k : Nat) (hr : 0≤r)
    (hlocal : 4*r*(2:Rat)^k≤(1:Rat)/2) : 2*r≤(1:Rat)/2 := by
  have hpow : 1≤(2:Rat)^k := two_pow_ge_one k
  have h := Rat.mul_le_mul_of_nonneg_left hpow (show 0≤4*r from Rat.mul_nonneg (by decide) hr)
  grind only

theorem nomeMomentOuterSum_valid (z : Scalar) (r : Rat) (k : Nat) (hr : 0≤r)
    (hlocal : 4*r*(2:Rat)^k≤(1:Rat)/2) (hz : Small z.val r) :
    (nomeMomentOuterSum z r k hr hlocal hz).Valid :=
  ScalarSeries.value_valid _ _ _ _ (Rat.mul_nonneg (by decide) hr)
    (Rat.mul_nonneg (by decide) hr) (nomeMomentOuterRatio_le r k hr hlocal)
    (nomeMomentOuterTerm_bound z r k hr hlocal hz)

theorem nomeMomentOuterSum_close (z : Scalar) (r : Rat) (k : Nat) (hr : 0≤r)
    (hlocal : 4*r*(2:Rat)^k≤(1:Rat)/2) (hz : Small z.val r) (N : Nat) :
    Small (sub (nomeMomentOuterSum z r k hr hlocal hz)
      (ScalarSeries.block (nomeMomentOuterTerm z r k) 0 N)) (4*(4*r)*(2*r)^N) :=
  ScalarSeries.value_close _ _ _ _ (Rat.mul_nonneg (by decide) hr)
    (Rat.mul_nonneg (by decide) hr) (nomeMomentOuterRatio_le r k hr hlocal)
    (nomeMomentOuterTerm_bound z r k hr hlocal hz) N

/-- The outer tail has a proved schedule tending to zero. -/
theorem nomeMomentOuterSum_tail_shrinks (r : Rat) (k : Nat) (hr : 0≤r)
    (hlocal : 4*r*(2:Rat)^k≤(1:Rat)/2) :
    ShrinksToZero (fun N => 4*(4*r)*(2*r)^N) :=
  LocalODE.tail_bound_shrinks (4*r) (2*r) (Rat.mul_nonneg (by decide) hr)
    (Rat.mul_nonneg (by decide) hr) (nomeMomentOuterRatio_le r k hr hlocal)

/-- Equivalent nome inputs and different justified radii give the same outer sum. -/
theorem nomeMomentOuterSum_congr (z w : Scalar) (r s : Rat) (k : Nat)
    (hr : 0≤r) (hs : 0≤s) (hrlocal : 4*r*(2:Rat)^k≤(1:Rat)/2)
    (hslocal : 4*s*(2:Rat)^k≤(1:Rat)/2)
    (hz : Small z.val r) (hw : Small w.val s) (he : z.val.Equiv w.val) :
    (nomeMomentOuterSum z r k hr hrlocal hz).Equiv
      (nomeMomentOuterSum w s k hs hslocal hw) := by
  apply ScalarSeries.value_congr _ _ _ _ (4*r) (2*r) (4*s) (2*s)
    (Rat.mul_nonneg (by decide) hr) (Rat.mul_nonneg (by decide) hr)
    (Rat.mul_nonneg (by decide) hs) (Rat.mul_nonneg (by decide) hs)
    (nomeMomentOuterRatio_le r k hr hrlocal) (nomeMomentOuterRatio_le s k hs hslocal)
    (nomeMomentOuterTerm_bound z r k hr hrlocal hz)
    (nomeMomentOuterTerm_bound w s k hs hslocal hw)
  intro n
  exact polynomialNomeMomentSum_congr _ _ _ _ k
    (nomePowerRadius_nonneg r hr n) (nomePowerRadius_nonneg s hs n)
    (nomePowerMomentRatio_le r k hr hrlocal n) (nomePowerMomentRatio_le s k hs hslocal n)
    (nomePowerScalar_small z r hr hz n) (nomePowerScalar_small w s hs hw n)
    (LocalODE.power_congr _ _ z.property w.property he (n+1))

end ComputableAnalysis.ModularForms
