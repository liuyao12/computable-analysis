import ComputableAnalysis.ModularForms.LambertPowers

/-! Geometric majorants for polynomially weighted actual Lambert factors. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

theorem lambertIndex_bound (n : Nat) : ((n+1 : Nat) : Rat)≤(2:Rat)^n := by
  induction n with
  | zero => change (1:Rat)≤1; decide +kernel
  | succ n ih =>
    have hn : (1:Rat)≤((n+1:Nat):Rat) := by
      simp only [Rat.natCast_add]
      have h : (0:Rat)≤(n:Rat) := Rat.natCast_nonneg
      grind only
    rw [Rat.pow_succ]
    simp only [Rat.natCast_add] at ih hn ⊢
    grind only

private theorem nonneg_pow_mono (a b : Rat) (ha : 0≤a) (hab : a≤b) (k : Nat) :
    a^k≤b^k := by
  have hb : 0≤b := Rat.le_trans ha hab
  induction k with
  | zero => simp only [Rat.pow_zero]; exact Rat.le_refl
  | succ k ih =>
    rw [Rat.pow_succ, Rat.pow_succ]
    have h1 := Rat.mul_le_mul_of_nonneg_right ih ha
    have h2 := Rat.mul_le_mul_of_nonneg_left hab (Rat.pow_nonneg (n := k) hb)
    exact Rat.le_trans h1 h2

private theorem pow_commute (a : Rat) (n k : Nat) : (a^n)^k=(a^k)^n := by
  induction n with
  | zero =>
    simp only [Rat.pow_zero]
    induction k with
    | zero => rfl
    | succ k ih => rw [Rat.pow_succ, ih, Rat.mul_one]
  | succ n ih =>
    rw [Rat.pow_succ, LocalODE.rational_mul_pow, ih, Rat.pow_succ]

theorem lambertWeight_bound (n k : Nat) :
    (((n+1:Nat):Rat)^k)≤((2:Rat)^k)^n := by
  have h := nonneg_pow_mono _ _ Rat.natCast_nonneg (lambertIndex_bound n) k
  rw [pow_commute] at h
  exact h

def weightedLambertTerm (z : Scalar) (r : Rat) (k n : Nat) : ComplexRaw :=
  scaleRat (((n+1:Nat):Rat)^k) (nomeLambertPower z r n)

theorem weightedLambertTerm_valid (z : Scalar) (r : Rat) (k : Nat) (hr : 0≤r)
    (hlocal : 4*r≤(1:Rat)/2) (hz : Small z.val r) (n : Nat) :
    (weightedLambertTerm z r k n).Valid :=
  scaleRat_valid (nomeLambertPower_valid z r hr hlocal hz n)

theorem weightedLambertTerm_bound (z : Scalar) (r : Rat) (k : Nat) (hr : 0≤r)
    (hlocal : 4*r≤(1:Rat)/2) (hz : Small z.val r) (n : Nat) :
    Small (weightedLambertTerm z r k n) (16*r*(2*r*(2:Rat)^k)^n) := by
  have h := LocalODE.small_scale (c := (((n+1:Nat):Rat)^k))
    (Rat.pow_nonneg (n := k) (show (0:Rat)≤((n+1:Nat):Rat) from Rat.natCast_nonneg))
    (nomeLambertPower_bound z r hr hlocal hz n)
  apply h.mono
  have hm := Rat.mul_le_mul_of_nonneg_right (lambertWeight_bound n k)
    (Rat.mul_nonneg (show (0:Rat)≤8 by decide)
      (nomePowerRadius_nonneg r hr n))
  unfold nomePowerRadius at hm
  rw [Rat.pow_succ] at hm ⊢
  rw [LocalODE.rational_mul_pow (2*r) ((2:Rat)^k) n]
  generalize (((n+1:Nat):Rat)^k) = A at hm ⊢
  generalize ((2:Rat)^k)^n = B at hm ⊢
  generalize (2*r)^n = D at hm ⊢
  grind only

end ComputableAnalysis.ModularForms
