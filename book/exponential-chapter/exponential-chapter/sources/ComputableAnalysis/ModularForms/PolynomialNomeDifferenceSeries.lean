import ComputableAnalysis.ModularForms.NomeWeightedDifferenceLimit

/-! Actual polynomial backward-difference series with geometric majorants. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

private theorem rational_nonneg_pow_mono (a b : Rat) (ha : 0≤a) (hab : a≤b) (k : Nat) :
    a^k≤b^k := by
  have hb := Rat.le_trans ha hab
  induction k with
  | zero => simp only [Rat.pow_zero]; exact Rat.le_refl
  | succ k ih =>
    rw [Rat.pow_succ,Rat.pow_succ]
    exact Rat.le_trans (Rat.mul_le_mul_of_nonneg_right ih ha)
      (Rat.mul_le_mul_of_nonneg_left hab (Rat.pow_nonneg (n := k) hb))

def polynomialNomeDifferenceWeight (k n : Nat) : Rat := ((n+1:Nat):Rat)^k-(n:Rat)^k

theorem polynomialNomeDifferenceWeight_bounds (k n : Nat) :
    0≤polynomialNomeDifferenceWeight k n ∧
      polynomialNomeDifferenceWeight k n≤((2:Rat)^k)^n := by
  have hp := rational_nonneg_pow_mono (n:Rat) ((n+1:Nat):Rat) Rat.natCast_nonneg
    (by exact_mod_cast (show n≤n+1 by omega)) k
  have hn := Rat.pow_nonneg (a := (n:Rat)) (n := k) Rat.natCast_nonneg
  have hb := lambertWeight_bound n k
  unfold polynomialNomeDifferenceWeight
  constructor <;> grind only

def polynomialNomeDifferenceTerm (z : Scalar) (k n : Nat) : ComplexRaw :=
  scaleRat (polynomialNomeDifferenceWeight k n) (LocalODE.power z.val (n+1))

theorem polynomialNomeDifferenceTerm_valid (z : Scalar) (k n : Nat) :
    (polynomialNomeDifferenceTerm z k n).Valid := scaleRat_valid (LocalODE.power_valid _ z.property (n+1))

theorem polynomialNomeDifferenceTerm_bound (z : Scalar) (r : Rat) (k : Nat)
    (hr : 0≤r) (hz : Small z.val r) (n : Nat) :
    Small (polynomialNomeDifferenceTerm z k n) (2*r*(polynomialNomeMomentRatio r k)^n) := by
  have hw := polynomialNomeDifferenceWeight_bounds k n
  have h := LocalODE.small_scale hw.1 (LocalODE.power_small _ z.property r hr hz (n+1))
  apply h.mono
  have hm := Rat.mul_le_mul_of_nonneg_right hw.2
    (Rat.pow_nonneg (a := 2*r) (n := n+1) (Rat.mul_nonneg (by decide) hr))
  rw [Rat.pow_succ] at hm
  have hp : (polynomialNomeMomentRatio r k)^n=(2*r)^n*((2:Rat)^k)^n := by
    unfold polynomialNomeMomentRatio
    exact LocalODE.rational_mul_pow _ _ n
  rw [hp,Rat.pow_succ]
  grind only

def polynomialNomeDifferenceSum (z : Scalar) (r : Rat) (k : Nat) : ComplexRaw :=
  ScalarSeries.value (polynomialNomeDifferenceTerm z k) (polynomialNomeDifferenceTerm_valid z k)
    r (polynomialNomeMomentRatio r k)

theorem polynomialNomeDifferenceSum_valid (z : Scalar) (r : Rat) (k : Nat) (hr : 0≤r)
    (hlocal : polynomialNomeMomentRatio r k≤(1:Rat)/2) (hz : Small z.val r) :
    (polynomialNomeDifferenceSum z r k).Valid :=
  ScalarSeries.value_valid _ _ r _ hr (polynomialNomeMomentRatio_nonneg r k hr) hlocal
    (polynomialNomeDifferenceTerm_bound z r k hr hz)

theorem polynomialNomeDifferenceSum_close (z : Scalar) (r : Rat) (k : Nat) (hr : 0≤r)
    (hlocal : polynomialNomeMomentRatio r k≤(1:Rat)/2) (hz : Small z.val r) (N : Nat) :
    Small (sub (polynomialNomeDifferenceSum z r k)
      (ScalarSeries.block (polynomialNomeDifferenceTerm z k) 0 N))
      (4*r*(polynomialNomeMomentRatio r k)^N) :=
  ScalarSeries.value_close _ _ r _ hr (polynomialNomeMomentRatio_nonneg r k hr) hlocal
    (polynomialNomeDifferenceTerm_bound z r k hr hz) N

theorem polynomialNome_boundary_bound (z : Scalar) (r : Rat) (k : Nat) (hr : 0≤r)
    (hz : Small z.val r) (N : Nat) :
    Small (scaleRat ((N:Rat)^k) (LocalODE.power z.val (N+1)))
      (2*r*(polynomialNomeMomentRatio r k)^N) := by
  have hn := rational_nonneg_pow_mono (N:Rat) ((N+1:Nat):Rat) Rat.natCast_nonneg
    (by exact_mod_cast (show N≤N+1 by omega)) k
  have hb := Rat.le_trans hn (lambertWeight_bound N k)
  have h := LocalODE.small_scale (Rat.pow_nonneg (a := (N:Rat)) (n := k) Rat.natCast_nonneg)
    (LocalODE.power_small _ z.property r hr hz (N+1))
  apply h.mono
  have hm := Rat.mul_le_mul_of_nonneg_right hb
    (Rat.pow_nonneg (a := 2*r) (n := N+1) (Rat.mul_nonneg (by decide) hr))
  rw [Rat.pow_succ] at hm
  have hp : (polynomialNomeMomentRatio r k)^N=(2*r)^N*((2:Rat)^k)^N := by
    unfold polynomialNomeMomentRatio
    exact LocalODE.rational_mul_pow _ _ N
  rw [hp,Rat.pow_succ]
  grind only

end ComputableAnalysis.ModularForms
