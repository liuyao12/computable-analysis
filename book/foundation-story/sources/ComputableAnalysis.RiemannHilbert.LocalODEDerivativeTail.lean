import ComputableAnalysis.RiemannHilbert.LocalODESum

/-!
# Quantitative tails for the scalar derivative series

These are bounds on the actual represented derivative-series terms and finite
blocks. They are a prerequisite for differentiating the constructed sum;
they do not themselves assert that this series is its analytic derivative.
-/
namespace ComputableAnalysis.RiemannHilbert.LocalODE

open ComplexRaw FunctionTheory

def derivativeTerm (a : Nat → ComplexRaw) (initial z : ComplexRaw) (k : Nat) : ComplexRaw :=
  scaleRat ((k+1 : Nat) : Rat) (mul (coefficient a initial (k+1)) (power z k))

theorem derivativeTerm_valid (a : Nat → ComplexRaw) (initial z : ComplexRaw)
    (ha : ∀ i, (a i).Valid) (h0 : initial.Valid) (hz : z.Valid) (k : Nat) :
    (derivativeTerm a initial z k).Valid :=
  scaleRat_valid (mul_valid (coefficient_valid a initial ha h0 _) (power_valid z hz _))

private theorem succ_le_two_pow (n : Nat) : n+1 ≤ 2^n := by
  induction n with
  | zero => decide
  | succ n ih =>
      calc
        n+1+1 ≤ 2*(n+1) := by omega
        _ ≤ 2*(2^n) := Nat.mul_le_mul_left 2 ih
        _ = 2^(n+1) := by rw [Nat.pow_succ]; omega

private theorem cast_two_pow (n : Nat) : ((2^n : Nat) : Rat) = (2 : Rat)^n := by
  induction n with
  | zero => decide +kernel
  | succ n ih =>
      rw [Nat.pow_succ, Rat.natCast_mul, Rat.pow_succ, ih]
      rfl

theorem derivativeTerm_majorant (a : Nat → ComplexRaw) (initial z : ComplexRaw)
    (ha : ∀ i, (a i).Valid) (h0 : initial.Valid) (hz : z.Valid)
    (M C K R : Rat) (hM : 0 ≤ M) (hC : 0 ≤ C) (hK : 0 ≤ K) (hR : 0 ≤ R)
    (hMK : 2*M ≤ K) (hab : ∀ i, Small (a i) (M*K^i))
    (hinit : Small initial C) (hpoint : Small z R) (k : Nat) :
    Small (derivativeTerm a initial z k) (2*C*K*(4*K*R)^k) := by
  have hq : 0 ≤ 2*K*R := Rat.mul_nonneg (Rat.mul_nonneg (by decide) hK) hR
  have hcoef := coefficient_majorant a initial ha h0 M C K hM hC hK hMK hab hinit (k+1)
  have hp := power_small z hz R hR hpoint k
  have hm := Small.mul (coefficient_valid a initial ha h0 (k+1)) (power_valid z hz k)
    (Rat.mul_nonneg hC (Rat.pow_nonneg hK))
    (Rat.pow_nonneg (Rat.mul_nonneg (by decide : (0 : Rat) ≤ 2) hR)) hcoef hp
  have he : 2*(C*K^(k+1))*(2*R)^k = 2*C*K*(2*K*R)^k := by
    rw [Rat.pow_succ]
    have hp : K^k*(2*R)^k = (2*K*R)^k := by
      rw [← rational_mul_pow]
      congr 1
      grind [Rat.mul_assoc, Rat.mul_comm]
    calc
      _ = (2*C*K)*(K^k*(2*R)^k) := by grind [Rat.mul_assoc, Rat.mul_comm]
      _ = _ := by rw [hp]
  rw [he] at hm
  have hn0 : 0 ≤ ((k+1 : Nat) : Rat) :=
    Rat.le_of_lt ((Rat.natCast_pos).2 (Nat.succ_pos k))
  have hs := small_scale hn0 hm
  apply hs.mono
  have hn : ((k+1 : Nat) : Rat) ≤ (2 : Rat)^k := by
    rw [← cast_two_pow]
    exact_mod_cast succ_le_two_pow k
  have hmain := Rat.mul_le_mul_of_nonneg_right hn (Rat.pow_nonneg (n := k) hq)
  have hconstant : 0 ≤ 2*C*K := Rat.mul_nonneg (Rat.mul_nonneg (by decide) hC) hK
  have hle := Rat.mul_le_mul_of_nonneg_left hmain hconstant
  have hpow : (2 : Rat)^k*(2*K*R)^k = (4*K*R)^k := by
    rw [← rational_mul_pow]
    congr 1
    grind [Rat.mul_assoc]
  rw [hpow] at hle
  grind [Rat.mul_assoc, Rat.mul_comm]

def derivativeBlock (a : Nat → ComplexRaw) (initial z : ComplexRaw) (N : Nat) :
    Nat → ComplexRaw
  | 0 => zero
  | k+1 => add (derivativeBlock a initial z N k) (derivativeTerm a initial z (N+k))

theorem derivativeBlock_valid (a : Nat → ComplexRaw) (initial z : ComplexRaw)
    (ha : ∀ i, (a i).Valid) (h0 : initial.Valid) (hz : z.Valid) (N k : Nat) :
    (derivativeBlock a initial z N k).Valid := by
  induction k with
  | zero => exact ofQComplex_valid QComplex.zero
  | succ k ih => exact add_valid ih (derivativeTerm_valid a initial z ha h0 hz _)

theorem derivativeBlock_majorant (a : Nat → ComplexRaw) (initial z : ComplexRaw)
    (ha : ∀ i, (a i).Valid) (h0 : initial.Valid) (hz : z.Valid)
    (M C K R : Rat) (hM : 0 ≤ M) (hC : 0 ≤ C) (hK : 0 ≤ K) (hR : 0 ≤ R)
    (hMK : 2*M ≤ K) (hab : ∀ i, Small (a i) (M*K^i))
    (hinit : Small initial C) (hpoint : Small z R) (N k : Nat) :
    Small (derivativeBlock a initial z N k)
      (RationalMajorant.geomTailPartial (2*C*K) (4*K*R) N k) := by
  induction k with
  | zero => exact Small.zero (by change (0 : Rat) ≤ 0; decide)
  | succ k ih =>
    exact small_add ih
      (derivativeTerm_majorant a initial z ha h0 hz M C K R hM hC hK hR hMK hab hinit hpoint _)

def derivativeTail (C K R : Rat) (N : Nat) : Rat := 4*C*K*(4*K*R)^N

theorem derivativeBlock_bound (a : Nat → ComplexRaw) (initial z : ComplexRaw)
    (ha : ∀ i, (a i).Valid) (h0 : initial.Valid) (hz : z.Valid)
    (M C K R : Rat) (hM : 0 ≤ M) (hC : 0 ≤ C) (hK : 0 ≤ K) (hR : 0 ≤ R)
    (hMK : 2*M ≤ K) (hab : ∀ i, Small (a i) (M*K^i))
    (hinit : Small initial C) (hpoint : Small z R)
    (hlocal : 4*K*R ≤ (1 : Rat)/2) (N k : Nat) :
    Small (derivativeBlock a initial z N k) (derivativeTail C K R N) := by
  have hs := derivativeBlock_majorant a initial z ha h0 hz M C K R hM hC hK hR hMK
    hab hinit hpoint N k
  apply hs.mono
  have ht := RationalMajorant.geometric_tail_partial_bound
    (C := 2*C*K) (r := 4*K*R) (N := N) (k := k)
    (Rat.mul_nonneg (Rat.mul_nonneg (by decide) hC) hK)
    (Rat.mul_nonneg (Rat.mul_nonneg (by decide) hK) hR) hlocal
  unfold derivativeTail
  unfold RationalMajorant.geomTailBound at ht
  grind [Rat.mul_assoc]

theorem derivativeTail_shrinks (C K R : Rat)
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hR : 0 ≤ R) (hlocal : 4*K*R ≤ (1 : Rat)/2) :
    ShrinksToZero (derivativeTail C K R) := by
  have hs := tail_bound_shrinks (C*K) (4*K*R) (Rat.mul_nonneg hC hK)
    (Rat.mul_nonneg (Rat.mul_nonneg (by decide) hK) hR) hlocal
  change ShrinksToZero (fun N => 4*C*K*(4*K*R)^N)
  simpa only [Rat.mul_assoc] using hs

end ComputableAnalysis.RiemannHilbert.LocalODE
