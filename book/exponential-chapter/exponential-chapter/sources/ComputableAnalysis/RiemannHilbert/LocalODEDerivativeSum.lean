import ComputableAnalysis.RiemannHilbert.LocalODEDerivativeTail

/-! Constructing the proposed derivative series. These sum the differentiated
coefficients; termwise differentiation of the value function is a separate obligation. -/
namespace ComputableAnalysis.RiemannHilbert.LocalODE
open ComplexRaw FunctionTheory

theorem derivativePrefix_append (a : Nat → ComplexRaw) (initial z : ComplexRaw)
    (ha : ∀ i, (a i).Valid) (h0 : initial.Valid) (hz : z.Valid) (N k : Nat) :
    (derivativeBlock a initial z 0 (N+k)).Equiv
      (add (derivativeBlock a initial z 0 N) (derivativeBlock a initial z N k)) := by
  induction k with
  | zero => exact equiv_symm (add_zero_equiv _ (derivativeBlock_valid a initial z ha h0 hz 0 N))
  | succ k ih =>
      change (add (derivativeBlock a initial z 0 (N+k))
        (derivativeTerm a initial z (0+(N+k)))).Equiv _
      simp only [Nat.zero_add]
      have hp := derivativeBlock_valid a initial z ha h0 hz 0 N
      have ht := derivativeBlock_valid a initial z ha h0 hz N k
      have hterm := derivativeTerm_valid a initial z ha h0 hz (N+k)
      apply equiv_trans
        (add_valid (derivativeBlock_valid a initial z ha h0 hz 0 (N+k)) hterm)
        (add_valid (add_valid hp ht) hterm) (add_valid hp (add_valid ht hterm))
      · exact add_equiv ih (equiv_refl _
          (derivativeTerm_valid a initial z ha h0 hz _))
      · exact add_assoc_equiv _ _ _
          (derivativeBlock_valid a initial z ha h0 hz 0 N)
          (derivativeBlock_valid a initial z ha h0 hz N k)
          (derivativeTerm_valid a initial z ha h0 hz _)

theorem derivativePrefix_difference_tail (a : Nat → ComplexRaw) (initial z : ComplexRaw)
    (ha : ∀ i, (a i).Valid) (h0 : initial.Valid) (hz : z.Valid) (N k : Nat) :
    (sub (derivativeBlock a initial z 0 (N+k)) (derivativeBlock a initial z 0 N)).Equiv
      (derivativeBlock a initial z N k) := by
  have hp := derivativeBlock_valid a initial z ha h0 hz 0 N
  have ht := derivativeBlock_valid a initial z ha h0 hz N k
  exact equiv_trans
    (sub_valid (derivativeBlock_valid a initial z ha h0 hz 0 (N+k)) hp)
    (sub_valid (add_valid hp ht) hp) ht
    (FunctionTheory.sub_congr (derivativePrefix_append a initial z ha h0 hz N k) (equiv_refl _ hp))
    (sub_add_cancel _ _ hp ht)

theorem derivativePrefix_cauchy (a : Nat → ComplexRaw) (initial z : ComplexRaw)
    (ha : ∀ i, (a i).Valid) (h0 : initial.Valid) (hz : z.Valid)
    (M C K R : Rat) (hM : 0 ≤ M) (hC : 0 ≤ C) (hK : 0 ≤ K) (hR : 0 ≤ R)
    (hMK : 2*M ≤ K) (hab : ∀ i, Small (a i) (M*K^i))
    (hinit : Small initial C) (hpoint : Small z R)
    (hlocal : 4*K*R ≤ (1 : Rat)/2) (N n : Nat) (hNn : N ≤ n) :
    Small (sub (derivativeBlock a initial z 0 n) (derivativeBlock a initial z 0 N)) (derivativeTail C K R N) := by
  have ht := derivativeBlock_bound a initial z ha h0 hz M C K R hM hC hK hR hMK hab hinit hpoint
    hlocal N (n-N)
  have he := derivativePrefix_difference_tail a initial z ha h0 hz N (n-N)
  rw [Nat.add_sub_of_le hNn] at he
  exact Small.congr (derivativeBlock_valid a initial z ha h0 hz N (n-N))
    (sub_valid (derivativeBlock_valid a initial z ha h0 hz 0 n)
      (derivativeBlock_valid a initial z ha h0 hz 0 N)) (equiv_symm he) ht

/-- All computations of the sum are rational finite boxes. The numerical
majorant parameters specify the radius used by finite stabilization. -/
def sumDerivative (a : Nat → ComplexRaw) (initial z : ComplexRaw)
    (ha : ∀ i, (a i).Valid) (h0 : initial.Valid) (hz : z.Valid)
    (C K R : Rat) : ComplexRaw :=
  RepresentedCauchySum.value (fun N => derivativeBlock a initial z 0 N)
    (derivativeBlock_valid a initial z ha h0 hz 0) (derivativeTail C K R)

theorem sumDerivative_valid (a : Nat → ComplexRaw) (initial z : ComplexRaw)
    (ha : ∀ i, (a i).Valid) (h0 : initial.Valid) (hz : z.Valid)
    (M C K R : Rat) (hM : 0 ≤ M) (hC : 0 ≤ C) (hK : 0 ≤ K) (hR : 0 ≤ R)
    (hMK : 2*M ≤ K) (hab : ∀ i, Small (a i) (M*K^i))
    (hinit : Small initial C) (hpoint : Small z R)
    (hlocal : 4*K*R ≤ (1 : Rat)/2) :
    (sumDerivative a initial z ha h0 hz C K R).Valid :=
  RepresentedCauchySum.value_valid _ _
    (derivativeTail C K R) (derivativeTail_shrinks C K R hC hK hR hlocal)
    (derivativePrefix_cauchy a initial z ha h0 hz M C K R hM hC hK hR hMK hab hinit hpoint hlocal)

/-- The evaluator is certified as this series sum, not merely as a valid
candidate. Error is measured against the actual represented prefixes. -/
theorem sumDerivative_close_prefix (a : Nat → ComplexRaw) (initial z : ComplexRaw)
    (ha : ∀ i, (a i).Valid) (h0 : initial.Valid) (hz : z.Valid)
    (M C K R : Rat) (hM : 0 ≤ M) (hC : 0 ≤ C) (hK : 0 ≤ K) (hR : 0 ≤ R)
    (hMK : 2*M ≤ K) (hab : ∀ i, Small (a i) (M*K^i))
    (hinit : Small initial C) (hpoint : Small z R)
    (hlocal : 4*K*R ≤ (1 : Rat)/2) (N : Nat) :
    Small (sub (sumDerivative a initial z ha h0 hz C K R) (derivativeBlock a initial z 0 N))
      (derivativeTail C K R N) :=
  RepresentedCauchySum.value_close_prefix _ _ _
    (derivativePrefix_cauchy a initial z ha h0 hz M C K R hM hC hK hR hMK hab hinit hpoint hlocal) N


theorem derivativeBlock_congr (a b : Nat → ComplexRaw) (x y z w : ComplexRaw)
    (ha : ∀ i, (a i).Valid) (hb : ∀ i, (b i).Valid)
    (hx : x.Valid) (hy : y.Valid) (hz : z.Valid) (hw : w.Valid)
    (hab : ∀ i, (a i).Equiv (b i)) (hxy : x.Equiv y) (hzw : z.Equiv w) (N k : Nat) :
    (derivativeBlock a x z N k).Equiv (derivativeBlock b y w N k) := by
  induction k with
  | zero => exact equiv_refl _ (ofQComplex_valid QComplex.zero)
  | succ k ih =>
      exact add_equiv ih (scaleRat_equiv (mul_equiv
        (coefficient_valid a x ha hx (_+1)) (coefficient_valid b y hb hy (_+1))
        (power_valid z hz _) (power_valid w hw _)
        (coefficient_congr a b x y ha hb hx hy hab hxy (_+1)) (power_congr z w hz hw hzw _)))

/-- The summed series respects coefficient, initial-value, and argument
representations. Bounds for the alternative implementation are transported,
not requested independently from the caller. -/
theorem sumDerivative_congr (a b : Nat → ComplexRaw) (x y z w : ComplexRaw)
    (ha : ∀ i, (a i).Valid) (hb : ∀ i, (b i).Valid)
    (hx : x.Valid) (hy : y.Valid) (hz : z.Valid) (hw : w.Valid)
    (hAB : ∀ i, (a i).Equiv (b i)) (hXY : x.Equiv y) (hZW : z.Equiv w)
    (M C K R : Rat) (hM : 0 ≤ M) (hC : 0 ≤ C) (hK : 0 ≤ K) (hR : 0 ≤ R)
    (hMK : 2*M ≤ K) (hab : ∀ i, Small (a i) (M*K^i))
    (hinit : Small x C) (hpoint : Small z R)
    (hlocal : 4*K*R ≤ (1 : Rat)/2) :
    (sumDerivative a x z ha hx hz C K R).Equiv (sumDerivative b y w hb hy hw C K R) := by
  have hbBound : ∀ i, Small (b i) (M*K^i) :=
    fun i => Small.congr (ha i) (hb i) (hAB i) (hab i)
  have hyBound := Small.congr hx hy hXY hinit
  have hwBound := Small.congr hz hw hZW hpoint
  have hq : 0 ≤ 4*K*R := Rat.mul_nonneg (Rat.mul_nonneg (by decide) hK) hR
  have ht := derivativeTail_shrinks C K R hC hK hR hlocal
  have hnonneg : ∀ N, 0 ≤ derivativeTail C K R N :=
    fun N => Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg (by decide) hC) hK) (Rat.pow_nonneg hq)
  exact RepresentedCauchySum.value_congr _ _ _ _ _ _ ht ht hnonneg hnonneg
    (derivativePrefix_cauchy a x z ha hx hz M C K R hM hC hK hR hMK hab hinit hpoint hlocal)
    (derivativePrefix_cauchy b y w hb hy hw M C K R hM hC hK hR hMK hbBound hyBound hwBound hlocal)
    (derivativeBlock_congr a b x y z w ha hb hx hy hz hw hAB hXY hZW 0)

/-- Auxiliary valid tail schedules cannot change the value. The Cauchy
hypotheses are finite bounds, not an assumed equality of the two sums. -/
theorem sumDerivative_independent (a : Nat → ComplexRaw) (initial z : ComplexRaw)
    (ha : ∀ i, (a i).Valid) (h0 : initial.Valid) (hz : z.Valid)
    (C K R D L S : Rat)
    (ht : ShrinksToZero (derivativeTail C K R)) (hs : ShrinksToZero (derivativeTail D L S))
    (ht0 : ∀ n, 0 ≤ derivativeTail C K R n) (hs0 : ∀ n, 0 ≤ derivativeTail D L S n)
    (hc : ∀ k n, k ≤ n → Small
      (sub (derivativeBlock a initial z 0 n) (derivativeBlock a initial z 0 k)) (derivativeTail C K R k))
    (hd : ∀ k n, k ≤ n → Small
      (sub (derivativeBlock a initial z 0 n) (derivativeBlock a initial z 0 k)) (derivativeTail D L S k)) :
    (sumDerivative a initial z ha h0 hz C K R).Equiv
      (sumDerivative a initial z ha h0 hz D L S) :=
  RepresentedCauchySum.value_congr _ _ _ _ _ _ ht hs ht0 hs0 hc hd
    (fun N => equiv_refl _ (derivativeBlock_valid a initial z ha h0 hz 0 N))

end ComputableAnalysis.RiemannHilbert.LocalODE
