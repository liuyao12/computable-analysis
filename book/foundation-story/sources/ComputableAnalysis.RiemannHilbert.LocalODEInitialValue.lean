import ComputableAnalysis.RiemannHilbert.LocalODEDerivativeSum

/-! Exact center values of the constructed scalar series. -/
namespace ComputableAnalysis.RiemannHilbert.LocalODE
open ComplexRaw FunctionTheory

theorem power_zero_succ (k : Nat) : (power zero (k+1)).Equiv zero :=
  mul_zero_equiv _ (power_valid zero (ofQComplex_valid _) k)

theorem prefix_zero_succ (a : Nat → ComplexRaw) (initial : ComplexRaw)
    (ha : ∀ i, (a i).Valid) (h0 : initial.Valid) (N : Nat) :
    (tailBlock a initial zero 0 (N+1)).Equiv initial := by
  induction N with
  | zero =>
    simp only [tailBlock, Nat.zero_add, coefficient_zero, power]
    change (add zero (mul initial one)).Equiv initial
    exact equiv_trans (add_valid (ofQComplex_valid _) (mul_valid h0 (ofQComplex_valid _)))
      (mul_valid h0 (ofQComplex_valid _)) h0
      (zero_add_equiv _ (mul_valid h0 (ofQComplex_valid _))) (mul_one_equiv _ h0)
  | succ N ih =>
    change (add (tailBlock a initial zero 0 (N+1))
      (mul (coefficient a initial (0+(N+1))) (power zero (0+(N+1))))).Equiv initial
    simp only [Nat.zero_add]
    have hc := coefficient_valid a initial ha h0 (N+1)
    have hp := power_valid zero (ofQComplex_valid _) (N+1)
    have he := equiv_trans (mul_valid hc hp) (mul_valid hc (ofQComplex_valid _))
      (ofQComplex_valid _) (mul_equiv hc hc hp (ofQComplex_valid _)
        (equiv_refl _ hc) (power_zero_succ N)) (mul_zero_equiv _ hc)
    exact equiv_trans
      (add_valid (tailBlock_valid a initial zero ha h0 (ofQComplex_valid _) 0 (N+1))
        (mul_valid hc hp))
      (add_valid h0 (ofQComplex_valid _)) h0
      (add_equiv ih he) (add_zero_equiv _ h0)

theorem initial_close_zero_prefix (a : Nat → ComplexRaw) (initial : ComplexRaw)
    (ha : ∀ i, (a i).Valid) (h0 : initial.Valid) (C K R : Rat)
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hR : 0 ≤ R) (hinit : Small initial C) (N : Nat) :
    Small (sub initial (tailBlock a initial zero 0 N)) (valueTail C K R N) := by
  have ht : 0 ≤ valueTail C K R N :=
    Rat.mul_nonneg (Rat.mul_nonneg (by decide) hC)
      (Rat.pow_nonneg (Rat.mul_nonneg (Rat.mul_nonneg (by decide) hK) hR))
  cases N with
  | zero =>
    have he : (sub initial zero).Equiv initial := add_zero_equiv _ h0
    have hs := Small.congr h0 (sub_valid h0 (ofQComplex_valid _)) (equiv_symm he) hinit
    apply hs.mono
    change C ≤ 4*C*(2*K*R)^0
    simp only [Rat.pow_zero, Rat.mul_one]
    grind
  | succ N =>
    have hp := tailBlock_valid a initial zero ha h0 (ofQComplex_valid _) 0 (N+1)
    have he := FunctionTheory.sub_congr (equiv_refl _ h0) (prefix_zero_succ a initial ha h0 N)
    have hz := add_neg_equiv initial h0
    have hs : (sub initial (tailBlock a initial zero 0 (N+1))).Equiv zero :=
      equiv_trans (sub_valid h0 hp) (sub_valid h0 h0) (ofQComplex_valid _) he hz
    exact Small.congr (ofQComplex_valid _) (sub_valid h0 hp) (equiv_symm hs) (Small.zero ht)

theorem sumValue_initial (a : Nat → ComplexRaw) (initial : ComplexRaw)
    (ha : ∀ i, (a i).Valid) (h0 : initial.Valid)
    (M C K R : Rat) (hM : 0 ≤ M) (hC : 0 ≤ C) (hK : 0 ≤ K) (hR : 0 ≤ R)
    (hMK : 2*M ≤ K) (hab : ∀ i, Small (a i) (M*K^i))
    (hinit : Small initial C) (hlocal : 2*K*R ≤ (1 : Rat)/2) :
    (sumValue a initial zero ha h0 (ofQComplex_valid _) C K R).Equiv initial := by
  have hz : Small zero R := Small.zero hR
  exact RepresentedCauchySum.unique _ (tailBlock_valid a initial zero ha h0 (ofQComplex_valid _) 0)
    (valueTail C K R)
    (tail_bound_shrinks C (2*K*R) hC
      (Rat.mul_nonneg (Rat.mul_nonneg (by decide) hK) hR) hlocal)
    _ initial
    (sumValue_valid a initial zero ha h0 (ofQComplex_valid _) M C K R
      hM hC hK hR hMK hab hinit hz hlocal) h0
    (sumValue_close_prefix a initial zero ha h0 (ofQComplex_valid _) M C K R
      hM hC hK hR hMK hab hinit hz hlocal)
    (initial_close_zero_prefix a initial ha h0 C K R hC hK hR hinit)

end ComputableAnalysis.RiemannHilbert.LocalODE
