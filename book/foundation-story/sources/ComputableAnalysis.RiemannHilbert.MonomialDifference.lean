import ComputableAnalysis.RiemannHilbert.SeriesRemainder

/-! Exact secant factorizations and bounds for represented monomials. -/
namespace ComputableAnalysis.RiemannHilbert.LocalODE
open ComplexRaw FunctionTheory

def monomialSecant (a z : ComplexRaw) : Nat → ComplexRaw
  | 0 => zero
  | n+1 => add (mul (monomialSecant a z n) z) (power a n)

theorem monomialSecant_valid (a z : ComplexRaw) (ha : a.Valid) (hz : z.Valid) (n : Nat) :
    (monomialSecant a z n).Valid := by
  induction n with
  | zero => exact ofQComplex_valid _
  | succ n ih => exact add_valid (mul_valid ih hz) (power_valid a ha n)

theorem monomial_secant_decomposition (a z : ComplexRaw) (ha : a.Valid) (hz : z.Valid) (n : Nat) :
    ComplexRawQuotient.ofRaw (power z n) (power_valid z hz n) =
      ComplexRawQuotient.ofRaw (power a n) (power_valid a ha n) +
      ComplexRawQuotient.ofRaw (monomialSecant a z n) (monomialSecant_valid a z ha hz n) *
        ComplexRawQuotient.ofRaw (sub z a) (sub_valid hz ha) := by
  have hza : ComplexRawQuotient.ofRaw z hz =
      ComplexRawQuotient.ofRaw a ha + ComplexRawQuotient.ofRaw (sub z a) (sub_valid hz ha) :=
    (ScalarAlgebra.add_sub_cancel _ _).symm
  induction n with
  | zero => change (1 : ScalarAlgebra.Value)=1+0*_; grind
  | succ n ih =>
    change ComplexRawQuotient.ofRaw (power z n) (power_valid z hz n)*ComplexRawQuotient.ofRaw z hz =
      ComplexRawQuotient.ofRaw (power a n) (power_valid a ha n)*ComplexRawQuotient.ofRaw a ha +
      (ComplexRawQuotient.ofRaw (monomialSecant a z n) (monomialSecant_valid a z ha hz n)*
        ComplexRawQuotient.ofRaw z hz + ComplexRawQuotient.ofRaw (power a n) (power_valid a ha n))*
          ComplexRawQuotient.ofRaw (sub z a) (sub_valid hz ha)
    grind

theorem power_difference_factor (a z : ComplexRaw) (ha : a.Valid) (hz : z.Valid) (n : Nat) :
    (sub (power z n) (power a n)).Equiv (mul (monomialSecant a z n) (sub z a)) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := sub_valid (power_valid z hz n) (power_valid a ha n))
    (hright := mul_valid (monomialSecant_valid a z ha hz n) (sub_valid hz ha))
  change ComplexRawQuotient.ofRaw (power z n) (power_valid z hz n) -
    ComplexRawQuotient.ofRaw (power a n) (power_valid a ha n) =
    ComplexRawQuotient.ofRaw (monomialSecant a z n) (monomialSecant_valid a z ha hz n) *
      ComplexRawQuotient.ofRaw (sub z a) (sub_valid hz ha)
  have := monomial_secant_decomposition a z ha hz n
  grind

theorem monomialSecant_bound (a z : ComplexRaw) (ha : a.Valid) (hz : z.Valid)
    (R : Rat) (hR : 0 ≤ R) (haR : Small a R) (hzR : Small z R) (n : Nat) :
    Small (monomialSecant a z (n+1)) (((n+1 : Nat) : Rat)*(2*R)^n) := by
  have hq : 0 ≤ 2*R := Rat.mul_nonneg (by decide) hR
  induction n with
  | zero =>
    have he : (monomialSecant a z 1).Equiv one := equiv_trans
      (monomialSecant_valid a z ha hz 1)
      (add_valid (ofQComplex_valid _) (ofQComplex_valid _)) (ofQComplex_valid _)
      (add_equiv (zero_mul_equiv z hz) (equiv_refl _ (ofQComplex_valid _)))
      (zero_add_equiv _ (ofQComplex_valid _))
    have hs := power_small a ha R hR haR 0
    rw [Rat.pow_zero] at hs
    change Small one 1 at hs
    have ht := Small.congr (ofQComplex_valid _) (monomialSecant_valid a z ha hz 1) (equiv_symm he) hs
    simp only [Rat.pow_zero, Rat.mul_one]
    change Small (monomialSecant a z 1) 1
    exact ht
  | succ n ih =>
    have hB : 0 ≤ ((n+1 : Nat) : Rat)*(2*R)^n :=
      Rat.mul_nonneg (Rat.le_of_lt ((Rat.natCast_pos).2 (by omega))) (Rat.pow_nonneg hq)
    have hs := small_add
      (Small.mul (monomialSecant_valid a z ha hz (n+1)) hz hB hR ih hzR)
      (power_small a ha R hR haR (n+1))
    apply hs.mono
    have h1 : ((n+1 : Nat) : Rat) = (n : Rat)+1 := by exact_mod_cast Nat.add_one n
    have h2 : ((n+1+1 : Nat) : Rat) = (n : Rat)+2 := by exact_mod_cast (by omega : n+1+1=n+2)
    rw [h1,h2,Rat.pow_succ]
    grind

theorem power_difference_bound (a z : ComplexRaw) (ha : a.Valid) (hz : z.Valid)
    (R H : Rat) (hR : 0 ≤ R) (hH : 0 ≤ H)
    (haR : Small a R) (hzR : Small z R) (hza : Small (sub z a) H) (n : Nat) :
    Small (sub (power z (n+1)) (power a (n+1)))
      (2*((n+1 : Nat) : Rat)*(2*R)^n*H) := by
  have hq : 0 ≤ 2*R := Rat.mul_nonneg (by decide) hR
  have hs := Small.mul (monomialSecant_valid a z ha hz (n+1)) (sub_valid hz ha)
    (Rat.mul_nonneg (Rat.le_of_lt ((Rat.natCast_pos).2 (by omega))) (Rat.pow_nonneg hq))
    hH (monomialSecant_bound a z ha hz R hR haR hzR n) hza
  have he : 2*(((n+1 : Nat) : Rat)*(2*R)^n)*H = 2*((n+1 : Nat) : Rat)*(2*R)^n*H := by grind
  rw [he] at hs
  exact Small.congr (mul_valid (monomialSecant_valid a z ha hz (n+1)) (sub_valid hz ha))
    (sub_valid (power_valid z hz (n+1)) (power_valid a ha (n+1)))
    (equiv_symm (power_difference_factor a z ha hz (n+1))) hs

end ComputableAnalysis.RiemannHilbert.LocalODE
