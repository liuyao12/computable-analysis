import ComputableAnalysis.RiemannHilbert.ScalarAlgebra

/-! Finite first-order monomial remainders at arbitrary represented inputs. -/
namespace ComputableAnalysis.RiemannHilbert.LocalODE
open ComplexRaw FunctionTheory

def monomialSlope (a : ComplexRaw) : Nat → ComplexRaw
  | 0 => zero
  | n+1 => add (mul (monomialSlope a n) a) (power a n)

def monomialRemainder (a z : ComplexRaw) : Nat → ComplexRaw
  | 0 => zero
  | n+1 => add (mul (monomialRemainder a z n) z)
    (mul (monomialSlope a n) (mul (sub z a) (sub z a)))

theorem monomialSlope_valid (a : ComplexRaw) (ha : a.Valid) (n : Nat) :
    (monomialSlope a n).Valid := by
  induction n with
  | zero => exact ofQComplex_valid _
  | succ n ih => exact add_valid (mul_valid ih ha) (power_valid a ha n)

theorem monomialRemainder_valid (a z : ComplexRaw) (ha : a.Valid) (hz : z.Valid) (n : Nat) :
    (monomialRemainder a z n).Valid := by
  induction n with
  | zero => exact ofQComplex_valid _
  | succ n ih =>
    exact add_valid (mul_valid ih hz)
      (mul_valid (monomialSlope_valid a ha n) (mul_valid (sub_valid hz ha) (sub_valid hz ha)))

theorem monomialSlope_image (a : ComplexRaw) (ha : a.Valid) (n : Nat) :
    ComplexRawQuotient.ofRaw (monomialSlope a (n+1)) (monomialSlope_valid a ha _) =
      ((n+1 : Nat) : ScalarAlgebra.Value) * (ComplexRawQuotient.ofRaw a ha)^n := by
  induction n with
  | zero =>
    change 0 * ComplexRawQuotient.ofRaw a ha + 1 = (1 : ScalarAlgebra.Value)*1
    simp only [Lean.Grind.Semiring.zero_mul, Lean.Grind.Semiring.mul_one]
    exact ComplexRawQuotient.zero_add _
  | succ n ih =>
    change ComplexRawQuotient.ofRaw (monomialSlope a (n+1)) (monomialSlope_valid a ha _) *
      ComplexRawQuotient.ofRaw a ha +
      ComplexRawQuotient.ofRaw (power a (n+1)) (power_valid a ha _) = _
    rw [ih, ScalarAlgebra.ofRaw_power]
    have hn : ((n+1+1 : Nat) : ScalarAlgebra.Value) = ((n+1 : Nat) : ScalarAlgebra.Value)+1 :=
      ScalarAlgebra.natural_succ (n+1)
    rw [hn, Lean.Grind.Semiring.pow_succ, Lean.Grind.Semiring.right_distrib, Lean.Grind.Semiring.one_mul, Lean.Grind.Semiring.mul_assoc]

theorem monomialSlope_formula (a : ComplexRaw) (ha : a.Valid) (n : Nat) :
    (monomialSlope a (n+1)).Equiv (scaleRat ((n+1 : Nat) : Rat) (power a n)) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := monomialSlope_valid a ha _) (hright := scaleRat_valid (power_valid a ha _))
  change ComplexRawQuotient.ofRaw (monomialSlope a (n+1)) (monomialSlope_valid a ha _) =
    ComplexRawQuotient.scaleRat ((n+1 : Nat) : Rat) (ComplexRawQuotient.ofRaw (power a n) (power_valid a ha n))
  rw [ ScalarAlgebra.ofRaw_power, ScalarAlgebra.scale_natural]
  exact monomialSlope_image a ha n

theorem monomial_decomposition (a z : ComplexRaw) (ha : a.Valid) (hz : z.Valid) (n : Nat) :
    ComplexRawQuotient.ofRaw (power z n) (power_valid z hz _) =
      ComplexRawQuotient.ofRaw (power a n) (power_valid a ha _) +
      ComplexRawQuotient.ofRaw (monomialSlope a n) (monomialSlope_valid a ha _) *
        ComplexRawQuotient.ofRaw (sub z a) (sub_valid hz ha) +
      ComplexRawQuotient.ofRaw (monomialRemainder a z n) (monomialRemainder_valid a z ha hz _) := by
  have hza : ComplexRawQuotient.ofRaw z hz =
      ComplexRawQuotient.ofRaw a ha + ComplexRawQuotient.ofRaw (sub z a) (sub_valid hz ha) :=
    (ScalarAlgebra.add_sub_cancel _ _).symm
  induction n with
  | zero =>
    change 1 = (1 : ScalarAlgebra.Value)+0*_+0
    simp only [Lean.Grind.Semiring.zero_mul, Lean.Grind.Semiring.add_zero]
  | succ n ih =>
    change ComplexRawQuotient.ofRaw (power z n) (power_valid z hz _) * ComplexRawQuotient.ofRaw z hz =
      ComplexRawQuotient.ofRaw (power a n) (power_valid a ha _) * ComplexRawQuotient.ofRaw a ha +
      (ComplexRawQuotient.ofRaw (monomialSlope a n) (monomialSlope_valid a ha _) *
        ComplexRawQuotient.ofRaw a ha + ComplexRawQuotient.ofRaw (power a n) (power_valid a ha _)) *
        ComplexRawQuotient.ofRaw (sub z a) (sub_valid hz ha) +
      (ComplexRawQuotient.ofRaw (monomialRemainder a z n) (monomialRemainder_valid a z ha hz _) *
        ComplexRawQuotient.ofRaw z hz +
        ComplexRawQuotient.ofRaw (monomialSlope a n) (monomialSlope_valid a ha _) *
          (ComplexRawQuotient.ofRaw (sub z a) (sub_valid hz ha) *
           ComplexRawQuotient.ofRaw (sub z a) (sub_valid hz ha)))
    rw [ih, hza]
    simp only [ComplexRawQuotient.mul_add, ComplexRawQuotient.add_mul,
      ComplexRawQuotient.mul_assoc, ComplexRawQuotient.add_assoc,
      ComplexRawQuotient.mul_comm, ComplexRawQuotient.add_comm,
      ScalarAlgebra.mul_left_comm, ScalarAlgebra.add_left_comm]

theorem monomial_remainder_identity (a z : ComplexRaw) (ha : a.Valid) (hz : z.Valid) (n : Nat) :
    (sub (sub (power z n) (power a n)) (mul (monomialSlope a n) (sub z a))).Equiv
      (monomialRemainder a z n) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := sub_valid (sub_valid (power_valid z hz _) (power_valid a ha _))
      (mul_valid (monomialSlope_valid a ha _) (sub_valid hz ha)))
    (hright := monomialRemainder_valid a z ha hz _)
  change ((ComplexRawQuotient.ofRaw (power z n) (power_valid z hz _) +
      -ComplexRawQuotient.ofRaw (power a n) (power_valid a ha _)) +
      -(ComplexRawQuotient.ofRaw (monomialSlope a n) (monomialSlope_valid a ha _) *
        ComplexRawQuotient.ofRaw (sub z a) (sub_valid hz ha))) = _
  rw [monomial_decomposition a z ha hz n]
  exact ScalarAlgebra.extract_remainder _ _ _


theorem monomialSlope_small (a : ComplexRaw) (ha : a.Valid) (R : Rat)
    (hR : 0 ≤ R) (haR : Small a R) (n : Nat) :
    Small (monomialSlope a (n+1)) (((n+1 : Nat) : Rat)*(2*R)^n) := by
  have hs := small_scale (Rat.le_of_lt ((Rat.natCast_pos).2 (Nat.succ_pos n)))
    (power_small a ha R hR haR n)
  exact Small.congr (scaleRat_valid (power_valid a ha n))
    (monomialSlope_valid a ha (n+1)) (equiv_symm (monomialSlope_formula a ha n)) hs

theorem monomialRemainder_one_small (a z : ComplexRaw) (ha : a.Valid) (hz : z.Valid) :
    Small (monomialRemainder a z 1) 0 := by
  have he : (monomialRemainder a z 1).Equiv zero :=
    equiv_trans (monomialRemainder_valid a z ha hz 1)
      (add_valid (ofQComplex_valid _) (ofQComplex_valid _)) (ofQComplex_valid _)
      (add_equiv (zero_mul_equiv z hz)
        (zero_mul_equiv _ (mul_valid (sub_valid hz ha) (sub_valid hz ha))))
      (add_zero_equiv _ (ofQComplex_valid _))
  exact Small.congr (ofQComplex_valid _) (monomialRemainder_valid a z ha hz 1)
    (equiv_symm he) (Small.zero (by decide))

/-- A quadratic remainder in every complex direction, at represented inputs.
The coefficient is finite and rational; no derivative law is assumed. -/
theorem monomialRemainder_bound (a z : ComplexRaw) (ha : a.Valid) (hz : z.Valid)
    (R H : Rat) (hR : 0 ≤ R) (hH : 0 ≤ H)
    (haR : Small a R) (hzR : Small z R) (hza : Small (sub z a) H) (n : Nat) :
    Small (monomialRemainder a z (n+2))
      (2*((n+2 : Nat) : Rat)*((n+1 : Nat) : Rat)*(2*R)^n*H^2) := by
  have hq : 0 ≤ 2*R := Rat.mul_nonneg (by decide) hR
  have hsq := Small.mul (sub_valid hz ha) (sub_valid hz ha) hH hH hza hza
  have hsq0 : 0 ≤ 2*H*H := Rat.mul_nonneg (Rat.mul_nonneg (by decide) hH) hH
  induction n with
  | zero =>
    have hleft := Small.mul (monomialRemainder_valid a z ha hz 1) hz (by decide) hR
      (monomialRemainder_one_small a z ha hz) hzR
    have hd := monomialSlope_small a ha R hR haR 0
    simp only [Rat.pow_zero, Rat.mul_one] at hd
    change Small (monomialSlope a 1) 1 at hd
    have hright := Small.mul (monomialSlope_valid a ha 1)
      (mul_valid (sub_valid hz ha) (sub_valid hz ha))
      (by decide : (0 : Rat) ≤ 1) hsq0
      hd hsq
    have hs := small_add hleft hright
    apply hs.mono
    simp only [Rat.pow_zero, Rat.mul_one, Rat.mul_zero]
    simp only [Rat.pow_succ, Rat.pow_zero]
    change 0*R+2*(2*H*H) ≤ 2*2*1*(1*H*H)
    grind
  | succ n ih =>
    have hB : 0 ≤ 2*((n+2 : Nat) : Rat)*((n+1 : Nat) : Rat)*(2*R)^n*H^2 :=
      Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg
        (Rat.mul_nonneg (by decide) (Rat.le_of_lt ((Rat.natCast_pos).2 (by omega))))
        (Rat.le_of_lt ((Rat.natCast_pos).2 (by omega)))) (Rat.pow_nonneg hq))
        (Rat.pow_nonneg hH)
    have hleft := Small.mul (monomialRemainder_valid a z ha hz (n+2)) hz hB hR ih hzR
    have hD : 0 ≤ ((n+2 : Nat) : Rat)*(2*R)^(n+1) :=
      Rat.mul_nonneg (Rat.le_of_lt ((Rat.natCast_pos).2 (by omega))) (Rat.pow_nonneg hq)
    have hright := Small.mul (monomialSlope_valid a ha (n+2))
      (mul_valid (sub_valid hz ha) (sub_valid hz ha)) hD hsq0
      (monomialSlope_small a ha R hR haR (n+1)) hsq
    have hs := small_add hleft hright
    apply hs.mono
    have h1 : ((n+1 : Nat) : Rat) = (n : Rat)+1 := by exact_mod_cast Nat.add_one n
    have h2 : ((n+2 : Nat) : Rat) = (n : Rat)+2 := by exact_mod_cast (rfl : n+2=n+2)
    have h3 : ((n+1+2 : Nat) : Rat) = (n : Rat)+3 := by exact_mod_cast (by omega : n+1+2=n+3)
    simp only [h1, h2, h3, Rat.pow_succ, Rat.pow_zero]
    grind [Rat.mul_assoc, Rat.mul_comm]

end ComputableAnalysis.RiemannHilbert.LocalODE
