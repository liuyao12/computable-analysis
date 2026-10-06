import ComputableAnalysis.RiemannHilbert.MonomialRemainder
import ComputableAnalysis.RiemannHilbert.LocalODEDerivativeSum

/-! Finite coefficient-series identities and uniform quadratic remainders. -/
namespace ComputableAnalysis.RiemannHilbert.LocalODE
open ComplexRaw FunctionTheory

def slopePrefix (c : Nat → ComplexRaw) (a : ComplexRaw) : Nat → ComplexRaw
  | 0 => zero
  | n+1 => add (slopePrefix c a n) (mul (c n) (monomialSlope a n))

def remainderPrefix (c : Nat → ComplexRaw) (a z : ComplexRaw) : Nat → ComplexRaw
  | 0 => zero
  | n+1 => add (remainderPrefix c a z n) (mul (c n) (monomialRemainder a z n))

theorem slopePrefix_valid (c : Nat → ComplexRaw) (a : ComplexRaw)
    (hc : ∀ n, (c n).Valid) (ha : a.Valid) (N : Nat) : (slopePrefix c a N).Valid := by
  induction N with
  | zero => exact ofQComplex_valid _
  | succ N ih => exact add_valid ih (mul_valid (hc N) (monomialSlope_valid a ha N))

theorem remainderPrefix_valid (c : Nat → ComplexRaw) (a z : ComplexRaw)
    (hc : ∀ n, (c n).Valid) (ha : a.Valid) (hz : z.Valid) (N : Nat) :
    (remainderPrefix c a z N).Valid := by
  induction N with
  | zero => exact ofQComplex_valid _
  | succ N ih => exact add_valid ih (mul_valid (hc N) (monomialRemainder_valid a z ha hz N))

theorem quadratic_index_bound (n : Nat) : (n+2)*(n+1) ≤ 2*4^n := by
  induction n with
  | zero => decide
  | succ n ih =>
    calc
      (n+1+2)*(n+1+1) ≤ (4*(n+1))*(n+2) := Nat.mul_le_mul_right _ (by omega)
      _ = 4*((n+2)*(n+1)) := by simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      _ ≤ 4*(2*4^n) := Nat.mul_le_mul_left _ ih
      _ = 2*4^(n+1) := by rw [Nat.pow_succ]; omega

theorem cast_four_pow (n : Nat) : ((4^n : Nat) : Rat) = (4 : Rat)^n := by
  induction n with
  | zero => decide +kernel
  | succ n ih => rw [Nat.pow_succ, Rat.natCast_mul, Rat.pow_succ, ih]; rfl

theorem coefficient_remainder_bound (c : Nat → ComplexRaw) (a z : ComplexRaw)
    (hc : ∀ n, (c n).Valid) (ha : a.Valid) (hz : z.Valid)
    (C K R H : Rat) (hC : 0 ≤ C) (hK : 0 ≤ K) (hR : 0 ≤ R) (hH : 0 ≤ H)
    (hcB : ∀ n, Small (c n) (C*K^n))
    (haR : Small a R) (hzR : Small z R) (hza : Small (sub z a) H) (n : Nat) :
    Small (mul (c (n+2)) (monomialRemainder a z (n+2)))
      (8*C*K^2*H^2*(8*K*R)^n) := by
  have hq : 0 ≤ 2*R := Rat.mul_nonneg (by decide) hR
  have hn1 : 0 ≤ ((n+1 : Nat) : Rat) := Rat.le_of_lt ((Rat.natCast_pos).2 (by omega))
  have hn2 : 0 ≤ ((n+2 : Nat) : Rat) := Rat.le_of_lt ((Rat.natCast_pos).2 (by omega))
  have hb : 0 ≤ 2*((n+2 : Nat) : Rat)*((n+1 : Nat) : Rat)*(2*R)^n*H^2 :=
    Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg (by decide) hn2) hn1)
      (Rat.pow_nonneg hq)) (Rat.pow_nonneg hH)
  have hs := Small.mul (hc (n+2)) (monomialRemainder_valid a z ha hz (n+2))
    (Rat.mul_nonneg hC (Rat.pow_nonneg hK)) hb (hcB (n+2))
    (monomialRemainder_bound a z ha hz R H hR hH haR hzR hza n)
  apply hs.mono
  have hindex : ((n+2 : Nat) : Rat)*((n+1 : Nat) : Rat) ≤ 2*(4 : Rat)^n := by
    rw [← cast_four_pow]
    exact_mod_cast quadratic_index_bound n
  have hconst : 0 ≤ 4*C*K^(n+2)*(2*R)^n*H^2 :=
    Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg (by decide) hC)
      (Rat.pow_nonneg hK)) (Rat.pow_nonneg hq)) (Rat.pow_nonneg hH)
  have hle := Rat.mul_le_mul_of_nonneg_left hindex hconst
  have hp : (8*K*R)^n = (4 : Rat)^n*K^n*(2*R)^n := by
    have he : 8*K*R = (4*K)*(2*R) := by grind
    rw [he, rational_mul_pow, rational_mul_pow]
  rw [hp]
  simp only [Rat.pow_succ] at hle ⊢
  grind [Rat.mul_assoc, Rat.mul_comm]

theorem remainderPrefix_two_small (c : Nat → ComplexRaw) (a z : ComplexRaw)
    (hc : ∀ n, (c n).Valid) (ha : a.Valid) (hz : z.Valid) : Small (remainderPrefix c a z 2) 0 := by
  have h0 : Small (mul (c 0) (monomialRemainder a z 0)) 0 := by
    exact Small.congr (ofQComplex_valid _) (mul_valid (hc 0) (ofQComplex_valid _))
      (equiv_symm (mul_zero_equiv _ (hc 0))) (Small.zero (by decide))
  have h1 : Small (mul (c 1) (monomialRemainder a z 1)) 0 := by
    have hrem := monomialRemainder_one_small a z ha hz
    have he : (monomialRemainder a z 1).Equiv zero := by
      apply ComplexRawQuotient.equiv_of_ofRaw_eq
        (hleft := monomialRemainder_valid a z ha hz 1) (hright := ofQComplex_valid _)
      change ((0 : ScalarAlgebra.Value)*ComplexRawQuotient.ofRaw z hz +
        0*(ComplexRawQuotient.ofRaw (sub z a) (sub_valid hz ha)*
           ComplexRawQuotient.ofRaw (sub z a) (sub_valid hz ha))) = 0
      simp only [Lean.Grind.Semiring.zero_mul, Lean.Grind.Semiring.add_zero]
    have ht := mul_equiv (hc 1) (hc 1) (monomialRemainder_valid a z ha hz 1) (ofQComplex_valid _)
      (equiv_refl _ (hc 1)) he
    have he0 := equiv_trans (mul_valid (hc 1) (monomialRemainder_valid a z ha hz 1))
      (mul_valid (hc 1) (ofQComplex_valid _)) (ofQComplex_valid _) ht (mul_zero_equiv _ (hc 1))
    exact Small.congr (ofQComplex_valid _) (mul_valid (hc 1) (monomialRemainder_valid a z ha hz 1))
      (equiv_symm he0) (Small.zero (by decide))
  simpa only [remainderPrefix, Rat.zero_add] using
    small_add (small_add (Small.zero (r := 0) (by decide)) h0) h1

theorem remainderPrefix_majorant (c : Nat → ComplexRaw) (a z : ComplexRaw)
    (hc : ∀ n, (c n).Valid) (ha : a.Valid) (hz : z.Valid)
    (C K R H : Rat) (hC : 0 ≤ C) (hK : 0 ≤ K) (hR : 0 ≤ R) (hH : 0 ≤ H)
    (hcB : ∀ n, Small (c n) (C*K^n))
    (haR : Small a R) (hzR : Small z R) (hza : Small (sub z a) H) (N : Nat) :
    Small (remainderPrefix c a z (N+2))
      (RationalMajorant.geomTailPartial (8*C*K^2*H^2) (8*K*R) 0 N) := by
  induction N with
  | zero => exact remainderPrefix_two_small c a z hc ha hz
  | succ N ih =>
    have he : N+1+2 = (N+2)+1 := by omega
    rw [he, remainderPrefix, RationalMajorant.geomTailPartial]
    simpa only [Nat.zero_add] using small_add ih (coefficient_remainder_bound c a z hc ha hz C K R H
      hC hK hR hH hcB haR hzR hza N)

theorem remainderPrefix_bound (c : Nat → ComplexRaw) (a z : ComplexRaw)
    (hc : ∀ n, (c n).Valid) (ha : a.Valid) (hz : z.Valid)
    (C K R H : Rat) (hC : 0 ≤ C) (hK : 0 ≤ K) (hR : 0 ≤ R) (hH : 0 ≤ H)
    (hcB : ∀ n, Small (c n) (C*K^n))
    (haR : Small a R) (hzR : Small z R) (hza : Small (sub z a) H)
    (hlocal : 8*K*R ≤ (1 : Rat)/2) (N : Nat) :
    Small (remainderPrefix c a z (N+2)) (16*C*K^2*H^2) := by
  have hs := remainderPrefix_majorant c a z hc ha hz C K R H hC hK hR hH hcB haR hzR hza N
  apply hs.mono
  have ht := RationalMajorant.geometric_tail_partial_bound
    (C := 8*C*K^2*H^2) (r := 8*K*R) (N := 0) (k := N)
    (Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg (by decide) hC) (Rat.pow_nonneg hK))
      (Rat.pow_nonneg hH))
    (Rat.mul_nonneg (Rat.mul_nonneg (by decide) hK) hR) hlocal
  unfold RationalMajorant.geomTailBound at ht
  simp only [Rat.pow_zero, Rat.mul_one] at ht
  grind [Rat.mul_assoc]


theorem valuePrefix_decomposition (b : Nat → ComplexRaw) (initial a z : ComplexRaw)
    (hb : ∀ n, (b n).Valid) (h0 : initial.Valid) (ha : a.Valid) (hz : z.Valid) (N : Nat) :
    ComplexRawQuotient.ofRaw (tailBlock b initial z 0 N) (tailBlock_valid b initial z hb h0 hz 0 N) =
      ComplexRawQuotient.ofRaw (tailBlock b initial a 0 N) (tailBlock_valid b initial a hb h0 ha 0 N) +
      ComplexRawQuotient.ofRaw (slopePrefix (coefficient b initial) a N)
        (slopePrefix_valid _ a (coefficient_valid b initial hb h0) ha N) *
        ComplexRawQuotient.ofRaw (sub z a) (sub_valid hz ha) +
      ComplexRawQuotient.ofRaw (remainderPrefix (coefficient b initial) a z N)
        (remainderPrefix_valid _ a z (coefficient_valid b initial hb h0) ha hz N) := by
  induction N with
  | zero =>
    change (0 : ScalarAlgebra.Value) = 0+0*ComplexRawQuotient.ofRaw (sub z a) (sub_valid hz ha)+0
    simp only [Lean.Grind.Semiring.zero_mul, Lean.Grind.Semiring.add_zero]
  | succ N ih =>
    simp only [tailBlock.eq_2, slopePrefix.eq_2, remainderPrefix.eq_2, Nat.zero_add,
      ComplexRawQuotient.ofRaw_add, ComplexRawQuotient.ofRaw_mul]
    change (ComplexRawQuotient.ofRaw (tailBlock b initial z 0 N) (tailBlock_valid b initial z hb h0 hz 0 N) +
      ComplexRawQuotient.ofRaw (coefficient b initial N) (coefficient_valid b initial hb h0 N) * ComplexRawQuotient.ofRaw (power z N) (power_valid z hz N)) =
      (ComplexRawQuotient.ofRaw (tailBlock b initial a 0 N) (tailBlock_valid b initial a hb h0 ha 0 N) +
        ComplexRawQuotient.ofRaw (coefficient b initial N) (coefficient_valid b initial hb h0 N) * ComplexRawQuotient.ofRaw (power a N) (power_valid a ha N)) +
      (ComplexRawQuotient.ofRaw (slopePrefix (coefficient b initial) a N) (slopePrefix_valid _ a (coefficient_valid b initial hb h0) ha N) +
        ComplexRawQuotient.ofRaw (coefficient b initial N) (coefficient_valid b initial hb h0 N) * ComplexRawQuotient.ofRaw (monomialSlope a N) (monomialSlope_valid a ha N)) *
        ComplexRawQuotient.ofRaw (sub z a) (sub_valid hz ha) +
      (ComplexRawQuotient.ofRaw (remainderPrefix (coefficient b initial) a z N) (remainderPrefix_valid _ a z (coefficient_valid b initial hb h0) ha hz N) +
        ComplexRawQuotient.ofRaw (coefficient b initial N) (coefficient_valid b initial hb h0 N) * ComplexRawQuotient.ofRaw (monomialRemainder a z N) (monomialRemainder_valid a z ha hz N))
    rw [ih, monomial_decomposition a z ha hz N]
    simp only [ComplexRawQuotient.mul_add, ComplexRawQuotient.add_mul,
      ComplexRawQuotient.mul_assoc, ComplexRawQuotient.add_assoc,
      ComplexRawQuotient.mul_comm, ComplexRawQuotient.add_comm,
      ScalarAlgebra.mul_left_comm, ScalarAlgebra.add_left_comm]

theorem valuePrefix_remainder_identity (b : Nat → ComplexRaw) (initial a z : ComplexRaw)
    (hb : ∀ n, (b n).Valid) (h0 : initial.Valid) (ha : a.Valid) (hz : z.Valid) (N : Nat) :
    (sub (sub (tailBlock b initial z 0 N) (tailBlock b initial a 0 N))
      (mul (slopePrefix (coefficient b initial) a N) (sub z a))).Equiv
      (remainderPrefix (coefficient b initial) a z N) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := sub_valid
      (sub_valid (tailBlock_valid b initial z hb h0 hz 0 N) (tailBlock_valid b initial a hb h0 ha 0 N))
      (mul_valid (slopePrefix_valid _ a (coefficient_valid b initial hb h0) ha N) (sub_valid hz ha)))
    (hright := remainderPrefix_valid _ a z (coefficient_valid b initial hb h0) ha hz N)
  change ((ComplexRawQuotient.ofRaw (tailBlock b initial z 0 N) (tailBlock_valid b initial z hb h0 hz 0 N) +
      -ComplexRawQuotient.ofRaw (tailBlock b initial a 0 N) (tailBlock_valid b initial a hb h0 ha 0 N)) +
      -(ComplexRawQuotient.ofRaw (slopePrefix (coefficient b initial) a N) (slopePrefix_valid _ a (coefficient_valid b initial hb h0) ha N) *
        ComplexRawQuotient.ofRaw (sub z a) (sub_valid hz ha))) = _
  rw [valuePrefix_decomposition b initial a z hb h0 ha hz N]
  exact ScalarAlgebra.extract_remainder _ _ _

theorem slopePrefix_derivativeBlock (b : Nat → ComplexRaw) (initial a : ComplexRaw)
    (hb : ∀ n, (b n).Valid) (h0 : initial.Valid) (ha : a.Valid) (N : Nat) :
    (slopePrefix (coefficient b initial) a (N+1)).Equiv
      (derivativeBlock b initial a 0 N) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := slopePrefix_valid _ a (coefficient_valid b initial hb h0) ha _)
    (hright := derivativeBlock_valid b initial a hb h0 ha 0 N)
  induction N with
  | zero =>
    simp only [slopePrefix, coefficient_zero, monomialSlope, derivativeBlock]
    change (0 : ScalarAlgebra.Value)+ComplexRawQuotient.ofRaw initial h0*0=0
    simp only [Lean.Grind.Semiring.mul_zero, Lean.Grind.Semiring.add_zero]
  | succ N ih =>
    simp only [slopePrefix.eq_2, derivativeBlock.eq_2, derivativeTerm, Nat.zero_add,
      ComplexRawQuotient.ofRaw_add, ComplexRawQuotient.ofRaw_mul, ComplexRawQuotient.ofRaw_scaleRat]
    change (ComplexRawQuotient.ofRaw (slopePrefix (coefficient b initial) a (N+1)) (slopePrefix_valid _ a (coefficient_valid b initial hb h0) ha (N+1)) +
      ComplexRawQuotient.ofRaw (coefficient b initial (N+1)) (coefficient_valid b initial hb h0 (N+1)) *
        ComplexRawQuotient.ofRaw (monomialSlope a (N+1)) (monomialSlope_valid a ha (N+1))) =
      ComplexRawQuotient.ofRaw (derivativeBlock b initial a 0 N) (derivativeBlock_valid b initial a hb h0 ha 0 N) +
        ComplexRawQuotient.scaleRat ((N+1 : Nat) : Rat)
          (ComplexRawQuotient.ofRaw (coefficient b initial (N+1)) (coefficient_valid b initial hb h0 (N+1)) *
           ComplexRawQuotient.ofRaw (power a N) (power_valid a ha N))
    rw [ih, monomialSlope_image a ha N, ScalarAlgebra.ofRaw_power a ha N, ScalarAlgebra.scale_natural]
    simp only [ComplexRawQuotient.mul_assoc, ComplexRawQuotient.mul_comm, ScalarAlgebra.mul_left_comm]

end ComputableAnalysis.RiemannHilbert.LocalODE
