import ComputableAnalysis.RiemannHilbert.GeneralSeries

/-! Finite represented first-order identities for arbitrary supplied coefficients. -/
namespace ComputableAnalysis.RiemannHilbert.BoundedSeries
open ComplexRaw FunctionTheory LocalODE

theorem valuePrefix_decomposition (c : Nat → ComplexRaw) (a z : ComplexRaw)
    (hc : ∀ n, (c n).Valid) (ha : a.Valid) (hz : z.Valid) (N : Nat) :
    ComplexRawQuotient.ofRaw (valueBlock c z 0 N) (valueBlock_valid c z hc hz 0 N) =
      ComplexRawQuotient.ofRaw (valueBlock c a 0 N) (valueBlock_valid c a hc ha 0 N) +
      ComplexRawQuotient.ofRaw (slopePrefix c a N)
        (slopePrefix_valid _ a (hc) ha N) *
        ComplexRawQuotient.ofRaw (sub z a) (sub_valid hz ha) +
      ComplexRawQuotient.ofRaw (remainderPrefix c a z N)
        (remainderPrefix_valid _ a z (hc) ha hz N) := by
  induction N with
  | zero =>
    change (0 : ScalarAlgebra.Value) = 0+0*ComplexRawQuotient.ofRaw (sub z a) (sub_valid hz ha)+0
    simp only [Lean.Grind.Semiring.zero_mul, Lean.Grind.Semiring.add_zero]
  | succ N ih =>
    simp only [valueBlock.eq_2, slopePrefix.eq_2, remainderPrefix.eq_2, Nat.zero_add]
    change (ComplexRawQuotient.ofRaw (valueBlock c z 0 N) (valueBlock_valid c z hc hz 0 N) +
      ComplexRawQuotient.ofRaw (c N) (hc N) * ComplexRawQuotient.ofRaw (power z N) (power_valid z hz N)) =
      (ComplexRawQuotient.ofRaw (valueBlock c a 0 N) (valueBlock_valid c a hc ha 0 N) +
        ComplexRawQuotient.ofRaw (c N) (hc N) * ComplexRawQuotient.ofRaw (power a N) (power_valid a ha N)) +
      (ComplexRawQuotient.ofRaw (slopePrefix c a N) (slopePrefix_valid _ a (hc) ha N) +
        ComplexRawQuotient.ofRaw (c N) (hc N) * ComplexRawQuotient.ofRaw (monomialSlope a N) (monomialSlope_valid a ha N)) *
        ComplexRawQuotient.ofRaw (sub z a) (sub_valid hz ha) +
      (ComplexRawQuotient.ofRaw (remainderPrefix c a z N) (remainderPrefix_valid _ a z (hc) ha hz N) +
        ComplexRawQuotient.ofRaw (c N) (hc N) * ComplexRawQuotient.ofRaw (monomialRemainder a z N) (monomialRemainder_valid a z ha hz N))
    rw [ih, monomial_decomposition a z ha hz N]
    simp only [ComplexRawQuotient.mul_add, ComplexRawQuotient.add_assoc,
      ComplexRawQuotient.mul_comm, ComplexRawQuotient.add_comm,
      ScalarAlgebra.mul_left_comm, ScalarAlgebra.add_left_comm]

theorem valuePrefix_remainder_identity (c : Nat → ComplexRaw) (a z : ComplexRaw)
    (hc : ∀ n, (c n).Valid) (ha : a.Valid) (hz : z.Valid) (N : Nat) :
    (sub (sub (valueBlock c z 0 N) (valueBlock c a 0 N))
      (mul (slopePrefix c a N) (sub z a))).Equiv
      (remainderPrefix c a z N) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := sub_valid
      (sub_valid (valueBlock_valid c z hc hz 0 N) (valueBlock_valid c a hc ha 0 N))
      (mul_valid (slopePrefix_valid _ a (hc) ha N) (sub_valid hz ha)))
    (hright := remainderPrefix_valid _ a z (hc) ha hz N)
  change ((ComplexRawQuotient.ofRaw (valueBlock c z 0 N) (valueBlock_valid c z hc hz 0 N) +
      -ComplexRawQuotient.ofRaw (valueBlock c a 0 N) (valueBlock_valid c a hc ha 0 N)) +
      -(ComplexRawQuotient.ofRaw (slopePrefix c a N) (slopePrefix_valid _ a (hc) ha N) *
        ComplexRawQuotient.ofRaw (sub z a) (sub_valid hz ha))) = _
  rw [valuePrefix_decomposition c a z hc ha hz N]
  exact ScalarAlgebra.extract_remainder _ _ _

theorem slopePrefix_derivativeBlock (c : Nat → ComplexRaw) (a : ComplexRaw)
    (hc : ∀ n, (c n).Valid) (ha : a.Valid) (N : Nat) :
    (slopePrefix c a (N+1)).Equiv
      (derivativeBlock c a 0 N) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := slopePrefix_valid _ a (hc) ha _)
    (hright := derivativeBlock_valid c a hc ha 0 N)
  induction N with
  | zero =>
    simp only [slopePrefix, monomialSlope, derivativeBlock]
    change (0 : ScalarAlgebra.Value)+ComplexRawQuotient.ofRaw (c 0) (hc 0)*0=0
    simp only [Lean.Grind.Semiring.mul_zero, Lean.Grind.Semiring.add_zero]
  | succ N ih =>
    simp only [slopePrefix.eq_2, derivativeBlock.eq_2, derivativeTerm, Nat.zero_add]
    change (ComplexRawQuotient.ofRaw (slopePrefix c a (N+1)) (slopePrefix_valid _ a (hc) ha (N+1)) +
      ComplexRawQuotient.ofRaw (c (N+1)) (hc (N+1)) *
        ComplexRawQuotient.ofRaw (monomialSlope a (N+1)) (monomialSlope_valid a ha (N+1))) =
      ComplexRawQuotient.ofRaw (derivativeBlock c a 0 N) (derivativeBlock_valid c a hc ha 0 N) +
        ComplexRawQuotient.scaleRat ((N+1 : Nat) : Rat)
          (ComplexRawQuotient.ofRaw (c (N+1)) (hc (N+1)) *
           ComplexRawQuotient.ofRaw (power a N) (power_valid a ha N))
    rw [ih, monomialSlope_image a ha N, ScalarAlgebra.ofRaw_power a ha N, ScalarAlgebra.scale_natural]
    simp only [ComplexRawQuotient.mul_assoc, ComplexRawQuotient.mul_comm]

end ComputableAnalysis.RiemannHilbert.BoundedSeries
