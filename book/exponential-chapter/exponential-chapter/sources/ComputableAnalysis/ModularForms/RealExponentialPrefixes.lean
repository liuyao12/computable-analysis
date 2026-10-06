import ComputableAnalysis.ModularForms.ExponentialLegacyAgreement

/-! Positivity and linear lower bounds for the actual rational factorial prefixes. -/
namespace ComputableAnalysis.ModularForms
open ComplexExponentialApproximation

theorem real_exponential_power (t : Rat) (n : Nat) :
    QComplex.pow ⟨t,0⟩ n = ⟨t^n,0⟩ := by
  induction n with
  | zero => simp [QComplex.pow,Rat.pow_zero,QComplex.one]
  | succ n ih =>
    simp only [QComplex.pow,ih,QComplex.mul,Rat.pow_succ]
    congr 1 <;> grind only

theorem real_exponential_term (t : Rat) (n : Nat) :
    ComplexSeries.expTerm ⟨t,0⟩ n = ⟨t^n/factorialRat n,0⟩ := by
  unfold ComplexSeries.expTerm
  rw [real_exponential_power]
  simp [QComplex.divRat,Rat.div_def,Rat.zero_mul]

theorem real_exponential_term_nonnegative (t : Rat) (ht : 0 ≤ t) (n : Nat) :
    0 ≤ (ComplexSeries.expTerm ⟨t,0⟩ n).re := by
  rw [real_exponential_term]
  exact Rat.mul_nonneg (Rat.pow_nonneg ht)
    (Rat.le_of_lt (Rat.inv_pos.mpr (RationalMajorant.factorialRat_pos n)))

theorem real_exponential_prefix_imag_zero (t : Rat) (n : Nat) :
    (expPrefix ⟨t,0⟩ n).im = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [expPrefix_succ]; unfold term; rw [real_exponential_term]; change _ + 0 = 0; rw [ih,Rat.add_zero]

theorem real_exponential_prefix_linear_lower (t : Rat) (ht : 0 ≤ t) (n : Nat) :
    1+t ≤ (expPrefix ⟨t,0⟩ (n+2)).re := by
  induction n with
  | zero =>
    simp [expPrefix,tailPartial,ComplexSeries.expTerm,QComplex.pow,QComplex.divRat,
      QComplex.mul,QComplex.add,QComplex.one,QComplex.zero,factorialRat,factorial]
    grind only
  | succ n ih =>
    rw [show n+1+2=(n+2)+1 by omega,expPrefix_succ]
    have hn := real_exponential_term_nonnegative t ht (n+2)
    change 1+t ≤ (expPrefix ⟨t,0⟩ (n+2)).re+(ComplexSeries.expTerm ⟨t,0⟩ (n+2)).re
    grind only

theorem entireExponential_rational_real_linear_lower (t : Rat) (ht : 0 ≤ t) :
    (RealRaw.ofRat (1+t)).Le
      (entireExponentialValue ⟨ComplexRaw.ofQComplex ⟨t,0⟩,ComplexRaw.ofQComplex_valid _⟩).val.realPart := by
  let z : QComplex := ⟨t,0⟩
  have hz : QComplex.normBound z ≤ t := by
    change qabs t+qabs 0 ≤ t
    rw [qabs_eq_self_of_nonneg ht]
    simp [qabs,Rat.add_zero]
  let f := exponentialRawAt z t
  have hf : f.Valid := exponentialRawAt_valid ht hz
  have hl : (RealRaw.ofRat (1+t)).Le f.realPart := by
    intro n m
    have hn := ComplexRaw.valid_nestedIn hf (show m ≤ m+1 by omega)
    have hp := exponentialRawAt_contains_prefix ht hz (m+1)
    have hs : 2 ≤ RationalMajorant.factorialTailStart t+(m+1) := by
      unfold RationalMajorant.factorialTailStart
      omega
    have hb := real_exponential_prefix_linear_lower t ht
      (RationalMajorant.factorialTailStart t+(m+1)-2)
    rw [show RationalMajorant.factorialTailStart t+(m+1)-2+2=
      RationalMajorant.factorialTailStart t+(m+1) by omega] at hb
    change (1+t) ≤ (f.compute m).hi.re
    have hu := hp.2.1
    have hnest := hn.2.1
    exact Rat.le_trans hb (Rat.le_trans hu hnest)
  have he := ComplexRaw.realPart_equiv (ComplexRaw.equiv_symm
    (entireExponential_legacy_rational z t ht hz))
  exact RealRaw.le_trans (ComplexRaw.realPart_valid hf) hl
    (RealRaw.le_of_equiv (ComplexRaw.realPart_valid hf)
      (ComplexRaw.realPart_valid (entireExponentialValue _).property) he)

end ComputableAnalysis.ModularForms
