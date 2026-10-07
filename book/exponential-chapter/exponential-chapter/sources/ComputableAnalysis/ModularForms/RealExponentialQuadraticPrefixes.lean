import ComputableAnalysis.ModularForms.RealExponentialOrder

/-! Quadratic lower bounds from the actual rational factorial prefixes. -/
namespace ComputableAnalysis.ModularForms
open ComplexExponentialApproximation

theorem real_exponential_prefix_quadratic_lower (t : Rat) (ht : 0 ≤ t) (n : Nat) :
    1+t+t*t/2 ≤ (expPrefix ⟨t,0⟩ (n+3)).re := by
  induction n with
  | zero =>
    simp [expPrefix,tailPartial,ComplexSeries.expTerm,QComplex.pow,QComplex.divRat,
      QComplex.mul,QComplex.add,QComplex.one,QComplex.zero,factorialRat,factorial]
    grind only
  | succ n ih =>
    rw [show n+1+3=(n+3)+1 by omega,expPrefix_succ]
    have hn := real_exponential_term_nonnegative t ht (n+3)
    change 1+t+t*t/2 ≤ (expPrefix ⟨t,0⟩ (n+3)).re+(ComplexSeries.expTerm ⟨t,0⟩ (n+3)).re
    grind only

theorem entireExponential_rational_real_quadratic_lower (t : Rat) (ht : 0 ≤ t) :
    (RealRaw.ofRat (1+t+t*t/2)).Le
      (entireExponentialValue ⟨ComplexRaw.ofQComplex ⟨t,0⟩,ComplexRaw.ofQComplex_valid _⟩).val.realPart := by
  let z : QComplex := ⟨t,0⟩
  have hz : QComplex.normBound z ≤ t := by
    change qabs t+qabs 0 ≤ t
    rw [qabs_eq_self_of_nonneg ht]
    simp [qabs,Rat.add_zero]
  let f := exponentialRawAt z t
  have hf : f.Valid := exponentialRawAt_valid ht hz
  have hl : (RealRaw.ofRat (1+t+t*t/2)).Le f.realPart := by
    intro n m
    have hn := ComplexRaw.valid_nestedIn hf (show m ≤ m+2 by omega)
    have hp := exponentialRawAt_contains_prefix ht hz (m+2)
    have hs : 3 ≤ RationalMajorant.factorialTailStart t+(m+2) := by
      unfold RationalMajorant.factorialTailStart
      omega
    have hb := real_exponential_prefix_quadratic_lower t ht
      (RationalMajorant.factorialTailStart t+(m+2)-3)
    rw [show RationalMajorant.factorialTailStart t+(m+2)-3+3=
      RationalMajorant.factorialTailStart t+(m+2) by omega] at hb
    change (1+t+t*t/2) ≤ (f.compute m).hi.re
    have hu := hp.2.1
    have hnest := hn.2.1
    exact Rat.le_trans hb (Rat.le_trans hu hnest)
  have he := ComplexRaw.realPart_equiv (ComplexRaw.equiv_symm
    (entireExponential_legacy_rational z t ht hz))
  exact RealRaw.le_trans (ComplexRaw.realPart_valid hf) hl
    (RealRaw.le_of_equiv (ComplexRaw.realPart_valid hf)
      (ComplexRaw.realPart_valid (entireExponentialValue _).property) he)


end ComputableAnalysis.ModularForms
