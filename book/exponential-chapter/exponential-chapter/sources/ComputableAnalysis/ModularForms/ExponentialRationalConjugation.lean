import ComputableAnalysis.ModularForms.ExponentialConjugatePrefixes
import ComputableAnalysis.ModularForms.ExponentialLegacyAgreement

/-! Actual exponential conjugation at rational complex inputs from literal prefixes. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory SeriesLimitLaws

theorem legacyExponential_conjugation (z : QComplex) (C : Rat) (hC : 0≤C)
    (hz : QComplex.normBound z≤C) :
    (conj (ComplexExponentialApproximation.exponentialRawAt z C)).Equiv
      (ComplexExponentialApproximation.exponentialRawAt (QComplex.conj z) C) := by
  have hcz : QComplex.normBound (QComplex.conj z)≤C := by
    simpa only [QComplex.normBound,QComplex.conj,qabs_neg] using hz
  let start := RationalMajorant.factorialTailStart C
  let B := RationalMajorant.factorialTailTerm C start
  let e := fun (n : Nat) => 4*B*((1:Rat)/2)^n
  have hB : 0≤B := RationalMajorant.factorialTailTerm_nonneg hC start
  have he : ShrinksToZero e := LocalODE.tail_bound_shrinks B (1/2) hB (by decide +kernel) (by decide +kernel)
  have hen (n : Nat) : 0≤e n := Rat.mul_nonneg (Rat.mul_nonneg (by decide) hB)
    (Rat.pow_nonneg (show (0:Rat)≤1/2 by decide +kernel))
  apply conjugateLimit_comparison _ _
    (ComplexExponentialApproximation.exponentialRawAt_valid hC hz)
    (ComplexExponentialApproximation.exponentialRawAt_valid hC hcz)
    (fun n => ofQComplex (ComplexExponentialApproximation.expPrefix z (start+n)))
    (fun n => ofQComplex (ComplexExponentialApproximation.expPrefix (QComplex.conj z) (start+n)))
    (fun _ => ofQComplex_valid _) (fun _ => ofQComplex_valid _) e e he he hen hen
    (legacy_exponential_prefix_error z C hC hz)
    (legacy_exponential_prefix_error (QComplex.conj z) C hC hcz)
  intro n k
  apply (compareAt_overlap_iff _ _ k k).mpr
  change QComplex.conj (ComplexExponentialApproximation.expPrefix z (start+n)) ≤
    ComplexExponentialApproximation.expPrefix (QComplex.conj z) (start+n) ∧
    ComplexExponentialApproximation.expPrefix (QComplex.conj z) (start+n) ≤
      QComplex.conj (ComplexExponentialApproximation.expPrefix z (start+n))
  rw [rationalExp_prefix_conjugate]
  exact ⟨QComplex.le_refl _,QComplex.le_refl _⟩

theorem entireExponential_rational_conjugation (z : QComplex) :
    (conj (entireExponentialValue ⟨ofQComplex z,ofQComplex_valid _⟩).val).Equiv
      (entireExponentialValue ⟨ofQComplex (QComplex.conj z),ofQComplex_valid _⟩).val := by
  let C := QComplex.normBound z
  have hC : 0≤C := QComplex.normBound_nonneg z
  have hz : QComplex.normBound z≤C := Rat.le_refl
  have hcz : QComplex.normBound (QComplex.conj z)≤C := by
    simpa only [QComplex.normBound,QComplex.conj,qabs_neg] using hz
  have h1 := conj_equiv (entireExponential_legacy_rational z C hC hz)
  have h2 := legacyExponential_conjugation z C hC hz
  have h3 := equiv_symm (entireExponential_legacy_rational (QComplex.conj z) C hC hcz)
  exact equiv_trans (conj_valid _ (entireExponentialValue ⟨ofQComplex z,ofQComplex_valid _⟩).property)
    (conj_valid _ (ComplexExponentialApproximation.exponentialRawAt_valid hC hz))
    (entireExponentialValue ⟨ofQComplex (QComplex.conj z),ofQComplex_valid _⟩).property h1
    (equiv_trans (conj_valid _ (ComplexExponentialApproximation.exponentialRawAt_valid hC hz))
      (ComplexExponentialApproximation.exponentialRawAt_valid hC hcz)
      (entireExponentialValue ⟨ofQComplex (QComplex.conj z),ofQComplex_valid _⟩).property h2 h3)

end ComputableAnalysis.ModularForms
