import ComputableAnalysis.ModularForms.ExponentialLegacyTail
import ComputableAnalysis.ModularForms.EntireExponential

/-! Exact agreement of the rational exponential evaluators via their actual
common scheduled prefixes and independently proved shrinking errors. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert LocalODE SeriesLimitLaws

theorem rational_exponential_prefix_equiv (z : QComplex) (N : Nat) :
    (ScalarSeries.block (seriesTerm exponentialCoefficients (ofQComplex z)) 0 N).Equiv
      (ofQComplex (ComplexExponentialApproximation.expPrefix z N)) := by
  intro stage
  apply (compareAt_overlap_iff _ _ stage stage).mpr
  rw [rational_exponential_prefix_compute]
  change (QBox.point _).lo ≤ (QBox.point _).hi ∧ (QBox.point _).lo ≤ (QBox.point _).hi
  exact ⟨QComplex.le_refl _,QComplex.le_refl _⟩

theorem exponential_chart_legacy_agreement (z : QComplex) (C : Rat)
    (hC : 0 ≤ C) (hzC : QComplex.normBound z ≤ C) (R : QPos)
    (hzR : Small (ofQComplex z) R.val) :
    (BoundedSeries.sumValue exponentialCoefficients (ofQComplex z)
      exponentialCoefficients_valid (ofQComplex_valid z)
      (exponentialBudget (exponentialRatio R)) (exponentialRatio R) R.val).Equiv
      (ComplexExponentialApproximation.exponentialRawAt z C) := by
  let M := exponentialBudget (exponentialRatio R)
  let q := 2*exponentialRatio R*R.val
  let start := RationalMajorant.factorialTailStart C
  let p := fun n => ofQComplex (ComplexExponentialApproximation.expPrefix z (start+n))
  let e := fun (n : Nat) => 4*M*q^(start+n)
  let B := RationalMajorant.factorialTailTerm C start
  let f := fun (n : Nat) => 4*B*((1 : Rat)/2)^n
  have hM : 0 ≤ M := exponentialBudget_nonnegative _ (exponentialRatio_positive R)
  have hK := Rat.le_of_lt (exponentialRatio_positive R)
  have hR := Rat.le_of_lt R.property
  have hq : 0 ≤ q := Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) hK) hR
  have hlocal : q ≤ (1 : Rat)/2 := by
    have h := exponentialRatio_local R
    dsimp [q]
    grind
  have hB : 0 ≤ B := RationalMajorant.factorialTailTerm_nonneg hC start
  have he : ShrinksToZero e := by
    have h := shrinks_shift _ (tail_bound_shrinks M q hM hq hlocal) start
    simpa only [e, Nat.add_comm] using h
  have hf : ShrinksToZero f := tail_bound_shrinks B ((1 : Rat)/2) hB
    (by decide +kernel) (by decide +kernel)
  have hv := BoundedSeries.sumValue_valid _ _ exponentialCoefficients_valid (ofQComplex_valid z)
    M _ _ hM hK hR (exponentialCoefficients_small _ (exponentialRatio_positive R)) hzR hlocal
  have hl := ComplexExponentialApproximation.exponentialRawAt_valid hC hzC
  apply RepresentedCauchySum.unique p (fun n => ofQComplex_valid _) (fun n => e n+f n)
    (RepresentedCauchySum.sum_shrinks e f he hf) _ _ hv hl
  · intro n
    have hb := BoundedSeries.sumValue_close_prefix _ _ exponentialCoefficients_valid (ofQComplex_valid z)
      M _ _ hM hK hR (exponentialCoefficients_small _ (exponentialRatio_positive R)) hzR hlocal (start+n)
    rw [BoundedSeries.valueBlock_as_terms] at hb
    have heq := rational_exponential_prefix_equiv z (start+n)
    have hs := Small.congr
      (sub_valid hv (ScalarSeries.block_valid _ (seriesTerm_valid _ _ exponentialCoefficients_valid (ofQComplex_valid z)) 0 (start+n)))
      (sub_valid hv (ofQComplex_valid _))
      (FunctionTheory.sub_congr (equiv_refl _ hv) heq) hb
    apply hs.mono
    have hn : 0 ≤ f n := Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) hB)
      (Rat.pow_nonneg (by decide +kernel))
    change e n ≤ e n+f n
    grind
  · intro n
    have hb := legacy_exponential_prefix_error z C hC hzC n
    apply hb.mono
    have hn : 0 ≤ e n := Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) hM)
      (Rat.pow_nonneg hq)
    change f n ≤ e n+f n
    grind

/-- The global evaluator agrees with the older rational computation for
every rational complex input and every justified norm budget. -/
theorem entireExponential_legacy_rational (z : QComplex) (C : Rat)
    (hC : 0 ≤ C) (hzC : QComplex.normBound z ≤ C) :
    (entireExponentialValue ⟨ofQComplex z,ofQComplex_valid z⟩).val.Equiv
      (ComplexExponentialApproximation.exponentialRawAt z C) := by
  let a : Scalar := ⟨ofQComplex z,ofQComplex_valid z⟩
  let R := exponentialInputRadius a
  have ha := exponentialInputRadius_mem a
  obtain ⟨r,hr,hrR,hs⟩ := ha
  have hsR : Small a.val R.val := hs.mono (Rat.le_of_lt hrR)
  have hchart := exponential_chart_legacy_agreement z C hC hzC R hsR
  exact hchart

end ComputableAnalysis.ModularForms
