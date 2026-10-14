import ComputableAnalysis.ComplexExponentialApproximation
import ComputableAnalysis.GaussianDifferential

/-!
# Real-axis compatibility of the complex exponential evaluator

The bounded complex Taylor evaluator and the established adaptive real
factorial-series evaluator use different schedules.  This module proves that
they represent the same value at every rational real input by exhibiting a
common later finite Taylor prefix in both stage boxes.
-/

namespace ComputableAnalysis

namespace QComplex

theorem pow_ofRat (x : Rat) (n : Nat) :
    pow (ofRat x) n = ofRat (x ^ n) := by
  induction n with
  | zero =>
      unfold pow one ofRat
      rw [Rat.pow_zero]
  | succ n ih =>
      rw [pow, ih, Rat.pow_succ]
      unfold mul ofRat
      congr 1 <;> grind [Rat.mul_assoc, Rat.mul_comm]

end QComplex

namespace ComplexExponentialApproximation

theorem term_ofRat (x : Rat) (n : Nat) :
    term (QComplex.ofRat x) n =
      QComplex.ofRat (ExpProofs.powerSeriesTermAtTerms x n) := by
  rw [ExpProofs.powerSeriesTermAtTerms_eq_expCoeff_monomial]
  unfold term ComplexSeries.expTerm
  rw [QComplex.pow_ofRat]
  unfold QComplex.divRat FormalPowerSeries.expCoeff QComplex.ofRat
  congr 1
  · grind [Rat.div_def, Rat.mul_assoc, Rat.mul_comm]
  · rw [Rat.div_def, Rat.zero_mul]

theorem expPrefix_ofRat (x : Rat) (terms : Nat) :
    expPrefix (QComplex.ofRat x) terms =
      QComplex.ofRat (ExpProofs.powerSeriesCenterAtTerms x terms) := by
  induction terms with
  | zero =>
      have hcenterOne :=
        ExpProofs.powerSeriesCenterAtTerms_eq_expTaylorPrefix x 0
      have hsucc := ExpProofs.powerSeriesCenterAtTerms_succ x 0
      have hterm := ExpProofs.powerSeriesTermAtTerms_eq_expCoeff_monomial x 0
      have hcenterZero : ExpProofs.powerSeriesCenterAtTerms x 0 = 0 := by
        simp [FinitePolynomial.expTaylorPrefix,
          FinitePolynomial.integratedTaylorPrefix,
          FormalPowerSeries.expCoeff, factorialRat, factorial] at hcenterOne hterm
        grind
      rw [hcenterZero]
      rfl
  | succ terms ih =>
      rw [expPrefix_succ, ih, term_ofRat,
        ExpProofs.powerSeriesCenterAtTerms_succ]
      unfold QComplex.add QComplex.ofRat
      congr 1 <;> grind

/-- The complex Taylor evaluator at a rational real input agrees with the
real-axis embedding of the repository's adaptive factorial-series evaluator.
The proof uses one explicitly selected later prefix as a common rational
witness. -/
theorem exponentialRawAt_equiv_ofRealRaw_expPowerSeries
    (x C : Rat) (hC : 0 <= C) (hx : qabs x <= C) :
    (exponentialRawAt (QComplex.ofRat x) C).Equiv
      (ComplexRaw.ofRealRaw (expPowerSeries x)) := by
  have hz : QComplex.normBound (QComplex.ofRat x) <= C := by
    unfold QComplex.normBound QComplex.ofRat
    rw [show qabs (0 : Rat) = 0 by native_decide, Rat.add_zero]
    exact hx
  have hexpValid := exponentialRawAt_valid hC hz
  have hseriesValid := ExpProofs.expPowerSeries_valid x
  intro stage
  apply (ComplexRaw.compareAt_overlap_iff
    (exponentialRawAt (QComplex.ofRat x) C)
    (ComplexRaw.ofRealRaw (expPowerSeries x)) stage stage).2
  let base := RationalMajorant.factorialTailStart C
  let futureStage := base + stage
  let terms := expPowerSeriesTerms x futureStage
  have hbaseTerms : base + stage <= terms := by
    dsimp [base, futureStage, terms]
    unfold expPowerSeriesTerms
    omega
  let complexStage := terms - base
  have hstageComplex : stage <= complexStage := by
    dsimp [complexStage]
    omega
  have hterms : base + complexStage = terms := by
    dsimp [complexStage]
    omega
  let witness := ExpProofs.powerSeriesCenterAtTerms x terms
  have hcomplexPoint := exponentialRawAt_contains_prefix hC hz complexStage
  have hcomplexNested := ComplexRaw.valid_nestedIn hexpValid hstageComplex
  have hcomplexAtStage :
      (QBox.point (QComplex.ofRat witness)).NestedIn
        ((exponentialRawAt (QComplex.ofRat x) C).compute stage) := by
    apply QBox.nested_trans ?_ hcomplexNested
    rw [expPrefix_ofRat] at hcomplexPoint
    rw [hterms] at hcomplexPoint
    exact hcomplexPoint
  have hstageFuture : stage <= futureStage := by
    dsimp [futureStage]
    omega
  have hwitnessSeries :
      ((expPowerSeries x).compute stage).lo <= witness /\
        witness <= ((expPowerSeries x).compute stage).hi := by
    dsimp [witness, terms]
    exact expPowerSeries_future_center_mem x hstageFuture
  have hseriesPoint :
      (QBox.point (QComplex.ofRat witness)).NestedIn
        ((ComplexRaw.ofRealRaw (expPowerSeries x)).compute stage) := by
    unfold QBox.point QComplex.ofRat ComplexRaw.ofRealRaw QBox.NestedIn
    simp only [QComplex.le_def]
    exact ⟨⟨hwitnessSeries.1, Rat.le_refl⟩,
      ⟨hwitnessSeries.2, Rat.le_refl⟩⟩
  exact ⟨QComplex.le_trans hcomplexAtStage.1 hseriesPoint.2,
    QComplex.le_trans hseriesPoint.1 hcomplexAtStage.2⟩

/-- Real-coordinate corollary of the real-axis complex exponential bridge. -/
theorem exponentialRawAt_realPart_equiv_expPowerSeries
    (x C : Rat) (hC : 0 <= C) (hx : qabs x <= C) :
    (exponentialRawAt (QComplex.ofRat x) C).realPart.Equiv
      (expPowerSeries x) := by
  have h := ComplexRaw.realPart_equiv
    (exponentialRawAt_equiv_ofRealRaw_expPowerSeries x C hC hx)
  have hembedValid := ComplexRaw.realPart_valid
    (ComplexRaw.ofRealRaw_valid _ (ExpProofs.expPowerSeries_valid x))
  have hembed :
      (ComplexRaw.ofRealRaw (expPowerSeries x)).realPart.Equiv
        (expPowerSeries x) := by
    intro n
    apply (RealRaw.compareAt_overlap_iff _ _ n n).2
    have horder := RealRaw.interval_order_of_valid (expPowerSeries x)
      (ExpProofs.expPowerSeries_valid x) n
    exact ⟨horder, horder⟩
  exact RealRaw.equiv_trans
    (ComplexRaw.realPart_valid
      (exponentialRawAt_valid hC (by
        unfold QComplex.normBound QComplex.ofRat
        rw [show qabs (0 : Rat) = 0 by native_decide, Rat.add_zero]
        exact hx)))
    hembedValid (ExpProofs.expPowerSeries_valid x) h hembed

end ComplexExponentialApproximation
end ComputableAnalysis
