import ComputableAnalysis.ElementarySeriesComparisons
import ComputableAnalysis.ElementaryInverseBranches
import ComputableAnalysis.ExponentialComputations.RationalAgreement

/-! A concrete test of the function-computation identity skill. The primary
functions retain their rational coordinates. The existing represented-angle
operation is identified with the real-axis power-series sine using finite
prefix agreement and the quantitative exponential extension bridge.
No identity theorem or ODE uniqueness premise is used. -/
namespace ComputableAnalysis.ElementarySineComparison
open ComplexRaw RiemannHilbert FunctionTheory ModularForms ElementaryInverseBranches
set_option maxHeartbeats 1000000

private theorem imaginaryAxis_rational (x : Rat) :
    (imaginaryAxis (RealRaw.ofRat x)).Equiv (ofQComplex ⟨0,x⟩) := by
  intro n
  apply (compareAt_overlap_iff _ _ n n).mpr
  rw [imaginaryAxis_compute]
  exact ⟨QComplex.le_refl _,QComplex.le_refl _⟩

/-- The derived angle evaluator agrees with the primary power-series sine
at every rational radian input. Its convergence and representation invariance
are supplied by the existing exponential construction, not assumed here. -/
theorem powerSeries_rational_agrees_derived (x : Rat) :
    (ElementaryPowerSeries.sineValue ⟨x,0⟩).realPart.Equiv
      (sineAtAngle (RealRaw.ofRat x) (RealRaw.ofRat_valid x)) := by
  let a : Scalar := ⟨imaginaryAxis (RealRaw.ofRat x),
    imaginaryAxis_valid (RealRaw.ofRat_valid x)⟩
  let b : Scalar := ⟨ofQComplex ⟨0,x⟩,ofQComplex_valid _⟩
  have he : (entireExponentialValue a).val.Equiv
      (ElementaryRational.exponentialValue ⟨0,x⟩) :=
    equiv_trans (entireExponentialValue a).property
      (entireExponentialValue b).property (ElementaryRational.exponentialValue_valid _)
      (entireExponentialValue_congr a b (imaginaryAxis_rational x))
      (ExponentialComputations.Rational.rational_powerSeries_agrees ⟨0,x⟩)
  exact RealRaw.equiv_trans
    (realPart_valid (ElementaryPowerSeries.sineValue_valid _))
    (imagPart_valid (ElementaryRational.exponentialValue_valid _))
    (sineAtAngle_valid _ _)
    (ElementaryPowerSeries.sineValue_realAxis_agrees x)
    (RealRaw.equiv_symm (imagPart_equiv he))

/-- Every normalized rational input agrees with the derived power-series
evaluation at its actual angle, which need not be rational. -/
theorem sinPi_agrees_derived_powerSeries (r : Rat) :
    (ElementaryRational.sinPi.evalRaw r trivial).Equiv
      (sineAtAngle (ElementaryRational.piAngle r) (ElementaryRational.piAngle_valid r)) :=
  ExponentialComputations.Rational.rational_sinPi_agrees_derived r

/-- Primary functions with different coordinate maps agree wherever their
physical input points agree. No density of that overlap is asserted. -/
theorem sinPi_powerSeries_agrees_at_coordinates :
    ElementaryRational.sinPi.AgreeAtCoordinates
      ElementaryPowerSeries.sine.realPartOnRealAxis
      ElementaryRational.piAngle RealRaw.ofRat := by
  intro r x _ _ h
  change (ElementaryRational.sinPi.evalRaw r trivial).Equiv
    (ElementaryPowerSeries.sineValue ⟨x,0⟩).realPart
  exact RealRaw.equiv_trans (ElementaryRational.sinPi_valid r trivial)
    (ElementaryRational.sineRadianRotation_valid x trivial)
    (realPart_valid (ElementaryPowerSeries.sineValue_valid ⟨x,0⟩))
    (ExponentialComputations.Rational.sinPi_radian_agrees_on_chart_overlap r x trivial trivial h)
    (RealRaw.equiv_symm (ElementaryPowerSeries.sineValue_realAxis_agrees x))

end ComputableAnalysis.ElementarySineComparison
