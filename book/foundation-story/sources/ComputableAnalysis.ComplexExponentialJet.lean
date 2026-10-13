import ComputableAnalysis.ComplexExponentialLift
import ComputableAnalysis.RepresentedHolomorphicJet
import ComputableAnalysis.RepresentedHolomorphicJetAlgebra

/-!
# Represented first jet of the complex exponential

The derivative certificate is power-series based.  At each moving rational
input center we use the exact polynomial first jet of a finite exponential
prefix.  Its derivative component is retained by the represented exponential,
while its value component differs by one factorial term and is therefore
retained after an explicitly shrinking enlargement.  The coefficient stream
is literally fixed by formal differentiation.
-/

namespace ComputableAnalysis
namespace ComplexExponentialJet

open ComplexExponentialApproximation
open ComplexExponentialLift

/-- The completed value and derivative algorithms for exponential. -/
def representedJet {C : Rat} (A : ComplexExponentialLift.BoundedInput C) :
    RepresentedHolomorphicJet.FirstJet where
  value := A.exponential
  derivative := A.exponential

theorem representedJet_valid
    {C : Rat} (A : ComplexExponentialLift.BoundedInput C) :
    (representedJet A).Valid :=
  ⟨A.exponential_valid, A.exponential_valid⟩

theorem representedJet_selfDerivative
    {C : Rat} (A : ComplexExponentialLift.BoundedInput C) :
    (representedJet A).SelfDerivative :=
  ComplexRaw.equiv_refl A.exponential A.exponential_valid

theorem representedJet_equiv_of_input_equiv
    {C : Rat} (A B : ComplexExponentialLift.BoundedInput C)
    (hAB : A.raw.Equiv B.raw) :
    (representedJet A).Equiv (representedJet B) := by
  have hexp := A.exponential_equiv_of_input_equiv B hAB
  exact ⟨hexp, hexp⟩

/-- Exact finite polynomial first jet at the current rational center. -/
def finiteJetAtStage {C : Rat}
    (A : ComplexExponentialLift.BoundedInput C) (stage : Nat) :
    HolomorphicJet.FirstJet :=
  ComplexExponentialApproximation.finiteJet
    (A.raw.compute stage).center
    (ComplexExponentialLift.BoundedInput.terms C stage)

theorem finiteJetAtStage_derivative
    {C : Rat} (A : ComplexExponentialLift.BoundedInput C) (stage : Nat) :
    (finiteJetAtStage A stage).derivative =
      expPrefix (A.raw.compute stage).center
        (ComplexExponentialLift.BoundedInput.terms C stage) := rfl

theorem finiteJetAtStage_value_eq_derivative_add_term
    {C : Rat} (A : ComplexExponentialLift.BoundedInput C) (stage : Nat) :
    (finiteJetAtStage A stage).value =
      QComplex.add (finiteJetAtStage A stage).derivative
        (term (A.raw.compute stage).center
          (ComplexExponentialLift.BoundedInput.terms C stage)) :=
  ComplexExponentialApproximation.finiteJet_value_eq_derivative_add_term
    (A.raw.compute stage).center
    (ComplexExponentialLift.BoundedInput.terms C stage)

theorem finiteJetAtStage_gap_le
    {C : Rat} (A : ComplexExponentialLift.BoundedInput C) (stage : Nat) :
    QComplex.normBound
        (term (A.raw.compute stage).center
          (ComplexExponentialLift.BoundedInput.terms C stage)) <=
      stageRadius C stage := by
  have hterm := term_normBound_le A.radius_nonneg
    (A.center_normBound stage)
    (ComplexExponentialLift.BoundedInput.terms C stage)
  have htail0 :
      0 <= RationalMajorant.factorialTailTerm C
        (RationalMajorant.factorialTailStart C + stage) :=
    RationalMajorant.factorialTailTerm_nonneg A.radius_nonneg _
  exact Rat.le_trans hterm (by
    unfold ComplexExponentialLift.BoundedInput.terms stageRadius
    grind)

/-- The exact derivative polynomial prefix is contained in the completed
derivative output at the same stage. -/
theorem finiteJetAtStage_derivative_contained
    {C : Rat} (A : ComplexExponentialLift.BoundedInput C) (stage : Nat) :
    (QBox.point (finiteJetAtStage A stage).derivative).NestedIn
      ((representedJet A).derivative.compute stage) := by
  simpa [representedJet,
    ComplexExponentialLift.BoundedInput.candidate,
    finiteJetAtStage_derivative] using
      A.exponential_contains_current_candidate stage

/-- The finite value prefix lies in the completed value box enlarged only by
the one-term derivative gap. -/
theorem finiteJetAtStage_value_contained_expanded
    {C : Rat} (A : ComplexExponentialLift.BoundedInput C) (stage : Nat) :
    (QBox.point (finiteJetAtStage A stage).value).NestedIn
      (QBox.expand ((representedJet A).value.compute stage)
        (stageRadius C stage)) := by
  have hderivative := finiteJetAtStage_derivative_contained A stage
  rw [finiteJetAtStage_value_eq_derivative_add_term]
  exact point_add_error_nested_expand_box
    hderivative.1 hderivative.2 (finiteJetAtStage_gap_le A stage)

/-- The finite value/derivative discrepancy disappears with the executable
factorial radius. -/
theorem finiteJetGap_shrinks
    {C : Rat} (A : ComplexExponentialLift.BoundedInput C) :
    ShrinksToZero (stageRadius C) :=
  stageRadius_shrinks A.radius_nonneg

/-- Complete power-series certificate that the represented exponential is
self-derivative.  This records the exact formal coefficient identity, valid
completed components, finite polynomial jets, their containment, and the
shrinking value/derivative discrepancy. -/
structure Certificate {C : Rat}
    (A : ComplexExponentialLift.BoundedInput C) : Prop where
  valid : (representedJet A).Valid
  selfDerivative : (representedJet A).SelfDerivative
  coefficientDerivative :
    FormalPowerSeries.derivative FormalPowerSeries.expCoeff =
      FormalPowerSeries.expCoeff
  derivativeContained : forall stage,
    (QBox.point (finiteJetAtStage A stage).derivative).NestedIn
      ((representedJet A).derivative.compute stage)
  valueContainedExpanded : forall stage,
    (QBox.point (finiteJetAtStage A stage).value).NestedIn
      (QBox.expand ((representedJet A).value.compute stage)
        (stageRadius C stage))
  gapBound : forall stage,
    QComplex.normBound
        (term (A.raw.compute stage).center
          (ComplexExponentialLift.BoundedInput.terms C stage)) <=
      stageRadius C stage
  gapShrinks : ShrinksToZero (stageRadius C)

theorem certificate
    {C : Rat} (A : ComplexExponentialLift.BoundedInput C) :
    Certificate A where
  valid := representedJet_valid A
  selfDerivative := representedJet_selfDerivative A
  coefficientDerivative := formal_exponential_coefficient_derivative
  derivativeContained := finiteJetAtStage_derivative_contained A
  valueContainedExpanded := finiteJetAtStage_value_contained_expanded A
  gapBound := finiteJetAtStage_gap_le A
  gapShrinks := finiteJetGap_shrinks A

/-! ## Chain-rule composition -/

/-- An inner represented jet together with a bounded representative of its
value at which exponential is evaluated. -/
structure CompositionInput (C : Rat) where
  inner : RepresentedHolomorphicJet.FirstJet
  innerValid : inner.Valid
  exponent : ComplexExponentialLift.BoundedInput C
  exponent_agrees : exponent.raw.Equiv inner.value

/-- The represented chain-rule jet for `exp` after an inner chart. -/
def composedJet {C : Rat} (input : CompositionInput C) :
    RepresentedHolomorphicJet.FirstJet :=
  RepresentedHolomorphicJet.FirstJet.compose
    (representedJet input.exponent) input.inner

theorem composedJet_value {C : Rat} (input : CompositionInput C) :
    (composedJet input).value = input.exponent.exponential := rfl

/-- Literal represented chain rule `(exp after g)' = exp(g) * g'`. -/
theorem composedJet_derivative {C : Rat} (input : CompositionInput C) :
    (composedJet input).derivative =
      ComplexRaw.mul input.exponent.exponential input.inner.derivative := rfl

theorem composedJet_valid {C : Rat} (input : CompositionInput C) :
    (composedJet input).Valid :=
  RepresentedHolomorphicJet.FirstJet.compose_valid
    (representedJet_valid input.exponent) input.innerValid

/-- Two composition packages describing equivalent inner jets give
equivalent exponential chain-rule jets. -/
theorem composedJet_equiv
    {C : Rat} (left right : CompositionInput C)
    (hinner : left.inner.Equiv right.inner) :
    (composedJet left).Equiv (composedJet right) := by
  have hexponentRaw : left.exponent.raw.Equiv right.exponent.raw :=
    ComplexRaw.equiv_trans left.exponent.valid left.innerValid.1
      right.exponent.valid left.exponent_agrees
      (ComplexRaw.equiv_trans left.innerValid.1 right.innerValid.1
        right.exponent.valid hinner.1
        (ComplexRaw.equiv_symm right.exponent_agrees))
  have houter := representedJet_equiv_of_input_equiv
    left.exponent right.exponent hexponentRaw
  exact RepresentedHolomorphicJet.FirstJet.compose_equiv
    (representedJet_valid left.exponent)
    (representedJet_valid right.exponent)
    left.innerValid right.innerValid houter hinner

end ComplexExponentialJet
end ComputableAnalysis
