import ComputableAnalysis.ComplexReciprocalLift
import ComputableAnalysis.RepresentedHolomorphicJetAlgebra

/-!
# Represented first jet of reciprocal away from zero

The completed derivative is `-r*r`, where `r` is the stabilized reciprocal.
Finite rational inverse values and their exact derivatives are enclosed at
every stage, while the reciprocal lift supplies the quantitative continuity
certificate and representative invariance.
-/

namespace ComputableAnalysis
namespace ComplexReciprocalJet

open ComplexReciprocalLift

def representedJet {C margin : Rat}
    (A : ComplexReciprocalLift.AwayInput C margin) :
    RepresentedHolomorphicJet.FirstJet where
  value := A.reciprocal
  derivative := ComplexRaw.neg
    (ComplexRaw.mul A.reciprocal A.reciprocal)

theorem representedJet_derivative {C margin : Rat}
    (A : ComplexReciprocalLift.AwayInput C margin) :
    (representedJet A).derivative = ComplexRaw.neg
      (ComplexRaw.mul A.reciprocal A.reciprocal) := rfl

theorem representedJet_valid {C margin : Rat}
    (A : ComplexReciprocalLift.AwayInput C margin) :
    (representedJet A).Valid := by
  constructor
  · exact A.reciprocal_valid
  · exact ComplexRaw.neg_valid
      (ComplexRaw.mul_valid A.reciprocal_valid A.reciprocal_valid)

theorem representedJet_equiv_of_input_equiv
    {C margin : Rat} (A B : ComplexReciprocalLift.AwayInput C margin)
    (hAB : A.raw.Equiv B.raw) :
    (representedJet A).Equiv (representedJet B) := by
  have hrecip := A.reciprocal_equiv_of_input_equiv B hAB
  constructor
  · exact hrecip
  · apply ComplexRaw.neg_equiv
    exact ComplexRaw.mul_equiv
      A.reciprocal_valid B.reciprocal_valid
      A.reciprocal_valid B.reciprocal_valid hrecip hrecip

/-- Exact rational first jet of reciprocal at the sampled center. -/
def finiteJetAtStage {C margin : Rat}
    (A : ComplexReciprocalLift.AwayInput C margin) (stage : Nat) :
    HolomorphicJet.FirstJet :=
  let inverse := QComplex.inverse (A.raw.compute stage).center
  { value := inverse
    derivative := QComplex.neg (QComplex.mul inverse inverse) }

theorem finiteJetAtStage_value_contained
    {C margin : Rat} (A : ComplexReciprocalLift.AwayInput C margin)
    (stage : Nat) :
    (QBox.point (finiteJetAtStage A stage).value).NestedIn
      ((representedJet A).value.compute stage) := by
  simpa [finiteJetAtStage, representedJet,
    ComplexReciprocalLift.AwayInput.candidate] using
      A.reciprocal_contains_current_candidate stage

theorem finiteJetAtStage_derivative_contained
    {C margin : Rat} (A : ComplexReciprocalLift.AwayInput C margin)
    (stage : Nat) :
    (QBox.point (finiteJetAtStage A stage).derivative).NestedIn
      ((representedJet A).derivative.compute stage) := by
  let inverse := QComplex.inverse (A.raw.compute stage).center
  have hinverse := finiteJetAtStage_value_contained A stage
  have hproduct :
      (QBox.point (QComplex.mul inverse inverse)).NestedIn
        ((ComplexRaw.mul A.reciprocal A.reciprocal).compute stage) := by
    change (QBox.point (QComplex.mul inverse inverse)).NestedIn
      (QBox.mul (A.reciprocal.compute stage) (A.reciprocal.compute stage))
    exact QBox.mul_contains hinverse.1 hinverse.2 hinverse.1 hinverse.2
  change (QBox.point (QComplex.neg (QComplex.mul inverse inverse))).NestedIn
    (QBox.neg
      ((ComplexRaw.mul A.reciprocal A.reciprocal).compute stage))
  unfold QBox.NestedIn QBox.point QBox.neg
  simp only [QComplex.le_def, QComplex.neg]
  unfold QBox.NestedIn QBox.point at hproduct
  simp only [QComplex.le_def] at hproduct
  exact ⟨
    ⟨Rat.neg_le_neg hproduct.2.1, Rat.neg_le_neg hproduct.2.2⟩,
    ⟨Rat.neg_le_neg hproduct.1.1, Rat.neg_le_neg hproduct.1.2⟩⟩

/-- Packaged reciprocal derivative certificate.  The exact finite derivative
formula is enclosed by the completed derivative at every stage, and the value
algorithm is the representative-invariant quantitative reciprocal lift. -/
structure Certificate {C margin : Rat}
    (A : ComplexReciprocalLift.AwayInput C margin) : Prop where
  valid : (representedJet A).Valid
  derivativeFormula : (representedJet A).derivative = ComplexRaw.neg
    (ComplexRaw.mul A.reciprocal A.reciprocal)
  valueContained : forall stage,
    (QBox.point (finiteJetAtStage A stage).value).NestedIn
      ((representedJet A).value.compute stage)
  derivativeContained : forall stage,
    (QBox.point (finiteJetAtStage A stage).derivative).NestedIn
      ((representedJet A).derivative.compute stage)

theorem certificate {C margin : Rat}
    (A : ComplexReciprocalLift.AwayInput C margin) : Certificate A where
  valid := representedJet_valid A
  derivativeFormula := representedJet_derivative A
  valueContained := finiteJetAtStage_value_contained A
  derivativeContained := finiteJetAtStage_derivative_contained A

/-! ## Chain-rule composition -/

structure CompositionInput (C margin : Rat) where
  inner : RepresentedHolomorphicJet.FirstJet
  innerValid : inner.Valid
  denominator : ComplexReciprocalLift.AwayInput C margin
  denominator_agrees : denominator.raw.Equiv inner.value

def composedJet {C margin : Rat} (input : CompositionInput C margin) :
    RepresentedHolomorphicJet.FirstJet :=
  RepresentedHolomorphicJet.FirstJet.compose
    (representedJet input.denominator) input.inner

theorem composedJet_value {C margin : Rat}
    (input : CompositionInput C margin) :
    (composedJet input).value = input.denominator.reciprocal := rfl

/-- Literal represented reciprocal chain rule
`(1/g)' = -(1/g)^2 * g'`. -/
theorem composedJet_derivative {C margin : Rat}
    (input : CompositionInput C margin) :
    (composedJet input).derivative = ComplexRaw.mul
      (ComplexRaw.neg (ComplexRaw.mul input.denominator.reciprocal
        input.denominator.reciprocal)) input.inner.derivative := rfl

theorem composedJet_valid {C margin : Rat}
    (input : CompositionInput C margin) : (composedJet input).Valid :=
  RepresentedHolomorphicJet.FirstJet.compose_valid
    (representedJet_valid input.denominator) input.innerValid

theorem composedJet_equiv
    {C margin : Rat} (left right : CompositionInput C margin)
    (hinner : left.inner.Equiv right.inner) :
    (composedJet left).Equiv (composedJet right) := by
  have hdenominator : left.denominator.raw.Equiv right.denominator.raw :=
    ComplexRaw.equiv_trans left.denominator.valid left.innerValid.1
      right.denominator.valid left.denominator_agrees
      (ComplexRaw.equiv_trans left.innerValid.1 right.innerValid.1
        right.denominator.valid hinner.1
        (ComplexRaw.equiv_symm right.denominator_agrees))
  have houter := representedJet_equiv_of_input_equiv
    left.denominator right.denominator hdenominator
  exact RepresentedHolomorphicJet.FirstJet.compose_equiv
    (representedJet_valid left.denominator)
    (representedJet_valid right.denominator)
    left.innerValid right.innerValid houter hinner

end ComplexReciprocalJet
end ComputableAnalysis
