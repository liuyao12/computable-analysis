import ComputableAnalysis.RepresentedMultivariableHolomorphicJet
import ComputableAnalysis.ComplexExponentialJet
import ComputableAnalysis.ComplexReciprocalJet

/-!
# Scalar analytic functions composed with multivariable represented jets

This module transports the checked reciprocal and exponential scalar jets to
all partial derivatives of a finite-dimensional represented first jet.
-/

namespace ComputableAnalysis
namespace ComplexMultivariableJetComposition

abbrev MultiFirstJet := RepresentedMultivariableHolomorphicJet.FirstJet

/-! ## Reciprocal -/

structure ReciprocalInput (dimension : Nat) (C margin : Rat) where
  inner : MultiFirstJet dimension
  innerValid : inner.Valid
  denominator : ComplexReciprocalLift.AwayInput C margin
  denominator_agrees : denominator.raw.Equiv inner.value

def reciprocalJet {dimension : Nat} {C margin : Rat}
    (input : ReciprocalInput dimension C margin) : MultiFirstJet dimension :=
  RepresentedMultivariableHolomorphicJet.FirstJet.composeScalar
    (ComplexReciprocalJet.representedJet input.denominator) input.inner

theorem reciprocalJet_value {dimension : Nat} {C margin : Rat}
    (input : ReciprocalInput dimension C margin) :
    (reciprocalJet input).value = input.denominator.reciprocal := rfl

/-- Every partial satisfies `partial_i (1/g) = -(1/g)^2 partial_i g`. -/
theorem reciprocalJet_gradient {dimension : Nat} {C margin : Rat}
    (input : ReciprocalInput dimension C margin) (i : Fin dimension) :
    (reciprocalJet input).gradient i = ComplexRaw.mul
      (ComplexRaw.neg (ComplexRaw.mul input.denominator.reciprocal
        input.denominator.reciprocal)) (input.inner.gradient i) := rfl

theorem reciprocalJet_valid {dimension : Nat} {C margin : Rat}
    (input : ReciprocalInput dimension C margin) :
    (reciprocalJet input).Valid :=
  RepresentedMultivariableHolomorphicJet.FirstJet.composeScalar_valid
    (ComplexReciprocalJet.representedJet_valid input.denominator)
    input.innerValid

theorem reciprocalJet_equiv {dimension : Nat} {C margin : Rat}
    (left right : ReciprocalInput dimension C margin)
    (hinner : left.inner.Equiv right.inner) :
    (reciprocalJet left).Equiv (reciprocalJet right) := by
  have hdenominator : left.denominator.raw.Equiv right.denominator.raw :=
    ComplexRaw.equiv_trans left.denominator.valid left.innerValid.1
      right.denominator.valid left.denominator_agrees
      (ComplexRaw.equiv_trans left.innerValid.1 right.innerValid.1
        right.denominator.valid hinner.1
        (ComplexRaw.equiv_symm right.denominator_agrees))
  have houter := ComplexReciprocalJet.representedJet_equiv_of_input_equiv
    left.denominator right.denominator hdenominator
  exact RepresentedMultivariableHolomorphicJet.FirstJet.composeScalar_equiv
    (ComplexReciprocalJet.representedJet_valid left.denominator)
    (ComplexReciprocalJet.representedJet_valid right.denominator)
    left.innerValid right.innerValid houter hinner

/-! ## Exponential -/

structure ExponentialInput (dimension : Nat) (C : Rat) where
  inner : MultiFirstJet dimension
  innerValid : inner.Valid
  exponent : ComplexExponentialLift.BoundedInput C
  exponent_agrees : exponent.raw.Equiv inner.value

def exponentialJet {dimension : Nat} {C : Rat}
    (input : ExponentialInput dimension C) : MultiFirstJet dimension :=
  RepresentedMultivariableHolomorphicJet.FirstJet.composeScalar
    (ComplexExponentialJet.representedJet input.exponent) input.inner

theorem exponentialJet_value {dimension : Nat} {C : Rat}
    (input : ExponentialInput dimension C) :
    (exponentialJet input).value = input.exponent.exponential := rfl

/-- Every partial satisfies `partial_i exp(g) = exp(g) partial_i g`. -/
theorem exponentialJet_gradient {dimension : Nat} {C : Rat}
    (input : ExponentialInput dimension C) (i : Fin dimension) :
    (exponentialJet input).gradient i =
      ComplexRaw.mul input.exponent.exponential (input.inner.gradient i) := rfl

theorem exponentialJet_valid {dimension : Nat} {C : Rat}
    (input : ExponentialInput dimension C) :
    (exponentialJet input).Valid :=
  RepresentedMultivariableHolomorphicJet.FirstJet.composeScalar_valid
    (ComplexExponentialJet.representedJet_valid input.exponent)
    input.innerValid

theorem exponentialJet_equiv {dimension : Nat} {C : Rat}
    (left right : ExponentialInput dimension C)
    (hinner : left.inner.Equiv right.inner) :
    (exponentialJet left).Equiv (exponentialJet right) := by
  have hexponent : left.exponent.raw.Equiv right.exponent.raw :=
    ComplexRaw.equiv_trans left.exponent.valid left.innerValid.1
      right.exponent.valid left.exponent_agrees
      (ComplexRaw.equiv_trans left.innerValid.1 right.innerValid.1
        right.exponent.valid hinner.1
        (ComplexRaw.equiv_symm right.exponent_agrees))
  have houter := ComplexExponentialJet.representedJet_equiv_of_input_equiv
    left.exponent right.exponent hexponent
  exact RepresentedMultivariableHolomorphicJet.FirstJet.composeScalar_equiv
    (ComplexExponentialJet.representedJet_valid left.exponent)
    (ComplexExponentialJet.representedJet_valid right.exponent)
    left.innerValid right.innerValid houter hinner

end ComplexMultivariableJetComposition
end ComputableAnalysis
