import ComputableAnalysis.ComplexSquareRootJet
import ComputableAnalysis.RepresentedPositiveSquareRoot

/-!
# Positive represented square-root jets

This module joins the numerical positive-real square-root construction to the
implicit multivariable square-root jet.  The numerical layer supplies the
root, its nonzero reciprocal certificate, and the represented square equation;
the only remaining input is agreement between the real radicand and the value
component of the multivariable inner jet.
-/

namespace ComputableAnalysis
namespace PositiveSquareRootJet

abbrev MultiFirstJet := RepresentedMultivariableHolomorphicJet.FirstJet
abbrev PositiveInput := RepresentedPositiveSquareRoot.PositiveInput

/-- A positive represented-real radicand identified with the value component
of a represented multivariable jet. -/
structure Input (dimension bound : Nat) (margin : Rat) where
  positive : PositiveInput bound margin
  inner : MultiFirstJet dimension
  innerValid : inner.Valid
  value_agrees :
    (ComplexRaw.ofRealRaw positive.raw).Equiv inner.value

namespace Input

def toSquareRootInput
    {dimension bound : Nat} {margin : Rat}
    (input : Input dimension bound margin) :
    ComplexSquareRootJet.Input dimension
      (RepresentedPositiveSquareRoot.PositiveInput.rootBound bound)
      (RepresentedPositiveSquareRoot.PositiveInput.awayRootMargin margin) where
  inner := input.inner
  innerValid := input.innerValid
  root := RepresentedPositiveSquareRoot.PositiveInput.awayInput input.positive
  square_agrees := by
    exact ComplexRaw.equiv_trans
      (ComplexRaw.mul_valid
        (RepresentedPositiveSquareRoot.PositiveInput.awayRootRaw_valid
          input.positive)
        (RepresentedPositiveSquareRoot.PositiveInput.awayRootRaw_valid
          input.positive))
      (ComplexRaw.ofRealRaw_valid input.positive.raw input.positive.valid)
      input.innerValid.1
      (RepresentedPositiveSquareRoot.PositiveInput.awayRootRaw_square_equiv_raw
        input.positive)
      input.value_agrees

/-- The automatically selected positive square-root jet. -/
def representedJet
    {dimension bound : Nat} {margin : Rat}
    (input : Input dimension bound margin) : MultiFirstJet dimension :=
  ComplexSquareRootJet.representedJet input.toSquareRootInput

theorem representedJet_valid
    {dimension bound : Nat} {margin : Rat}
    (input : Input dimension bound margin) :
    input.representedJet.Valid :=
  ComplexSquareRootJet.representedJet_valid input.toSquareRootInput

theorem representedJet_value
    {dimension bound : Nat} {margin : Rat}
    (input : Input dimension bound margin) :
    input.representedJet.value =
      RepresentedPositiveSquareRoot.PositiveInput.awayRootRaw input.positive :=
  rfl

theorem representedJet_square_equiv_inner
    {dimension bound : Nat} {margin : Rat}
    (input : Input dimension bound margin) :
    (ComplexRaw.mul input.representedJet.value input.representedJet.value).Equiv
      input.inner.value :=
  ComplexSquareRootJet.representedJet_square_equiv_inner
    input.toSquareRootInput

theorem representedJet_gradient
    {dimension bound : Nat} {margin : Rat}
    (input : Input dimension bound margin) (i : Fin dimension) :
    input.representedJet.gradient i =
      ComplexRaw.scaleRat (1 / 2 : Rat)
        (ComplexRaw.mul input.toSquareRootInput.root.reciprocal
          (input.inner.gradient i)) :=
  rfl

end Input
end PositiveSquareRootJet
end ComputableAnalysis
