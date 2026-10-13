import ComputableAnalysis.ComplexMultivariableJetComposition

/-!
# Certified nonzero square-root branches

This module is the branch-safe implicit-function layer for square root.  It
does not pretend that a square root of an arbitrary represented input can be
selected automatically.  Instead, the input supplies a represented nonzero
root and the checked equation `root * root ≈ inner.value`.  The resulting
gradient is the implicit derivative `inner_i / (2 * root)`.
-/

namespace ComputableAnalysis
namespace ComplexSquareRootJet

abbrev MultiFirstJet := RepresentedMultivariableHolomorphicJet.FirstJet

/-- A selected nonzero square-root branch over a multivariable inner jet. -/
structure Input (dimension : Nat) (rootBound rootMargin : Rat) where
  inner : MultiFirstJet dimension
  innerValid : inner.Valid
  root : ComplexReciprocalLift.AwayInput rootBound rootMargin
  square_agrees :
    (ComplexRaw.mul root.raw root.raw).Equiv inner.value

/-- The represented value and all partials of the selected square-root
branch. -/
def representedJet {dimension : Nat} {rootBound rootMargin : Rat}
    (input : Input dimension rootBound rootMargin) : MultiFirstJet dimension where
  value := input.root.raw
  gradient := fun i => ComplexRaw.scaleRat (1 / 2 : Rat)
    (ComplexRaw.mul input.root.reciprocal (input.inner.gradient i))

theorem representedJet_value {dimension : Nat} {rootBound rootMargin : Rat}
    (input : Input dimension rootBound rootMargin) :
    (representedJet input).value = input.root.raw := rfl

/-- Literal implicit derivative `partial_i sqrt(g) = partial_i g/(2*sqrt(g))`. -/
theorem representedJet_gradient
    {dimension : Nat} {rootBound rootMargin : Rat}
    (input : Input dimension rootBound rootMargin) (i : Fin dimension) :
    (representedJet input).gradient i =
      ComplexRaw.scaleRat (1 / 2 : Rat)
        (ComplexRaw.mul input.root.reciprocal
          (input.inner.gradient i)) := rfl

theorem representedJet_valid
    {dimension : Nat} {rootBound rootMargin : Rat}
    (input : Input dimension rootBound rootMargin) :
    (representedJet input).Valid := by
  constructor
  · exact input.root.valid
  · intro i
    exact ComplexRaw.scaleRat_valid
      (ComplexRaw.mul_valid input.root.reciprocal_valid
        (input.innerValid.2 i))

/-- The selected value still carries the defining square-root equation. -/
theorem representedJet_square_equiv_inner
    {dimension : Nat} {rootBound rootMargin : Rat}
    (input : Input dimension rootBound rootMargin) :
    (ComplexRaw.mul (representedJet input).value
      (representedJet input).value).Equiv input.inner.value :=
  input.square_agrees

/-- A packaged algebraic/implicit derivative certificate.  Analytic branch
construction on a concrete domain must additionally provide the `Input`. -/
structure Certificate
    {dimension : Nat} {rootBound rootMargin : Rat}
    (input : Input dimension rootBound rootMargin) : Prop where
  valid : (representedJet input).Valid
  squareEquation :
    (ComplexRaw.mul (representedJet input).value
      (representedJet input).value).Equiv input.inner.value
  gradientFormula : forall i,
    (representedJet input).gradient i =
      ComplexRaw.scaleRat (1 / 2 : Rat)
        (ComplexRaw.mul input.root.reciprocal
          (input.inner.gradient i))

theorem certificate
    {dimension : Nat} {rootBound rootMargin : Rat}
    (input : Input dimension rootBound rootMargin) : Certificate input where
  valid := representedJet_valid input
  squareEquation := representedJet_square_equiv_inner input
  gradientFormula := representedJet_gradient input

/-- Equivalent selected roots and equivalent inner gradients produce
equivalent square-root jets.  Root equivalence is explicit because the square
equation alone cannot distinguish the two signs. -/
theorem representedJet_equiv
    {dimension : Nat} {rootBound rootMargin : Rat}
    (left right : Input dimension rootBound rootMargin)
    (hinner : left.inner.Equiv right.inner)
    (hroot : left.root.raw.Equiv right.root.raw) :
    (representedJet left).Equiv (representedJet right) := by
  have hreciprocal := left.root.reciprocal_equiv_of_input_equiv
    right.root hroot
  constructor
  · exact hroot
  · intro i
    apply ComplexRaw.scaleRat_equiv
    exact ComplexRaw.mul_equiv
      left.root.reciprocal_valid right.root.reciprocal_valid
      (left.innerValid.2 i) (right.innerValid.2 i)
      hreciprocal (hinner.2 i)

end ComplexSquareRootJet
end ComputableAnalysis
