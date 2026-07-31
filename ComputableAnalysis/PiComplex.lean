import ComputableAnalysis.PiProofs

/-!
# The certified imaginary half-pi input

This small bridge turns the project's abstract, multi-presentation pi handle
into the represented complex input `i * pi / 2`.  It is deliberately not an
Euler-identity theorem: the current rotation exponential accepts rational
imaginary inputs only.  The point of this module is to make the already
checked input-side transport explicit, independently of the remaining
represented-input exponential construction.
-/

namespace ComputableAnalysis

namespace PiProofs

namespace pi

/-- The certified complex raw input \(i\pi/2\), formed from the default
circle-area representative of the abstract pi handle. -/
def imaginaryHalf : ComplexRaw :=
  ((1 : Rat) / 2) * ComplexRaw.imaginaryAxis circleArea.raw

theorem imaginaryHalf_valid : imaginaryHalf.Valid := by
  unfold imaginaryHalf
  exact ComplexRaw.scaleRat_valid_of_nonneg (by native_decide)
    (ComplexRaw.imaginaryAxis_valid circleArea.valid)

/-- The `i*pi/2` input formed from any named pi presentation agrees with the
default handle.  This is the representation transport needed before an Euler
route can evaluate a complex exponential at the selected pi value. -/
theorem imaginaryHalf_equiv_presentation (kind : PiPresentation) :
    imaginaryHalf.Equiv
      (((1 : Rat) / 2) * ComplexRaw.imaginaryAxis (presentation kind).raw) := by
  unfold imaginaryHalf
  apply ComplexRaw.scaleRat_equiv_of_nonneg (by native_decide)
  apply ComplexRaw.imaginaryAxis_equiv circleArea.valid (presentation kind).valid
  exact representations_equiv circleArea (presentation kind)

end pi

end PiProofs

end ComputableAnalysis
