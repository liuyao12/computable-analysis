import ComputableAnalysis.ComplexMultiplication
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

/-- The exact rational complex scalar `i/2`.  Applying it through
`ComplexRaw.qcomplexLeftMul` is the algebraic presentation of the same
represented input as `imaginaryHalf`. -/
def imaginaryHalfScalar : QComplex := { re := 0, im := (1 : Rat) / 2 }

theorem imaginaryHalf_valid : imaginaryHalf.Valid := by
  unfold imaginaryHalf
  exact ComplexRaw.scaleRat_valid_of_nonneg (by native_decide)
    (ComplexRaw.imaginaryAxis_valid circleArea.valid)

/-- The coordinate construction of `i*pi/2` agrees stage by stage with
literal multiplication of the preferred pi representative by the exact
rational complex scalar (i/2). -/
theorem imaginaryHalf_compute_eq_qcomplexLeftMul :
    imaginaryHalf.compute =
      (ComplexRaw.qcomplexLeftMul imaginaryHalfScalar
        (ComplexRaw.ofRealRaw circleArea.raw)).compute := by
  funext n
  change QBox.scaleRat ((1 : Rat) / 2)
      { lo := { re := 0, im := (circleArea.raw.compute n).lo },
        hi := { re := 0, im := (circleArea.raw.compute n).hi } } =
    QBox.add (QBox.scaleRat 0 (QBox.ofRealInterval (circleArea.raw.compute n)))
      (QBox.scaleRat ((1 : Rat) / 2)
        { lo := { re := -(QBox.ofRealInterval (circleArea.raw.compute n)).hi.im,
                  im := (QBox.ofRealInterval (circleArea.raw.compute n)).lo.re },
          hi := { re := -(QBox.ofRealInterval (circleArea.raw.compute n)).lo.im,
                  im := (QBox.ofRealInterval (circleArea.raw.compute n)).hi.re } })
  have h0 : (0 : Rat) <= 0 := by native_decide
  have hhalf : (0 : Rat) <= (1 : Rat) / 2 := by native_decide
  simp only [QBox.scaleRat, QBox.add, QBox.ofRealInterval, if_pos h0,
    if_pos hhalf, Rat.zero_mul, Rat.neg_zero]
  congr 1 <;> congr 1 <;> exact (Rat.zero_add _).symm

/-- The literal `i/2` action on pi is itself a valid complex raw. -/
theorem imaginaryHalf_qcomplexLeftMul_valid :
    (ComplexRaw.qcomplexLeftMul imaginaryHalfScalar
      (ComplexRaw.ofRealRaw circleArea.raw)).Valid :=
  ComplexRaw.qcomplexLeftMul_valid imaginaryHalfScalar
    (ComplexRaw.ofRealRaw_valid circleArea.raw circleArea.valid)

/-- The two presentations of `i*pi/2` are equivalent.  This makes the
Euler route use the same exact complex-scalar operation as later formulas
such as `-2*i*log(i)`, without claiming that the complex exponential is
already defined on this represented input. -/
theorem imaginaryHalf_equiv_qcomplexLeftMul :
    imaginaryHalf.Equiv
      (ComplexRaw.qcomplexLeftMul imaginaryHalfScalar
        (ComplexRaw.ofRealRaw circleArea.raw)) := by
  intro n
  apply (ComplexRaw.compareAt_overlap_iff imaginaryHalf
    (ComplexRaw.qcomplexLeftMul imaginaryHalfScalar
      (ComplexRaw.ofRealRaw circleArea.raw)) n n).2
  rw [imaginaryHalf_compute_eq_qcomplexLeftMul]
  have hordered :=
    ComplexRaw.valid_ordered imaginaryHalf_qcomplexLeftMul_valid n
  exact ⟨hordered, hordered⟩

/-- Exact `i/2`-scalar multiplication transports every named pi
presentation to the same represented complex input. -/
theorem imaginaryHalf_qcomplexLeftMul_equiv_presentation
    (kind : PiPresentation) :
    (ComplexRaw.qcomplexLeftMul imaginaryHalfScalar
      (ComplexRaw.ofRealRaw circleArea.raw)).Equiv
      (ComplexRaw.qcomplexLeftMul imaginaryHalfScalar
        (ComplexRaw.ofRealRaw (presentation kind).raw)) := by
  apply ComplexRaw.qcomplexLeftMul_equiv
  apply ComplexRaw.ofRealRaw_equiv_of_equiv circleArea.valid
    (presentation kind).valid
  exact representations_equiv circleArea (presentation kind)

/-- The exact scalar `-2i`, used in the complex-logarithm presentation of pi. -/
def negativeTwoImaginaryScalar : QComplex := { re := 0, im := -2 }

/-- The exact rational raw complex number (-2i), retained separately from
the affine scalar so that the Euler/logarithm route can use ordinary certified
complex multiplication. -/
def negativeTwoImaginaryRaw : ComplexRaw :=
  ComplexRaw.ofQComplex negativeTwoImaginaryScalar

theorem negativeTwoImaginaryRaw_valid : negativeTwoImaginaryRaw.Valid :=
  ComplexRaw.ofQComplex_valid negativeTwoImaginaryScalar

/-- The finite rational box calculation

\[
 (-2i)(i\pi/2)=\pi
\]

is exact at every stage of the selected pi representative. -/
theorem negativeTwoImaginaryScalar_imaginaryHalf_compute :
    (ComplexRaw.qcomplexLeftMul negativeTwoImaginaryScalar imaginaryHalf).compute =
      (ComplexRaw.ofRealRaw circleArea.raw).compute := by
  funext n
  change QBox.add
      (QBox.scaleRat 0
        (QBox.scaleRat ((1 : Rat) / 2)
          { lo := { re := 0, im := (circleArea.raw.compute n).lo },
            hi := { re := 0, im := (circleArea.raw.compute n).hi } }))
      (QBox.scaleRat (-2)
        { lo := { re := -(QBox.scaleRat ((1 : Rat) / 2)
                    { lo := { re := 0, im := (circleArea.raw.compute n).lo },
                      hi := { re := 0, im := (circleArea.raw.compute n).hi } }).hi.im,
                  im := (QBox.scaleRat ((1 : Rat) / 2)
                    { lo := { re := 0, im := (circleArea.raw.compute n).lo },
                      hi := { re := 0, im := (circleArea.raw.compute n).hi } }).lo.re },
          hi := { re := -(QBox.scaleRat ((1 : Rat) / 2)
                    { lo := { re := 0, im := (circleArea.raw.compute n).lo },
                      hi := { re := 0, im := (circleArea.raw.compute n).hi } }).lo.im,
                  im := (QBox.scaleRat ((1 : Rat) / 2)
                    { lo := { re := 0, im := (circleArea.raw.compute n).lo },
                      hi := { re := 0, im := (circleArea.raw.compute n).hi } }).hi.re } }) =
    QBox.ofRealInterval (circleArea.raw.compute n)
  have h0 : (0 : Rat) <= 0 := by native_decide
  have hhalf : (0 : Rat) <= (1 : Rat) / 2 := by native_decide
  have hminusTwo : ¬ (0 : Rat) <= -2 := by native_decide
  have htwo : (2 : Rat) * (2 : Rat)⁻¹ = 1 := by
    exact Rat.mul_inv_cancel 2 (Rat.ne_of_gt (by native_decide))
  have hscale (q : Rat) : (-2 : Rat) * -(((1 : Rat) / 2) * q) = q := by
    rw [Rat.div_def]
    simp only [Rat.one_mul]
    calc
      (-2 : Rat) * -(2⁻¹ * q) = 2 * (2⁻¹ * q) := by
        grind [Rat.neg_mul, Rat.mul_neg]
      _ = (2 * 2⁻¹) * q := by rw [Rat.mul_assoc]
      _ = q := by rw [htwo, Rat.one_mul]
  simp only [QBox.scaleRat, QBox.add, QBox.ofRealInterval, QComplex.add,
    if_pos h0, if_pos hhalf, if_neg hminusTwo, Rat.zero_mul]
  congr 1 <;> congr 1
  all_goals try rw [hscale]
  all_goals grind

/-- The exact scalar conversion from the certified `i*pi/2` input back to
the real-axis preferred pi representative. -/
theorem negativeTwoImaginaryScalar_imaginaryHalf_equiv_piCircleArea :
    (ComplexRaw.qcomplexLeftMul negativeTwoImaginaryScalar imaginaryHalf).Equiv
      (ComplexRaw.ofRealRaw circleArea.raw) := by
  intro n
  apply (ComplexRaw.compareAt_overlap_iff
    (ComplexRaw.qcomplexLeftMul negativeTwoImaginaryScalar imaginaryHalf)
    (ComplexRaw.ofRealRaw circleArea.raw) n n).2
  rw [negativeTwoImaginaryScalar_imaginaryHalf_compute]
  have hordered := ComplexRaw.valid_ordered
    (ComplexRaw.ofRealRaw_valid circleArea.raw circleArea.valid) n
  exact ⟨hordered, hordered⟩

/-- The same return leg is now also a theorem of ordinary certified complex
multiplication, rather than only of the exact affine scalar shortcut:

\[
  (-2i)(i\pi/2)=\pi.
\]

The general product is first bridged to the affine evaluator using its common
rational center witness; no completed complex field is introduced. -/
theorem negativeTwoImaginaryRaw_mul_imaginaryHalf_equiv_piCircleArea :
    (negativeTwoImaginaryRaw * imaginaryHalf).Equiv
      (ComplexRaw.ofRealRaw circleArea.raw) := by
  have hproductToAffine :
      (negativeTwoImaginaryRaw * imaginaryHalf).Equiv
        (ComplexRaw.qcomplexLeftMul negativeTwoImaginaryScalar imaginaryHalf) := by
    simpa [negativeTwoImaginaryRaw] using
      ComplexRaw.equiv_symm
        (ComplexRaw.qcomplexLeftMul_equiv_mul_ofQComplex
          negativeTwoImaginaryScalar imaginaryHalf_valid)
  exact ComplexRaw.equiv_trans
    (ComplexRaw.mul_valid negativeTwoImaginaryRaw_valid imaginaryHalf_valid)
    (ComplexRaw.qcomplexLeftMul_valid negativeTwoImaginaryScalar imaginaryHalf_valid)
    (ComplexRaw.ofRealRaw_valid circleArea.raw circleArea.valid)
    hproductToAffine
    negativeTwoImaginaryScalar_imaginaryHalf_equiv_piCircleArea

/-- The remaining branch-specific input for the complex-logarithm pi route.
This package does not construct a logarithm: a series, path, or inverse-exp
branch must separately supply its valid raw evaluator and its agreement with
the certified `i*pi/2` input. -/
structure LogAtICertificate where
  raw : ComplexRaw
  valid : raw.Valid
  agreesWithImaginaryHalf : raw.Equiv imaginaryHalf

/-- Once a complex logarithm branch at `i` has been certified to equal
`i*pi/2`, the formula `-2*i*log(i)=pi` follows using only the checked
exact affine scalar action. -/
theorem negativeTwoImaginary_logAtI_equiv_piCircleArea
    (logI : LogAtICertificate) :
    (ComplexRaw.qcomplexLeftMul negativeTwoImaginaryScalar logI.raw).Equiv
      (ComplexRaw.ofRealRaw circleArea.raw) := by
  exact ComplexRaw.equiv_trans
    (ComplexRaw.qcomplexLeftMul_valid negativeTwoImaginaryScalar logI.valid)
    (ComplexRaw.qcomplexLeftMul_valid negativeTwoImaginaryScalar
      imaginaryHalf_valid)
    (ComplexRaw.ofRealRaw_valid circleArea.raw circleArea.valid)
    (ComplexRaw.qcomplexLeftMul_equiv negativeTwoImaginaryScalar
      logI.agreesWithImaginaryHalf)
    negativeTwoImaginaryScalar_imaginaryHalf_equiv_piCircleArea

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
