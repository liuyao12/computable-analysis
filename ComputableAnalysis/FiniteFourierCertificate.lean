import ComputableAnalysis.RotationSeries

/-!
# A finite Fourier orthogonality certificate

Fourier analysis is represented at the project's constructive boundary by a
finite root-of-unity transform.  The four rational quarter-turn roots give
exact cancellation for the first two nonzero modes; no infinite Fourier
limit or completeness theorem is asserted.
-/

namespace ComputableAnalysis

def fourPointFourierSum (mode : Nat) : QComplex :=
  QComplex.add
    (QComplex.add
      (QComplex.add
        (QComplex.natPow RotationSeries.imaginaryUnit (mode * 0))
        (QComplex.natPow RotationSeries.imaginaryUnit (mode * 1)))
      (QComplex.natPow RotationSeries.imaginaryUnit (mode * 2)))
    (QComplex.natPow RotationSeries.imaginaryUnit (mode * 3))

theorem fourPointFourierSum_zero_mode :
    fourPointFourierSum 0 = { re := 4, im := 0 } := by
  native_decide

theorem fourPointFourierSum_first_mode :
    fourPointFourierSum 1 = QComplex.zero := by
  native_decide

theorem fourPointFourierSum_second_mode :
    fourPointFourierSum 2 = QComplex.zero := by
  native_decide

theorem fourPointFourierSum_third_mode :
    fourPointFourierSum 3 = QComplex.zero := by
  native_decide

theorem fourPointFourierSum_fourth_mode :
    fourPointFourierSum 4 = { re := 4, im := 0 } := by
  native_decide

theorem fourPointFourierSum_fifth_mode :
    fourPointFourierSum 5 = QComplex.zero := by
  native_decide

theorem fourPointFourier_orthogonality_certificate :
    fourPointFourierSum 0 = { re := 4, im := 0 } /\
      fourPointFourierSum 1 = QComplex.zero /\
      fourPointFourierSum 2 = QComplex.zero /\
      fourPointFourierSum 3 = QComplex.zero /\
      fourPointFourierSum 4 = { re := 4, im := 0 } := by
  exact ⟨fourPointFourierSum_zero_mode,
    fourPointFourierSum_first_mode, fourPointFourierSum_second_mode,
    fourPointFourierSum_third_mode, fourPointFourierSum_fourth_mode⟩

/-! A finite Parseval-style energy check for a nonconstant rational signal.

The transform is intentionally unnormalized: the sum of coefficient energies
is four times the input energy. -/

def fourPointWeightedFourierSum (mode : Nat) : QComplex :=
  QComplex.add
    (QComplex.add
      (QComplex.add
        (QComplex.mul (QComplex.ofRat 1)
          (QComplex.natPow RotationSeries.imaginaryUnit (mode * 0)))
        (QComplex.mul (QComplex.ofRat 2)
          (QComplex.natPow RotationSeries.imaginaryUnit (mode * 1))))
      (QComplex.mul (QComplex.ofRat 3)
        (QComplex.natPow RotationSeries.imaginaryUnit (mode * 2))))
    (QComplex.mul (QComplex.ofRat 4)
      (QComplex.natPow RotationSeries.imaginaryUnit (mode * 3)))

theorem fourPointWeightedFourierSum_modes :
    fourPointWeightedFourierSum 0 = { re := 10, im := 0 } /\
      fourPointWeightedFourierSum 1 = { re := -2, im := -2 } /\
      fourPointWeightedFourierSum 2 = { re := -2, im := 0 } /\
      fourPointWeightedFourierSum 3 = { re := -2, im := 2 } := by
  native_decide

theorem fourPointWeightedFourier_parseval_certificate :
    QComplex.normSq (fourPointWeightedFourierSum 0) +
        QComplex.normSq (fourPointWeightedFourierSum 1) +
        QComplex.normSq (fourPointWeightedFourierSum 2) +
        QComplex.normSq (fourPointWeightedFourierSum 3) =
      4 * (1 ^ 2 + 2 ^ 2 + 3 ^ 2 + 4 ^ 2) := by
  native_decide

end ComputableAnalysis
