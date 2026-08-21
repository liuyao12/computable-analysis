import ComputableAnalysis.FiniteFourierFoundation
import ComputableAnalysis.Series

/-!
# Geometric coefficient stages for Fourier computation

The stage list below is the actual coefficient family
`1, r, r^2, ...`, rather than a pre-summed zero-mode surrogate.  The theorem
exposes the exact finite recurrence for every rational-complex root and mode.
-/

namespace ComputableAnalysis

def geometricCoefficientStage (r : Rat) : Nat -> List QComplex
  | 0 => []
  | n + 1 => geometricCoefficientStage r n ++
      [QComplex.ofRat (r ^ n)]

theorem geometricCoefficientStage_length (r : Rat) (n : Nat) :
    (geometricCoefficientStage r n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [geometricCoefficientStage, ih]

theorem finiteFourierSum_geometricCoefficientStage_succ
    (root : QComplex) (mode : Nat) (r : Rat) (n : Nat) :
    finiteFourierSum root mode (geometricCoefficientStage r (n + 1)) =
      QComplex.add
        (finiteFourierSum root mode (geometricCoefficientStage r n))
        (QComplex.mul
          (QComplex.natPow root (mode * n))
          (QComplex.ofRat (r ^ n))) := by
  rw [geometricCoefficientStage, finiteFourierSum_append_phase]
  rw [geometricCoefficientStage_length]
  simp [finiteFourierSum_singleton, QComplex.natPow,
    QComplex.mul_one_cert]

theorem finiteFourierSum_geometricCoefficientStage_zero (root : QComplex)
    (mode : Nat) (r : Rat) :
    finiteFourierSum root mode (geometricCoefficientStage r 0) =
      QComplex.zero := by
  rfl

end ComputableAnalysis
