import ComputableAnalysis.RationalCircle
import ComputableAnalysis.ComplexMultiplication

/-!
# Finite bridge from rational circle points to rational complex points

This module identifies the rational-coordinate circle multiplication with the
finite multiplication on `QComplex`.  Every object here is a pair of rational
coordinates and every power is a natural-number recursion; no angle semantics,
real exponential, or completeness principle is used.
-/

namespace ComputableAnalysis

namespace RationalCircle

namespace Trigonometry

/-- Embed a rational circle point as a finite rational complex point. -/
def toQComplex (p : PiCirclePoint) : QComplex :=
  { re := p.x, im := p.y }

/-- Circle multiplication is transported to finite complex multiplication. -/
theorem toQComplex_pointMul (p q : PiCirclePoint) :
    toQComplex (pointMul p q) = QComplex.mul (toQComplex p) (toQComplex q) := by
  rfl

theorem toQComplex_pointConj (p : PiCirclePoint) :
    toQComplex (pointConj p) = QComplex.conj (toQComplex p) := by
  rfl

/-- The rational circle unit is transported to the finite complex unit. -/
theorem toQComplex_circleOne :
    toQComplex circleOne = QComplex.one := by
  rfl

/-! The coordinate embedding preserves the finite norm-square invariant. -/

theorem toQComplex_normSq (p : PiCirclePoint) :
    QComplex.normSq (toQComplex p) = Stage.normSq p := by
  rfl

/-- Natural powers of rational circle points are transported to finite
natural powers of their rational complex embeddings. -/
theorem toQComplex_pointPow (p : PiCirclePoint) (n : Nat) :
    toQComplex (pointPow p n) = QComplex.natPow (toQComplex p) n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      rw [pointPow_succ, QComplex.natPow_succ, toQComplex_pointMul, ih]

theorem toQComplex_pointPow_normSq (p : PiCirclePoint) (n : Nat) :
    QComplex.normSq (QComplex.natPow (toQComplex p) n) =
      (Stage.normSq p) ^ n := by
  rw [← toQComplex_pointPow p n, toQComplex_normSq, pointPow_normSq]

theorem toQComplex_pointPow_normSq_of_unit {p : PiCirclePoint}
    (hp : Stage.normSq p = 1) (n : Nat) :
    QComplex.normSq (QComplex.natPow (toQComplex p) n) = 1 := by
  rw [toQComplex_pointPow_normSq, hp]
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Rat.pow_succ, ih, Rat.mul_one]

/-! Lift the finite circle-power computation into the represented complex
raw layer.  The lift is exact at every stage, so this adds representation
without introducing an angle or a completed exponential. -/

def pointPowRaw (p : PiCirclePoint) (n : Nat) : ComplexRaw :=
  ComplexRaw.ofQComplex (toQComplex (pointPow p n))

theorem pointPowRaw_valid (p : PiCirclePoint) (n : Nat) :
    (pointPowRaw p n).Valid := by
  unfold pointPowRaw
  exact ComplexRaw.ofQComplex_valid _

theorem pointPowRaw_equiv_natPow (p : PiCirclePoint) (n : Nat) :
    (pointPowRaw p n).Equiv
      (ComplexRaw.ofQComplex (QComplex.natPow (toQComplex p) n)) := by
  unfold pointPowRaw
  rw [← toQComplex_pointPow p n]
  exact ComplexRaw.equiv_refl _ (ComplexRaw.ofQComplex_valid _)

/-- The represented-complex form of the finite de Moivre product law. -/
theorem pointPowRaw_mul_equiv (p q : PiCirclePoint) (n : Nat) :
    (pointPowRaw (pointMul p q) n).Equiv
      (ComplexRaw.ofQComplex
        (QComplex.mul (QComplex.natPow (toQComplex p) n)
          (QComplex.natPow (toQComplex q) n))) := by
  unfold pointPowRaw
  rw [toQComplex_pointPow, toQComplex_pointMul, QComplex.natPow_mul]
  exact ComplexRaw.equiv_refl _ (ComplexRaw.ofQComplex_valid _)

/-- Finite de Moivre law in embedded rational coordinates: the power of a
circle product is the product of the corresponding finite complex powers. -/
theorem toQComplex_pointPow_mul (p q : PiCirclePoint) (n : Nat) :
    toQComplex (pointPow (pointMul p q) n) =
      QComplex.mul (QComplex.natPow (toQComplex p) n)
        (QComplex.natPow (toQComplex q) n) := by
  rw [toQComplex_pointPow, toQComplex_pointMul, QComplex.natPow_mul]

theorem toQComplex_pointPow_conj (p : PiCirclePoint) (n : Nat) :
    toQComplex (pointPow (pointConj p) n) =
      QComplex.conj (QComplex.natPow (toQComplex p) n) := by
  rw [toQComplex_pointPow, toQComplex_pointConj, QComplex.conj_natPow]

theorem pointPowRaw_conj_equiv (p : PiCirclePoint) (n : Nat) :
    (pointPowRaw (pointConj p) n).Equiv
      (ComplexRaw.ofQComplex
        (QComplex.conj (QComplex.natPow (toQComplex p) n))) := by
  unfold pointPowRaw
  rw [← toQComplex_pointPow_conj p n]
  exact ComplexRaw.equiv_refl _ (ComplexRaw.ofQComplex_valid _)

end Trigonometry

end RationalCircle

end ComputableAnalysis
