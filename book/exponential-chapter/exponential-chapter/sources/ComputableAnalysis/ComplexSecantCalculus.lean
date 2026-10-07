import ComputableAnalysis.ComplexPowerCalculus

/-!
# Finite rational-complex secant calculus

This module supplies the reusable second-order estimate for a complex
monomial.  Everything is finite rational algebra.  For a base point `z`, an
increment `h`, and a natural degree `n`, the linear remainder is

`(z+h)^n - z^n - n*z^(n-1)*h`.

The recursive majorant below avoids division, factorials, limits, and a
completed complex field.  It is designed to be summed termwise by computable
power-series charts such as the local logarithm.
-/

namespace ComputableAnalysis
namespace ComplexSecantCalculus

/-- The directional linear term of `z^degree` in the increment `h`. -/
def powerDirectionalTerm (z h : QComplex) : Nat -> QComplex
  | 0 => QComplex.zero
  | degree + 1 =>
      QComplex.scaleRat (((degree + 1 : Nat) : Rat))
        (QComplex.mul (QComplex.pow z degree) h)

/-- The exact finite first-order remainder for a complex natural power. -/
def powerLinearRemainder (z h : QComplex) (degree : Nat) : QComplex :=
  QComplex.sub
    (QComplex.sub (QComplex.pow (QComplex.add z h) degree)
      (QComplex.pow z degree))
    (powerDirectionalTerm z h degree)

/-- The new quadratic term in the recurrence from degree `n` to `n+1`. -/
def powerSecondOrderStep (z h : QComplex) : Nat -> QComplex
  | 0 => QComplex.zero
  | degree + 1 =>
      QComplex.scaleRat (((degree + 1 : Nat) : Rat))
        (QComplex.mul (QComplex.mul (QComplex.pow z degree) h) h)

/-- Exact recurrence
`R_(n+1) = (z+h) R_n + n z^(n-1) h^2`. -/
theorem powerLinearRemainder_succ (z h : QComplex) (degree : Nat) :
    powerLinearRemainder z h (degree + 1) =
      QComplex.add
        (QComplex.mul (QComplex.add z h)
          (powerLinearRemainder z h degree))
        (powerSecondOrderStep z h degree) := by
  cases degree with
  | zero =>
      cases z
      cases h
      simp [powerLinearRemainder, powerDirectionalTerm,
        powerSecondOrderStep, QComplex.pow, QComplex.add, QComplex.sub,
        QComplex.neg, QComplex.mul, QComplex.scaleRat, QComplex.zero,
        QComplex.one]
      constructor <;> grind [Rat.sub_eq_add_neg]
  | succ degree =>
      cases z with
      | mk zre zim =>
          cases h with
          | mk hre him =>
              cases hzpow : QComplex.pow { re := zre, im := zim } degree with
              | mk zpowRe zpowIm =>
                  cases hapow : QComplex.pow
                      (QComplex.add { re := zre, im := zim }
                        { re := hre, im := him }) degree with
                  | mk apowRe apowIm =>
                      simp [powerLinearRemainder, powerDirectionalTerm,
                        powerSecondOrderStep, QComplex.pow, QComplex.add,
                        QComplex.sub, QComplex.neg, QComplex.mul,
                        QComplex.scaleRat, hzpow]
                      constructor <;>
                        grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
                          Rat.mul_assoc, Rat.mul_comm, Rat.add_assoc,
                          Rat.add_comm, Rat.neg_mul, Rat.mul_neg,
                          Rat.neg_neg]

/-- Scalar majorant for the new quadratic recurrence term. -/
def powerSecondOrderMajorant (C H : Rat) : Nat -> Rat
  | 0 => 0
  | degree + 1 =>
      (((degree + 1 : Nat) : Rat)) * C ^ degree * H * H

/-- Recursive scalar majorant for the full power remainder. -/
def powerLinearRemainderMajorant (C H : Rat) : Nat -> Rat
  | 0 => 0
  | degree + 1 =>
      C * powerLinearRemainderMajorant C H degree +
        powerSecondOrderMajorant C H degree

theorem powerSecondOrderMajorant_nonneg {C H : Rat}
    (hC : 0 <= C) (hH : 0 <= H) :
    forall degree, 0 <= powerSecondOrderMajorant C H degree
  | 0 => Rat.le_refl
  | degree + 1 => by
      unfold powerSecondOrderMajorant
      exact Rat.mul_nonneg
        (Rat.mul_nonneg
          (Rat.mul_nonneg (Rat.le_of_lt (Rat.natCast_pos.mpr (by omega)))
            (Rat.pow_nonneg hC)) hH) hH

theorem powerLinearRemainderMajorant_nonneg {C H : Rat}
    (hC : 0 <= C) (hH : 0 <= H) :
    forall degree, 0 <= powerLinearRemainderMajorant C H degree
  | 0 => Rat.le_refl
  | degree + 1 => by
      unfold powerLinearRemainderMajorant
      exact Rat.add_nonneg
        (Rat.mul_nonneg hC
          (powerLinearRemainderMajorant_nonneg hC hH degree))
        (powerSecondOrderMajorant_nonneg hC hH degree)

theorem powerSecondOrderStep_normBound_le
    {z h : QComplex} {C H : Rat}
    (hC : 0 <= C) (hz : QComplex.normBound z <= C)
    (hH : 0 <= H) (hh : QComplex.normBound h <= H) :
    forall degree,
      QComplex.normBound (powerSecondOrderStep z h degree) <=
        powerSecondOrderMajorant C H degree
  | 0 => by
      change QComplex.normBound QComplex.zero <= 0
      rw [QComplex.normBound_zero]
      exact Rat.le_refl
  | degree + 1 => by
      unfold powerSecondOrderStep powerSecondOrderMajorant
      rw [QComplex.normBound_scaleRat,
        qabs_eq_self_of_nonneg
          (Rat.le_of_lt (Rat.natCast_pos.mpr (by omega)))]
      have hpow := QComplex.normBound_pow_le hC hz degree
      have hh0 := QComplex.normBound_nonneg h
      have hpow0 := QComplex.normBound_nonneg (QComplex.pow z degree)
      calc
        (((degree + 1 : Nat) : Rat)) *
            QComplex.normBound
              (QComplex.mul (QComplex.mul (QComplex.pow z degree) h) h) <=
          (((degree + 1 : Nat) : Rat)) *
            (QComplex.normBound (QComplex.mul (QComplex.pow z degree) h) *
              QComplex.normBound h) :=
            Rat.mul_le_mul_of_nonneg_left
              (QComplex.normBound_mul_le _ _)
              (Rat.le_of_lt (Rat.natCast_pos.mpr (by omega)))
        _ <= (((degree + 1 : Nat) : Rat)) *
            ((QComplex.normBound (QComplex.pow z degree) *
              QComplex.normBound h) * QComplex.normBound h) :=
          Rat.mul_le_mul_of_nonneg_left
            (Rat.mul_le_mul_of_nonneg_right
              (QComplex.normBound_mul_le _ _) hh0)
            (Rat.le_of_lt (Rat.natCast_pos.mpr (by omega)))
        _ <= (((degree + 1 : Nat) : Rat)) *
            ((C ^ degree * QComplex.normBound h) *
              QComplex.normBound h) :=
          Rat.mul_le_mul_of_nonneg_left
            (Rat.mul_le_mul_of_nonneg_right
              (Rat.mul_le_mul_of_nonneg_right hpow hh0) hh0)
            (Rat.le_of_lt (Rat.natCast_pos.mpr (by omega)))
        _ <= (((degree + 1 : Nat) : Rat)) *
            ((C ^ degree * H) * H) := by
          have hpowC0 : 0 <= C ^ degree := Rat.pow_nonneg hC
          have hfirst : C ^ degree * QComplex.normBound h <= C ^ degree * H :=
            Rat.mul_le_mul_of_nonneg_left hh hpowC0
          have hleft0 : 0 <= C ^ degree * QComplex.normBound h :=
            Rat.mul_nonneg hpowC0 hh0
          calc
            (((degree + 1 : Nat) : Rat)) *
                ((C ^ degree * QComplex.normBound h) *
                  QComplex.normBound h) <=
              (((degree + 1 : Nat) : Rat)) *
                ((C ^ degree * QComplex.normBound h) * H) :=
              Rat.mul_le_mul_of_nonneg_left
                (Rat.mul_le_mul_of_nonneg_left hh hleft0)
                (Rat.le_of_lt (Rat.natCast_pos.mpr (by omega)))
            _ <= (((degree + 1 : Nat) : Rat)) *
                ((C ^ degree * H) * H) :=
              Rat.mul_le_mul_of_nonneg_left
                (Rat.mul_le_mul_of_nonneg_right hfirst hH)
                (Rat.le_of_lt (Rat.natCast_pos.mpr (by omega)))
        _ = (((degree + 1 : Nat) : Rat)) * C ^ degree * H * H := by
          grind [Rat.mul_assoc]

/-- Quantitative finite secant estimate for every natural complex power. -/
theorem powerLinearRemainder_normBound_le
    {z h : QComplex} {C H : Rat}
    (hC : 0 <= C)
    (hz : QComplex.normBound z <= C)
    (hzh : QComplex.normBound (QComplex.add z h) <= C)
    (hH : 0 <= H) (hh : QComplex.normBound h <= H) :
    forall degree,
      QComplex.normBound (powerLinearRemainder z h degree) <=
        powerLinearRemainderMajorant C H degree
  | 0 => by
      simp [powerLinearRemainder, powerLinearRemainderMajorant,
        powerDirectionalTerm, QComplex.pow, QComplex.sub,
        QComplex.add, QComplex.neg, QComplex.zero, QComplex.one,
        QComplex.normBound]
      decide +kernel
  | degree + 1 => by
      rw [powerLinearRemainder_succ]
      have ih := powerLinearRemainder_normBound_le
        hC hz hzh hH hh degree
      have hsecond := powerSecondOrderStep_normBound_le
        hC hz hH hh degree
      have hR0 := QComplex.normBound_nonneg
        (powerLinearRemainder z h degree)
      have hM0 := powerLinearRemainderMajorant_nonneg hC hH degree
      calc
        QComplex.normBound
            (QComplex.add
              (QComplex.mul (QComplex.add z h)
                (powerLinearRemainder z h degree))
              (powerSecondOrderStep z h degree)) <=
          QComplex.normBound
              (QComplex.mul (QComplex.add z h)
                (powerLinearRemainder z h degree)) +
            QComplex.normBound (powerSecondOrderStep z h degree) :=
          QComplex.normBound_add_le _ _
        _ <= (QComplex.normBound (QComplex.add z h) *
              QComplex.normBound (powerLinearRemainder z h degree)) +
            QComplex.normBound (powerSecondOrderStep z h degree) :=
          Rat.add_le_add_right.mpr (QComplex.normBound_mul_le _ _)
        _ <= (C * QComplex.normBound
              (powerLinearRemainder z h degree)) +
            QComplex.normBound (powerSecondOrderStep z h degree) :=
          Rat.add_le_add_right.mpr
            (Rat.mul_le_mul_of_nonneg_right hzh hR0)
        _ <= C * powerLinearRemainderMajorant C H degree +
            powerSecondOrderMajorant C H degree :=
          rat_add_le_add
            (Rat.mul_le_mul_of_nonneg_left ih hC) hsecond
        _ = powerLinearRemainderMajorant C H (degree + 1) := by
          rw [powerLinearRemainderMajorant]

end ComplexSecantCalculus
end ComputableAnalysis
