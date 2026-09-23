import ComputableAnalysis.ComplexLogarithmJet
import ComputableAnalysis.ComplexSecantCalculus

/-!
# Finite secant remainder for the local complex logarithm

This module combines the reusable monomial remainder estimate with the finite
Taylor prefixes for `log(1+w)`.  It proves a literal rational-complex bound on

`L_N(w+h) - L_N(w) - h D_N(w)`

where `L_N` is the finite logarithm prefix and `D_N` its finite geometric
derivative prefix.  This is the finite quantitative core of the eventual
analytic derivative certificate.
-/

namespace ComputableAnalysis
namespace ComplexLogarithmSecant

open ComplexSecantCalculus

/-- Exact secant remainder of one logarithm Taylor term. -/
def termLinearRemainder (w h : QComplex) (n : Nat) : QComplex :=
  QComplex.sub
    (QComplex.sub
      (ComplexLogarithmApproximation.term (QComplex.add w h) n)
      (ComplexLogarithmApproximation.term w n))
    (QComplex.mul (ComplexLogarithmJet.derivativeTerm w n) h)

/-- The one-term logarithm remainder is the corresponding power remainder
scaled by its exact Taylor coefficient. -/
theorem termLinearRemainder_eq_powerLinearRemainder
    (w h : QComplex) (n : Nat) :
    termLinearRemainder w h n =
      QComplex.scaleRat
        (FormalPowerSeries.altSign n / (((n + 1 : Nat) : Rat)))
        (powerLinearRemainder w h (n + 1)) := by
  have hdenPos : 0 < (((n + 1 : Nat) : Rat)) :=
    Rat.natCast_pos.mpr (by omega)
  have hdenNe : (((n + 1 : Nat) : Rat)) ≠ 0 := Rat.ne_of_gt hdenPos
  cases w with
  | mk wre wim =>
      cases h with
      | mk hre him =>
          cases hsumPow : QComplex.pow
              (QComplex.add { re := wre, im := wim }
                { re := hre, im := him }) (n + 1) with
          | mk sumPowRe sumPowIm =>
              cases hwPowSucc : QComplex.pow
                  { re := wre, im := wim } (n + 1) with
              | mk wPowSuccRe wPowSuccIm =>
                  cases hwPow : QComplex.pow
                      { re := wre, im := wim } n with
                  | mk wPowRe wPowIm =>
                      simp [termLinearRemainder,
                        ComplexLogarithmApproximation.term,
                        ComplexLogarithmJet.derivativeTerm,
                        powerLinearRemainder, powerDirectionalTerm,
                        QComplex.divRat, QComplex.scaleRat, QComplex.mul,
                        QComplex.add, QComplex.sub, QComplex.neg,
                        hwPowSucc, hwPow]
                      constructor <;>
                        grind [Rat.div_def, Rat.mul_inv_cancel _ hdenNe,
                          Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
                          Rat.mul_assoc, Rat.mul_comm, Rat.add_assoc,
                          Rat.add_comm, Rat.neg_mul, Rat.mul_neg,
                          Rat.neg_neg]

private theorem altSign_div_abs (n : Nat) :
    qabs (FormalPowerSeries.altSign n / (((n + 1 : Nat) : Rat))) =
      1 / (((n + 1 : Nat) : Rat)) := by
  have hdenPos : 0 < (((n + 1 : Nat) : Rat)) :=
    Rat.natCast_pos.mpr (by omega)
  have hinvNonneg : 0 <= (((n + 1 : Nat) : Rat))⁻¹ :=
    Rat.le_of_lt ((Rat.inv_pos).2 hdenPos)
  have hsign : qabs (FormalPowerSeries.altSign n) = 1 := by
    unfold FormalPowerSeries.altSign
    split <;> decide +kernel
  rw [Rat.div_def, qabs_mul, hsign,
    qabs_eq_self_of_nonneg hinvNonneg, Rat.one_mul]
  rw [Rat.div_def, Rat.one_mul]

private theorem one_div_nat_succ_nonneg (n : Nat) :
    0 <= 1 / (((n + 1 : Nat) : Rat)) := by
  rw [Rat.div_def, Rat.one_mul]
  exact Rat.le_of_lt ((Rat.inv_pos).2
    (Rat.natCast_pos.mpr (by omega)))

/-- Scalar majorant for one logarithm Taylor-term remainder. -/
def termRemainderMajorant (C H : Rat) (n : Nat) : Rat :=
  (1 / (((n + 1 : Nat) : Rat))) *
    powerLinearRemainderMajorant C H (n + 1)

theorem termRemainderMajorant_nonneg {C H : Rat}
    (hC : 0 <= C) (hH : 0 <= H) (n : Nat) :
    0 <= termRemainderMajorant C H n := by
  unfold termRemainderMajorant
  exact Rat.mul_nonneg
    (one_div_nat_succ_nonneg n)
    (powerLinearRemainderMajorant_nonneg hC hH (n + 1))

theorem termLinearRemainder_normBound_le
    {w h : QComplex} {C H : Rat}
    (hC : 0 <= C)
    (hw : QComplex.normBound w <= C)
    (hwh : QComplex.normBound (QComplex.add w h) <= C)
    (hH : 0 <= H) (hh : QComplex.normBound h <= H)
    (n : Nat) :
    QComplex.normBound (termLinearRemainder w h n) <=
      termRemainderMajorant C H n := by
  rw [termLinearRemainder_eq_powerLinearRemainder,
    QComplex.normBound_scaleRat, altSign_div_abs]
  exact Rat.mul_le_mul_of_nonneg_left
    (powerLinearRemainder_normBound_le hC hw hwh hH hh (n + 1))
    (one_div_nat_succ_nonneg n)

/-- Exact secant remainder of a finite logarithm prefix. -/
def prefixLinearRemainder (w h : QComplex) (terms : Nat) : QComplex :=
  QComplex.sub
    (QComplex.sub
      (ComplexLogarithmApproximation.logPrefix (QComplex.add w h) terms)
      (ComplexLogarithmApproximation.logPrefix w terms))
    (QComplex.mul (ComplexLogarithmJet.derivativePrefix w terms) h)

theorem prefixLinearRemainder_succ (w h : QComplex) (terms : Nat) :
    prefixLinearRemainder w h (terms + 1) =
      QComplex.add (prefixLinearRemainder w h terms)
        (termLinearRemainder w h terms) := by
  unfold prefixLinearRemainder termLinearRemainder
    ComplexLogarithmApproximation.logPrefix
  rw [ComplexLogarithmApproximation.tailPartial,
    ComplexLogarithmApproximation.tailPartial,
    ComplexLogarithmJet.derivativePrefix_succ,
    QComplex.sub_add_sub, QComplex.add_mul_cert,
    QComplex.sub_add_sub]
  simp only [Nat.zero_add]

/-- Sum of all one-term remainder majorants in a finite prefix. -/
def prefixRemainderMajorant (C H : Rat) : Nat -> Rat
  | 0 => 0
  | terms + 1 =>
      prefixRemainderMajorant C H terms +
        termRemainderMajorant C H terms

theorem prefixRemainderMajorant_nonneg {C H : Rat}
    (hC : 0 <= C) (hH : 0 <= H) :
    forall terms, 0 <= prefixRemainderMajorant C H terms
  | 0 => Rat.le_refl
  | terms + 1 => by
      unfold prefixRemainderMajorant
      exact Rat.add_nonneg
        (prefixRemainderMajorant_nonneg hC hH terms)
        (termRemainderMajorant_nonneg hC hH terms)

/-- The exact closed form of the power-remainder majorant on the half-ball.
Writing the degree as `n+1` avoids division: its quadratic coefficient is
`n(n+1) / 2^n`. -/
theorem powerLinearRemainderMajorant_half_succ (H : Rat) :
    forall n,
      powerLinearRemainderMajorant ((1 : Rat) / 2) H (n + 1) =
        (n : Rat) * ((n + 1 : Nat) : Rat) *
          ((1 : Rat) / 2) ^ n * H * H
  | 0 => by
      simp [powerLinearRemainderMajorant, powerSecondOrderMajorant]
      exact Rat.zero_add _
  | n + 1 => by
      rw [powerLinearRemainderMajorant, powerSecondOrderMajorant,
        powerLinearRemainderMajorant_half_succ H n, Rat.pow_succ]
      grind [Rat.mul_add, Rat.add_mul, Rat.mul_assoc, Rat.mul_comm]

/-- On the half-ball, the `n`-th logarithm term contributes exactly
`n / 2^n * H^2` to the recursive scalar majorant. -/
theorem termRemainderMajorant_half_eq (H : Rat) (n : Nat) :
    termRemainderMajorant ((1 : Rat) / 2) H n =
      (n : Rat) * ((1 : Rat) / 2) ^ n * H * H := by
  unfold termRemainderMajorant
  rw [powerLinearRemainderMajorant_half_succ]
  have hdenPos : 0 < (((n + 1 : Nat) : Rat)) :=
    Rat.natCast_pos.mpr (by omega)
  have hdenNe : (((n + 1 : Nat) : Rat)) ≠ 0 := Rat.ne_of_gt hdenPos
  grind [Rat.div_def, Rat.mul_inv_cancel _ hdenNe, Rat.mul_assoc,
    Rat.mul_comm]

/-- Finite weighted geometric sum `sum_{n < terms} n / 2^n`, defined without
an ambient infinite-series API. -/
def weightedHalfSum : Nat → Rat
  | 0 => 0
  | terms + 1 =>
      weightedHalfSum terms +
        (terms : Rat) * ((1 : Rat) / 2) ^ terms

/-- The nonnegative tail that completes `weightedHalfSum terms` to `2`. -/
def weightedHalfComplement (terms : Nat) : Rat :=
  2 * (((terms + 1 : Nat) : Rat)) * ((1 : Rat) / 2) ^ terms

theorem weightedHalfSum_add_complement :
    forall terms,
      weightedHalfSum terms + weightedHalfComplement terms = 2
  | 0 => by decide +kernel
  | terms + 1 => by
      have htail :
          (terms : Rat) * ((1 : Rat) / 2) ^ terms +
              weightedHalfComplement (terms + 1) =
            weightedHalfComplement terms := by
        unfold weightedHalfComplement
        rw [Rat.pow_succ]
        grind [Rat.mul_add, Rat.add_mul, Rat.mul_assoc, Rat.mul_comm]
      rw [weightedHalfSum]
      calc
        weightedHalfSum terms +
              (terms : Rat) * ((1 : Rat) / 2) ^ terms +
            weightedHalfComplement (terms + 1) =
          weightedHalfSum terms + weightedHalfComplement terms := by
            rw [Rat.add_assoc, htail]
        _ = 2 := weightedHalfSum_add_complement terms

theorem weightedHalfComplement_nonneg (terms : Nat) :
    0 <= weightedHalfComplement terms := by
  unfold weightedHalfComplement
  exact Rat.mul_nonneg
    (Rat.mul_nonneg (by decide +kernel)
      (Rat.le_of_lt (Rat.natCast_pos.mpr (by omega))))
    (Rat.pow_nonneg (by decide +kernel))

theorem weightedHalfSum_le_two (terms : Nat) :
    weightedHalfSum terms <= 2 := by
  have hsum := weightedHalfSum_add_complement terms
  have hcomplement := weightedHalfComplement_nonneg terms
  grind

/-- The prefix majorant factors into the finite weighted geometric sum and
the square of the increment bound. -/
theorem prefixRemainderMajorant_half_eq (H : Rat) :
    forall terms,
      prefixRemainderMajorant ((1 : Rat) / 2) H terms =
        weightedHalfSum terms * H * H
  | 0 => by
      simp [prefixRemainderMajorant, weightedHalfSum]
  | terms + 1 => by
      rw [prefixRemainderMajorant, weightedHalfSum,
        prefixRemainderMajorant_half_eq H terms,
        termRemainderMajorant_half_eq]
      grind [Rat.mul_add, Rat.add_mul, Rat.mul_assoc, Rat.mul_comm]

/-- Uniform quadratic bound for every finite logarithm prefix on the
half-ball.  Crucially, the right side no longer depends on the number of
Taylor terms. -/
theorem prefixRemainderMajorant_half_le {H : Rat} (hH : 0 <= H)
    (terms : Nat) :
    prefixRemainderMajorant ((1 : Rat) / 2) H terms <= 2 * H * H := by
  rw [prefixRemainderMajorant_half_eq]
  have hsum := weightedHalfSum_le_two terms
  have hH2 : 0 <= H * H := Rat.mul_nonneg hH hH
  calc
    weightedHalfSum terms * H * H =
        weightedHalfSum terms * (H * H) := Rat.mul_assoc _ _ _
    _ <= 2 * (H * H) := Rat.mul_le_mul_of_nonneg_right hsum hH2
    _ = 2 * H * H := (Rat.mul_assoc _ _ _).symm

/-- Quantitative finite secant theorem for the local logarithm prefix. -/
theorem prefixLinearRemainder_normBound_le
    {w h : QComplex} {C H : Rat}
    (hC : 0 <= C)
    (hw : QComplex.normBound w <= C)
    (hwh : QComplex.normBound (QComplex.add w h) <= C)
    (hH : 0 <= H) (hh : QComplex.normBound h <= H) :
    forall terms,
      QComplex.normBound (prefixLinearRemainder w h terms) <=
        prefixRemainderMajorant C H terms
  | 0 => by
      unfold prefixLinearRemainder prefixRemainderMajorant
        ComplexLogarithmApproximation.logPrefix
        ComplexLogarithmJet.derivativePrefix
      simp only [ComplexLogarithmApproximation.tailPartial,
        ComplexLogarithmJet.derivativeTailPartial]
      cases h
      simp [QComplex.normBound, QComplex.sub, QComplex.add,
        QComplex.neg, QComplex.mul, QComplex.zero]
      decide +kernel
  | terms + 1 => by
      rw [prefixLinearRemainder_succ, prefixRemainderMajorant]
      exact Rat.le_trans (QComplex.normBound_add_le _ _)
        (rat_add_le_add
          (prefixLinearRemainder_normBound_le
            hC hw hwh hH hh terms)
          (termLinearRemainder_normBound_le
            hC hw hwh hH hh terms))

/-- The concrete half-ball specialization used by the local logarithm chart. -/
theorem prefixLinearRemainder_normBound_le_on_halfBall
    {w h : QComplex}
    (hw : QComplex.normBound w <= (1 : Rat) / 2)
    (hwh : QComplex.normBound (QComplex.add w h) <= (1 : Rat) / 2)
    (hh : QComplex.normBound h <= (1 : Rat) / 2)
    (terms : Nat) :
    QComplex.normBound (prefixLinearRemainder w h terms) <=
      prefixRemainderMajorant ((1 : Rat) / 2) ((1 : Rat) / 2) terms :=
  prefixLinearRemainder_normBound_le
    (by decide +kernel) hw hwh (by decide +kernel) hh terms

/-- Uniform finite secant estimate on the half-ball.  The increment bound
`H` is kept explicit so the estimate can be scheduled against any requested
output precision. -/
theorem prefixLinearRemainder_normBound_le_uniformHalfBall
    {w h : QComplex} {H : Rat}
    (hw : QComplex.normBound w <= (1 : Rat) / 2)
    (hwh : QComplex.normBound (QComplex.add w h) <= (1 : Rat) / 2)
    (hH : 0 <= H) (hh : QComplex.normBound h <= H)
    (terms : Nat) :
    QComplex.normBound (prefixLinearRemainder w h terms) <=
      2 * H * H :=
  Rat.le_trans
    (prefixLinearRemainder_normBound_le
      (by decide +kernel) hw hwh hH hh terms)
    (prefixRemainderMajorant_half_le hH terms)

end ComplexLogarithmSecant
end ComputableAnalysis
