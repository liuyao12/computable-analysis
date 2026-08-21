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

/-! The quarter-turn root never amplifies a coordinate: its powers only swap
coordinates and change signs.  This is the elementary bound used by a
geometric tail enclosure for a nonzero Fourier mode. -/
theorem imaginaryUnit_natPow_coord_abs_le_one (n : Nat) :
    qabs ((QComplex.natPow RotationSeries.imaginaryUnit n).re) <= 1 /\
      qabs ((QComplex.natPow RotationSeries.imaginaryUnit n).im) <= 1 := by
  induction n with
  | zero => native_decide
  | succ n ih =>
      rw [QComplex.natPow_succ]
      cases h : QComplex.natPow RotationSeries.imaginaryUnit n with
      | mk re im =>
        simp [h, RotationSeries.imaginaryUnit, QComplex.mul, qabs_neg]
        exact ⟨by simpa [h, Rat.sub_eq_add_neg, Rat.zero_add, Rat.add_zero,
            qabs_neg] using ih.2,
          by simpa [h, Rat.zero_add, Rat.add_zero] using ih.1⟩

theorem quarterTurn_geometric_term_coord_abs_le
    {r : Rat} (hr0 : 0 <= r) (n : Nat) :
    qabs ((QComplex.mul (QComplex.ofRat (r ^ n))
      (QComplex.natPow RotationSeries.imaginaryUnit n)).re) <= r ^ n /\
      qabs ((QComplex.mul (QComplex.ofRat (r ^ n))
        (QComplex.natPow RotationSeries.imaginaryUnit n)).im) <= r ^ n := by
  have hpower := imaginaryUnit_natPow_coord_abs_le_one n
  have hpow_nonneg : 0 <= r ^ n := Rat.pow_nonneg hr0
  have hpow_abs : qabs (r ^ n) = r ^ n :=
    qabs_eq_self_of_nonneg hpow_nonneg
  simp [QComplex.mul, QComplex.ofRat, hpow_abs, qabs_mul,
    Rat.sub_eq_add_neg, Rat.zero_add, Rat.add_zero]
  constructor
  · simpa [Rat.mul_one] using
      Rat.mul_le_mul_of_nonneg_left hpower.1 hpow_nonneg
  · simpa [Rat.mul_one] using
      Rat.mul_le_mul_of_nonneg_left hpower.2 hpow_nonneg

def quarterTurnGeometricStage (r : Rat) (n : Nat) : QComplex :=
  finiteFourierSum RotationSeries.imaginaryUnit 1
    (geometricCoefficientStage r n)

theorem quarterTurnGeometricStage_succ (r : Rat) (n : Nat) :
    quarterTurnGeometricStage r (n + 1) =
      QComplex.add (quarterTurnGeometricStage r n)
        (QComplex.mul
          (QComplex.natPow RotationSeries.imaginaryUnit n)
          (QComplex.ofRat (r ^ n))) := by
  simpa [quarterTurnGeometricStage] using
    (finiteFourierSum_geometricCoefficientStage_succ
      RotationSeries.imaginaryUnit 1 r n)

theorem quarterTurnGeometricStage_increment_coord_abs_le
    {r : Rat} (hr0 : 0 <= r) (n : Nat) :
    qabs ((quarterTurnGeometricStage r (n + 1)).re -
      (quarterTurnGeometricStage r n).re) <= r ^ n /\
    qabs ((quarterTurnGeometricStage r (n + 1)).im -
      (quarterTurnGeometricStage r n).im) <= r ^ n := by
  rw [quarterTurnGeometricStage_succ]
  have hterm := quarterTurn_geometric_term_coord_abs_le hr0 n
  have hcancel (x a : Rat) : x + (-x + a) = a := by
    rw [← Rat.add_assoc, Rat.add_neg_cancel, Rat.zero_add]
  simpa [QComplex.add, QComplex.mul, QComplex.ofRat,
    Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm, Rat.add_left_comm,
    Rat.mul_comm, hcancel] using hterm

theorem quarterTurnGeometricStage_block_coord_abs_le
    {r : Rat} (hr0 : 0 <= r) (n k : Nat) :
    qabs ((quarterTurnGeometricStage r (n + k)).re -
      (quarterTurnGeometricStage r n).re) <=
        r ^ n * Series.geometricSum r k /\
    qabs ((quarterTurnGeometricStage r (n + k)).im -
      (quarterTurnGeometricStage r n).im) <=
        r ^ n * Series.geometricSum r k := by
  induction k with
  | zero =>
      simp [Series.geometricSum, Rat.sub_eq_add_neg, Rat.add_neg_cancel]
      native_decide
  | succ k ih =>
      have hstep := quarterTurnGeometricStage_increment_coord_abs_le hr0 (n + k)
      have hpow_add : ∀ a b : Nat, r ^ (a + b) = r ^ a * r ^ b := by
        intro a b
        induction b with
        | zero => simp
        | succ b ihb =>
            rw [Nat.add_succ, Rat.pow_succ, ihb, Rat.pow_succ]
            grind [Rat.mul_assoc, Rat.mul_comm]
      have hpow : r ^ (n + k) = r ^ n * r ^ k := hpow_add n k
      have hsum : r ^ n * Series.geometricSum r (k + 1) =
          r ^ n * Series.geometricSum r k + r ^ (n + k) := by
        rw [Series.geometricSum_succ, hpow]
        grind [Rat.mul_add, Rat.mul_assoc]
      constructor
      · calc
          qabs ((quarterTurnGeometricStage r (n + (k + 1))).re -
            (quarterTurnGeometricStage r n).re) =
              qabs (((quarterTurnGeometricStage r (n + k)).re -
                (quarterTurnGeometricStage r n).re) +
                ((quarterTurnGeometricStage r (n + k + 1)).re -
                  (quarterTurnGeometricStage r (n + k)).re)) := by
                    rw [show n + (k + 1) = n + k + 1 by omega]
                    rw [quarterTurnGeometricStage_succ]
                    have hcancel (x a : Rat) : x + (-x + a) = a := by
                      rw [← Rat.add_assoc, Rat.add_neg_cancel, Rat.zero_add]
                    simp [QComplex.add, Rat.sub_eq_add_neg,
                      Rat.add_assoc, Rat.add_comm, Rat.add_left_comm, hcancel]
          _ <= qabs ((quarterTurnGeometricStage r (n + k)).re -
                (quarterTurnGeometricStage r n).re) +
              qabs ((quarterTurnGeometricStage r (n + k + 1)).re -
                (quarterTurnGeometricStage r (n + k)).re) :=
            qabs_add_le _ _
          _ <= r ^ n * Series.geometricSum r k + r ^ (n + k) := by
            exact rat_add_le_add ih.1 hstep.1
          _ = r ^ n * Series.geometricSum r (k + 1) := by
            exact hsum.symm
      · calc
          qabs ((quarterTurnGeometricStage r (n + (k + 1))).im -
            (quarterTurnGeometricStage r n).im) =
              qabs (((quarterTurnGeometricStage r (n + k)).im -
                (quarterTurnGeometricStage r n).im) +
                ((quarterTurnGeometricStage r (n + k + 1)).im -
                  (quarterTurnGeometricStage r (n + k)).im)) := by
                    rw [show n + (k + 1) = n + k + 1 by omega]
                    rw [quarterTurnGeometricStage_succ]
                    have hcancel (x a : Rat) : x + (-x + a) = a := by
                      rw [← Rat.add_assoc, Rat.add_neg_cancel, Rat.zero_add]
                    simp [QComplex.add, Rat.sub_eq_add_neg,
                      Rat.add_assoc, Rat.add_comm, Rat.add_left_comm, hcancel]
          _ <= qabs ((quarterTurnGeometricStage r (n + k)).im -
                (quarterTurnGeometricStage r n).im) +
              qabs ((quarterTurnGeometricStage r (n + k + 1)).im -
                (quarterTurnGeometricStage r (n + k)).im) :=
            qabs_add_le _ _
          _ <= r ^ n * Series.geometricSum r k + r ^ (n + k) := by
            exact rat_add_le_add ih.2 hstep.2
          _ = r ^ n * Series.geometricSum r (k + 1) := by
            exact hsum.symm

end ComputableAnalysis
