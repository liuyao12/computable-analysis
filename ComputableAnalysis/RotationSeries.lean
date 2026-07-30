import ComputableAnalysis.PeanoBaker

/-!
# Finite complex rotation-series algebra

This module joins two already finite calculations: rational complex exponential
prefixes and constant-coefficient Peano--Baker rotation prefixes.  It does not
construct a valid complex raw exponential or a continuous ODE solution.
-/

namespace ComputableAnalysis

namespace RotationSeries

/-- Coordinate equality for the local rational-complex structure. -/
theorem qcomplex_ext {z w : QComplex}
    (hre : z.re = w.re) (him : z.im = w.im) : z = w := by
  cases z
  cases w
  simp at hre him ⊢
  exact ⟨hre, him⟩

/-- The rational complex unit on the positive imaginary axis. -/
def imaginaryUnit : QComplex := { re := 0, im := 1 }

/-- The imaginary-axis input used by the rotation exponential prefix. -/
def imaginaryAxis (T : Rat) : QComplex :=
  QComplex.mul imaginaryUnit (QComplex.ofRat T)

theorem imaginaryAxis_coordinates (T : Rat) :
    imaginaryAxis T = { re := 0, im := T } := by
  unfold imaginaryAxis imaginaryUnit QComplex.mul QComplex.ofRat
  change ({ re := 0 * T - 1 * 0, im := 0 * 0 + 1 * T } : QComplex) =
    { re := 0, im := T }
  simp only [Rat.zero_mul, Rat.one_mul, Rat.sub_self, Rat.zero_add]

theorem imaginaryAxis_mul_real (T r : Rat) :
    QComplex.mul (imaginaryAxis T) { re := r, im := 0 } =
      { re := 0, im := T * r } := by
  rw [imaginaryAxis_coordinates]
  change ({ re := 0 * r - T * 0, im := 0 * 0 + T * r } : QComplex) =
    { re := 0, im := T * r }
  simp only [Rat.zero_mul, Rat.mul_zero, Rat.sub_self, Rat.zero_add]

theorem imaginaryAxis_mul_imaginary (T r : Rat) :
    QComplex.mul (imaginaryAxis T) { re := 0, im := r } =
      { re := -(T * r), im := 0 } := by
  rw [imaginaryAxis_coordinates]
  change ({ re := 0 * 0 - T * r, im := 0 * r + T * 0 } : QComplex) =
    { re := -(T * r), im := 0 }
  simp only [Rat.zero_mul, Rat.mul_zero, Rat.sub_eq_add_neg, Rat.add_zero]
  rw [Rat.zero_add]

/-- Even powers of the imaginary-axis input are real alternating powers. -/
theorem imaginaryAxis_pow_even (T : Rat) (k : Nat) :
    QComplex.pow (imaginaryAxis T) (2 * k) =
      { re := ((-1 : Rat) ^ k) * T ^ (2 * k), im := 0 } := by
  induction k with
  | zero =>
      simp [QComplex.pow, QComplex.one]
  | succ k ih =>
      rw [show 2 * (k + 1) = (2 * k + 1) + 1 by omega]
      rw [QComplex.pow]
      rw [show 2 * k + 1 = (2 * k) + 1 by omega]
      rw [QComplex.pow, ih]
      rw [imaginaryAxis_mul_real, imaginaryAxis_mul_imaginary]
      apply qcomplex_ext
      · simp
        simp only [Rat.pow_succ]
        grind [Rat.neg_mul, Rat.mul_neg, Rat.neg_neg, Rat.mul_assoc, Rat.mul_comm]
      · rfl

/-- Odd powers of the imaginary-axis input are imaginary alternating powers. -/
theorem imaginaryAxis_pow_odd (T : Rat) (k : Nat) :
    QComplex.pow (imaginaryAxis T) (2 * k + 1) =
      { re := 0, im := ((-1 : Rat) ^ k) * T ^ (2 * k + 1) } := by
  rw [show 2 * k + 1 = (2 * k) + 1 by omega]
  rw [QComplex.pow, imaginaryAxis_pow_even]
  rw [imaginaryAxis_mul_real]
  apply qcomplex_ext
  · rfl
  · simp only [Rat.pow_succ]
    grind [Rat.mul_assoc, Rat.mul_comm]

/-- The even exponential term at an imaginary-axis input is the matching
cosine-type rational coefficient. -/
theorem expTerm_imaginary_even (T : Rat) (k : Nat) :
    ComplexSeries.expTerm (imaginaryAxis T) (2 * k) =
      { re := LinearODE.RotationSystem.cosineCoefficient T k, im := 0 } := by
  unfold ComplexSeries.expTerm
  rw [imaginaryAxis_pow_even]
  apply qcomplex_ext
  · change ((-1 : Rat) ^ k * T ^ (2 * k)) / factorialRat (2 * k) =
      T ^ (2 * k) / factorialRat (2 * k) * (-1 : Rat) ^ k
    grind [Rat.div_def, Rat.mul_assoc, Rat.mul_comm]
  · change 0 / factorialRat (2 * k) = 0
    rw [Rat.div_def, Rat.zero_mul]

/-- The odd exponential term at an imaginary-axis input is the matching
sine-type rational coefficient on the imaginary axis. -/
theorem expTerm_imaginary_odd (T : Rat) (k : Nat) :
    ComplexSeries.expTerm (imaginaryAxis T) (2 * k + 1) =
      { re := 0, im := LinearODE.RotationSystem.sineCoefficient T k } := by
  unfold ComplexSeries.expTerm
  rw [imaginaryAxis_pow_odd]
  apply qcomplex_ext
  · change 0 / factorialRat (2 * k + 1) = 0
    rw [Rat.div_def, Rat.zero_mul]
  · change ((-1 : Rat) ^ k * T ^ (2 * k + 1)) /
      factorialRat (2 * k + 1) =
        T ^ (2 * k + 1) / factorialRat (2 * k + 1) * (-1 : Rat) ^ k
    grind [Rat.div_def, Rat.mul_assoc, Rat.mul_comm]

/-- The literal finite complex exponential prefix advances by its next
rational term. -/
theorem expPartial_succ (z : QComplex) (terms : Nat) :
    ComplexSeries.expPartial z (terms + 1) =
      QComplex.add (ComplexSeries.expPartial z terms) (ComplexSeries.expTerm z terms) := by
  unfold ComplexSeries.expPartial
  rw [List.range_succ, List.foldl_append]
  rfl

/-- The complex form of the executable rotation prefix. -/
def complexPrefix (T : Rat) (n : Nat) : QComplex :=
  { re := LinearODE.RotationSystem.cosinePrefix T n,
    im := LinearODE.RotationSystem.sinePrefix T n }

/-- At every finite even truncation, the rational complex exponential at
`i*T` is exactly the cosine--sine rotation prefix. -/
theorem expPartial_imaginary_even_split (T : Rat) (n : Nat) :
    ComplexSeries.expPartial (imaginaryAxis T) (2 * n) = complexPrefix T n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega]
      rw [expPartial_succ]
      rw [show 2 * n + 1 = (2 * n) + 1 by omega]
      rw [expPartial_succ, ih]
      rw [expTerm_imaginary_even, expTerm_imaginary_odd]
      apply qcomplex_ext
      · change
          (LinearODE.RotationSystem.cosinePrefix T n +
              LinearODE.RotationSystem.cosineCoefficient T n) + 0 =
            LinearODE.RotationSystem.cosinePrefix T n +
              LinearODE.RotationSystem.cosineCoefficient T n
        exact Rat.add_zero _
      · change
          (LinearODE.RotationSystem.sinePrefix T n + 0) +
              LinearODE.RotationSystem.sineCoefficient T n =
            LinearODE.RotationSystem.sinePrefix T n +
              LinearODE.RotationSystem.sineCoefficient T n
        rw [Rat.add_zero]

end RotationSeries

end ComputableAnalysis
