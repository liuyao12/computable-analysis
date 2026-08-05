import ComputableAnalysis.PeanoBaker

/-!
# Finite complex rotation-series algebra

This module joins two already finite calculations: rational complex exponential
prefixes and constant-coefficient Peano--Baker rotation prefixes.  It
constructs a valid factorial-tail complex raw exponential on rational
imaginary-axis inputs; extending that evaluator to represented inputs and
identifying it with geometry remain separate work.
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

/-- Rational absolute value commutes with a natural power.  This local lemma
keeps the complex-tail certificate below entirely in rational arithmetic. -/
private theorem qabs_pow (x : Rat) : forall n : Nat, qabs (x ^ n) = qabs x ^ n
  | 0 => by
      have hnot : ¬ ((1 : Rat) < 0) := by native_decide
      simp [Rat.pow_zero, qabs, hnot]
  | n + 1 => by
      rw [Rat.pow_succ, qabs_mul, qabs_pow, Rat.pow_succ]

private theorem qabs_neg_one_pow (n : Nat) : qabs ((-1 : Rat) ^ n) = 1 := by
  rw [qabs_pow]
  have hneg : (-1 : Rat) < 0 := by native_decide
  have habs : qabs (-1 : Rat) = 1 := by
    unfold qabs
    simp [hneg]
  rw [habs]
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Rat.pow_succ, ih, Rat.one_mul]

private theorem qabs_inv_factorialRat (n : Nat) :
    qabs ((factorialRat n)⁻¹) = (factorialRat n)⁻¹ := by
  apply qabs_eq_self_of_nonneg
  exact Rat.le_of_lt ((Rat.inv_pos).2 (RationalMajorant.factorialRat_pos n))

/-- The real coordinate of each even imaginary-axis exponential term has the
standard factorial majorant exactly, rather than merely asymptotically. -/
theorem expTerm_imaginary_even_re_abs (T : Rat) (k : Nat) :
    qabs (ComplexSeries.expTerm (imaginaryAxis T) (2 * k)).re =
      RationalMajorant.factorialTailTerm (qabs T) (2 * k) := by
  rw [expTerm_imaginary_even]
  unfold LinearODE.RotationSystem.cosineCoefficient
    RationalMajorant.factorialTailTerm
  rw [Rat.div_def, qabs_mul, qabs_mul, qabs_pow, qabs_inv_factorialRat,
    qabs_neg_one_pow]
  grind [Rat.div_def, Rat.mul_assoc]

/-- The imaginary coordinate of each odd imaginary-axis exponential term has
the standard factorial majorant exactly. -/
theorem expTerm_imaginary_odd_im_abs (T : Rat) (k : Nat) :
    qabs (ComplexSeries.expTerm (imaginaryAxis T) (2 * k + 1)).im =
      RationalMajorant.factorialTailTerm (qabs T) (2 * k + 1) := by
  rw [expTerm_imaginary_odd]
  unfold LinearODE.RotationSystem.sineCoefficient
    RationalMajorant.factorialTailTerm
  rw [Rat.div_def, qabs_mul, qabs_mul, qabs_pow, qabs_inv_factorialRat,
    qabs_neg_one_pow]
  grind [Rat.div_def, Rat.mul_assoc]

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

/-- The certified factorial-tail start for the imaginary-axis exponential
input.  Its magnitude is purely rational. -/
def rotationTailStart (T : Rat) : Nat :=
  RationalMajorant.factorialTailStart (qabs T)

/-- Each stage advances by an even pair of complex exponential terms, so its
center remains exactly a cosine--sine rotation prefix. -/
def rotationTailTerms (T : Rat) (n : Nat) : Nat :=
  2 * (rotationTailStart T + n)

def rotationTailMagnitude (T : Rat) (n : Nat) : Rat :=
  RationalMajorant.factorialTailTerm (qabs T) (rotationTailTerms T n)

/-- A deliberately slack radius: four times the first omitted term.  The
slack makes consecutive certified boxes nest while their centers advance by
one even--odd term pair. -/
def rotationTailRadius (T : Rat) (n : Nat) : Rat :=
  4 * rotationTailMagnitude T n

/-- The center stored at each stage of the certified complex rotation
evaluator. -/
def rotationCenter (T : Rat) (n : Nat) : QComplex :=
  complexPrefix T (rotationTailStart T + n)

/-- A symmetric rational complex box around a rotation-series center. -/
def rotationBox (T : Rat) (n : Nat) : QBox :=
  let c := rotationCenter T n
  let r := rotationTailRadius T n
  { lo := { re := c.re - r, im := c.im - r },
    hi := { re := c.re + r, im := c.im + r } }

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

/-- The even-stage centers of the complex evaluator are literally the finite
complex exponential prefixes, not a separately postulated rotation value. -/
theorem rotationCenter_eq_expPartial (T : Rat) (n : Nat) :
    rotationCenter T n =
      ComplexSeries.expPartial (imaginaryAxis T) (rotationTailTerms T n) := by
  unfold rotationCenter rotationTailTerms
  symm
  exact expPartial_imaginary_even_split T (rotationTailStart T + n)

private theorem rotation_tail_start (T : Rat) (n : Nat) :
    qabs T <= (((rotationTailTerms T n + 1 : Nat) : Rat) / 2) := by
  let s := RationalMajorant.factorialTailStart (qabs T)
  have hs := RationalMajorant.factorialTailStart_satisfies (qabs T)
  have hmono := RationalMajorant.factorialTailStart_mono (qabs T) s (s + 2 * n)
    (by simpa [s] using hs)
  change qabs T <= (((2 * (s + n) + 1 : Nat) : Rat) / 2)
  have hterms : s + (s + 2 * n) + 1 = 2 * (s + n) + 1 := by omega
  rw [hterms] at hmono
  exact hmono

private theorem rotationTailMagnitude_nonneg (T : Rat) (n : Nat) :
    0 <= rotationTailMagnitude T n := by
  unfold rotationTailMagnitude
  exact RationalMajorant.factorialTailTerm_nonneg (qabs_nonneg T) _

private theorem rotationTailMagnitude_next_le_quarter (T : Rat) (n : Nat) :
    rotationTailMagnitude T (n + 1) <= rotationTailMagnitude T n * ((1 : Rat) / 2) ^ 2 := by
  have h := RationalMajorant.factorialTailTerm_le_geometric_from_start
    (C := qabs T) (N := rotationTailTerms T n)
    (qabs_nonneg T) (rotation_tail_start T n) 2
  change RationalMajorant.factorialTailTerm (qabs T) (rotationTailTerms T (n + 1)) <=
    RationalMajorant.factorialTailTerm (qabs T) (rotationTailTerms T n) *
      ((1 : Rat) / 2) ^ 2
  have hterms : rotationTailTerms T (n + 1) = rotationTailTerms T n + 2 := by
    unfold rotationTailTerms
    omega
  rw [hterms]
  exact h

private theorem rotationTailRadius_drop_majorizes (T : Rat) (n : Nat) :
    rotationTailMagnitude T n <=
      rotationTailRadius T n - rotationTailRadius T (n + 1) := by
  have hnext := rotationTailMagnitude_next_le_quarter T n
  have hmag0 := rotationTailMagnitude_nonneg T n
  have hquarter : ((1 : Rat) / 2) ^ 2 = (1 : Rat) / 4 := by native_decide
  rw [hquarter] at hnext
  have hfour : 4 * rotationTailMagnitude T (n + 1) <= rotationTailMagnitude T n := by
    calc
      4 * rotationTailMagnitude T (n + 1) <=
          4 * (rotationTailMagnitude T n * ((1 : Rat) / 4)) :=
        Rat.mul_le_mul_of_nonneg_left hnext (by native_decide)
      _ = rotationTailMagnitude T n := by
        rw [Rat.div_def]
        grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
  unfold rotationTailRadius
  grind [Rat.sub_eq_add_neg]

private theorem rotationCenter_succ (T : Rat) (n : Nat) :
    rotationCenter T (n + 1) =
      QComplex.add
        (QComplex.add (rotationCenter T n)
          (ComplexSeries.expTerm (imaginaryAxis T) (rotationTailTerms T n)))
        (ComplexSeries.expTerm (imaginaryAxis T) (rotationTailTerms T n + 1)) := by
  rw [rotationCenter_eq_expPartial, rotationCenter_eq_expPartial]
  unfold rotationTailTerms
  rw [show 2 * (rotationTailStart T + (n + 1)) =
      (2 * (rotationTailStart T + n) + 1) + 1 by omega]
  rw [expPartial_succ]
  rw [show 2 * (rotationTailStart T + n) + 1 =
      2 * (rotationTailStart T + n) + 1 by rfl]
  rw [expPartial_succ]

private theorem even_term_coordinate_bounds (T : Rat) (k : Nat) :
    -RationalMajorant.factorialTailTerm (qabs T) (2 * k) <=
        (ComplexSeries.expTerm (imaginaryAxis T) (2 * k)).re /\
      (ComplexSeries.expTerm (imaginaryAxis T) (2 * k)).re <=
        RationalMajorant.factorialTailTerm (qabs T) (2 * k) := by
  have habs := expTerm_imaginary_even_re_abs T k
  constructor
  · rw [← habs]
    exact neg_qabs_le_self _
  · rw [← habs]
    exact self_le_qabs _

private theorem odd_term_coordinate_bounds (T : Rat) (k : Nat) :
    -RationalMajorant.factorialTailTerm (qabs T) (2 * k + 1) <=
        (ComplexSeries.expTerm (imaginaryAxis T) (2 * k + 1)).im /\
      (ComplexSeries.expTerm (imaginaryAxis T) (2 * k + 1)).im <=
        RationalMajorant.factorialTailTerm (qabs T) (2 * k + 1) := by
  have habs := expTerm_imaginary_odd_im_abs T k
  constructor
  · rw [← habs]
    exact neg_qabs_le_self _
  · rw [← habs]
    exact self_le_qabs _

private theorem rotationTailMagnitude_middle_le (T : Rat) (n : Nat) :
    RationalMajorant.factorialTailTerm (qabs T) (rotationTailTerms T n + 1) <=
      rotationTailMagnitude T n := by
  have hhalf := RationalMajorant.factorialTailTerm_succ_le_half
    (qabs_nonneg T) (rotationTailTerms T n)
    (RationalMajorant.factorialTailRatio_le_half_from_start
      (qabs T) (rotationTailTerms T n) 0 (rotation_tail_start T n))
  have hmag0 := rotationTailMagnitude_nonneg T n
  change RationalMajorant.factorialTailTerm (qabs T) (rotationTailTerms T n + 1) <=
    RationalMajorant.factorialTailTerm (qabs T) (rotationTailTerms T n) *
      ((1 : Rat) / 2) at hhalf
  calc
    RationalMajorant.factorialTailTerm (qabs T) (rotationTailTerms T n + 1) <=
        rotationTailMagnitude T n * ((1 : Rat) / 2) := by
      simpa [rotationTailMagnitude] using hhalf
    _ <= rotationTailMagnitude T n := by
      have hhalf_le_one : (1 : Rat) / 2 <= 1 := by native_decide
      calc
        rotationTailMagnitude T n * ((1 : Rat) / 2) <=
            rotationTailMagnitude T n * 1 :=
          Rat.mul_le_mul_of_nonneg_left hhalf_le_one hmag0
        _ = rotationTailMagnitude T n := by rw [Rat.mul_one]

private theorem rotation_even_term_coordinate_bounds (T : Rat) (n : Nat) :
    -rotationTailMagnitude T n <=
        (ComplexSeries.expTerm (imaginaryAxis T) (rotationTailTerms T n)).re /\
      (ComplexSeries.expTerm (imaginaryAxis T) (rotationTailTerms T n)).re <=
        rotationTailMagnitude T n := by
  simpa [rotationTailMagnitude, rotationTailTerms] using
    even_term_coordinate_bounds T (rotationTailStart T + n)

private theorem rotation_odd_term_coordinate_bounds (T : Rat) (n : Nat) :
    -rotationTailMagnitude T n <=
        (ComplexSeries.expTerm (imaginaryAxis T) (rotationTailTerms T n + 1)).im /\
      (ComplexSeries.expTerm (imaginaryAxis T) (rotationTailTerms T n + 1)).im <=
        rotationTailMagnitude T n := by
  have hterm := odd_term_coordinate_bounds T (rotationTailStart T + n)
  have hmiddle := rotationTailMagnitude_middle_le T n
  have hterms : rotationTailTerms T n + 1 = 2 * (rotationTailStart T + n) + 1 := by
    unfold rotationTailTerms
    rfl
  constructor
  · rw [hterms]
    calc
      -rotationTailMagnitude T n <=
          -RationalMajorant.factorialTailTerm (qabs T) (2 * (rotationTailStart T + n) + 1) :=
        Rat.neg_le_neg (by simpa [rotationTailMagnitude, rotationTailTerms] using hmiddle)
      _ <= (ComplexSeries.expTerm
          (imaginaryAxis T) (2 * (rotationTailStart T + n) + 1)).im := hterm.1
  · rw [hterms]
    calc
      (ComplexSeries.expTerm
          (imaginaryAxis T) (2 * (rotationTailStart T + n) + 1)).im <=
          RationalMajorant.factorialTailTerm (qabs T) (2 * (rotationTailStart T + n) + 1) :=
        hterm.2
      _ <= rotationTailMagnitude T n := by
        simpa [rotationTailMagnitude, rotationTailTerms] using hmiddle

private theorem rotation_even_term_im_eq_zero (T : Rat) (n : Nat) :
    (ComplexSeries.expTerm (imaginaryAxis T) (rotationTailTerms T n)).im = 0 := by
  change (ComplexSeries.expTerm
    (imaginaryAxis T) (2 * (rotationTailStart T + n))).im = 0
  rw [expTerm_imaginary_even]

private theorem rotation_odd_term_re_eq_zero (T : Rat) (n : Nat) :
    (ComplexSeries.expTerm (imaginaryAxis T) (rotationTailTerms T n + 1)).re = 0 := by
  change (ComplexSeries.expTerm
    (imaginaryAxis T) (2 * (rotationTailStart T + n) + 1)).re = 0
  rw [expTerm_imaginary_odd]

private theorem rotationCenter_step_re_bounds (T : Rat) (n : Nat) :
    -rotationTailMagnitude T n <=
        (rotationCenter T (n + 1)).re - (rotationCenter T n).re /\
      (rotationCenter T (n + 1)).re - (rotationCenter T n).re <=
        rotationTailMagnitude T n := by
  have hcenter := rotationCenter_succ T n
  have heven := rotation_even_term_coordinate_bounds T n
  have hoddzero := rotation_odd_term_re_eq_zero T n
  rw [hcenter]
  change -rotationTailMagnitude T n <=
      ((rotationCenter T n).re +
        (ComplexSeries.expTerm (imaginaryAxis T) (rotationTailTerms T n)).re +
          (ComplexSeries.expTerm (imaginaryAxis T) (rotationTailTerms T n + 1)).re) -
        (rotationCenter T n).re /\
    ((rotationCenter T n).re +
        (ComplexSeries.expTerm (imaginaryAxis T) (rotationTailTerms T n)).re +
          (ComplexSeries.expTerm (imaginaryAxis T) (rotationTailTerms T n + 1)).re) -
        (rotationCenter T n).re <= rotationTailMagnitude T n
  rw [hoddzero]
  grind [Rat.sub_eq_add_neg]

private theorem rotationCenter_step_im_bounds (T : Rat) (n : Nat) :
    -rotationTailMagnitude T n <=
        (rotationCenter T (n + 1)).im - (rotationCenter T n).im /\
      (rotationCenter T (n + 1)).im - (rotationCenter T n).im <=
        rotationTailMagnitude T n := by
  have hcenter := rotationCenter_succ T n
  have hodd := rotation_odd_term_coordinate_bounds T n
  have hevenzero := rotation_even_term_im_eq_zero T n
  rw [hcenter]
  change -rotationTailMagnitude T n <=
      ((rotationCenter T n).im +
        (ComplexSeries.expTerm (imaginaryAxis T) (rotationTailTerms T n)).im +
          (ComplexSeries.expTerm (imaginaryAxis T) (rotationTailTerms T n + 1)).im) -
        (rotationCenter T n).im /\
    ((rotationCenter T n).im +
        (ComplexSeries.expTerm (imaginaryAxis T) (rotationTailTerms T n)).im +
          (ComplexSeries.expTerm (imaginaryAxis T) (rotationTailTerms T n + 1)).im) -
        (rotationCenter T n).im <= rotationTailMagnitude T n
  rw [hevenzero]
  grind [Rat.sub_eq_add_neg]

private theorem rotationBox_width (T : Rat) (n : Nat) :
    (rotationBox T n).width = 2 * rotationTailRadius T n := by
  unfold rotationBox QBox.width
  dsimp
  grind [Rat.sub_eq_add_neg]

private theorem rotationBox_height (T : Rat) (n : Nat) :
    (rotationBox T n).height = 2 * rotationTailRadius T n := by
  unfold rotationBox QBox.height
  dsimp
  grind [Rat.sub_eq_add_neg]

private theorem rotationBox_ordered (T : Rat) (n : Nat) :
    0 <= (rotationBox T n).width /\ 0 <= (rotationBox T n).height := by
  have hmag0 := rotationTailMagnitude_nonneg T n
  rw [rotationBox_width, rotationBox_height]
  unfold rotationTailRadius
  constructor <;> exact Rat.mul_nonneg (by native_decide) (Rat.mul_nonneg (by native_decide) hmag0)

private theorem rotationBox_nested_step (T : Rat) (n : Nat) :
    QBox.NestedIn (rotationBox T (n + 1)) (rotationBox T n) := by
  have hre := rotationCenter_step_re_bounds T n
  have him := rotationCenter_step_im_bounds T n
  have hdrop := rotationTailRadius_drop_majorizes T n
  unfold QBox.NestedIn rotationBox
  dsimp
  constructor
  · constructor
    · grind [Rat.sub_eq_add_neg]
    · grind [Rat.sub_eq_add_neg]
  · constructor
    · grind [Rat.sub_eq_add_neg]
    · grind [Rat.sub_eq_add_neg]

private theorem qbox_nested_trans {A B C : QBox}
    (hAB : QBox.NestedIn A B) (hBC : QBox.NestedIn B C) :
    QBox.NestedIn A C := by
  exact ⟨QComplex.le_trans hBC.1 hAB.1, QComplex.le_trans hAB.2 hBC.2⟩

private theorem rotationBox_nested (T : Rat) :
    forall n m : Nat, n <= m -> QBox.NestedIn (rotationBox T m) (rotationBox T n)
  | n, 0, hnm => by
      have hn : n = 0 := by omega
      subst n
      exact ⟨QComplex.le_refl _, QComplex.le_refl _⟩
  | n, m + 1, hnm => by
      by_cases hlast : n = m + 1
      · subst n
        exact ⟨QComplex.le_refl _, QComplex.le_refl _⟩
      · have hnm' : n <= m := by omega
        exact qbox_nested_trans (rotationBox_nested_step T m) (rotationBox_nested T n m hnm')

private theorem rat_pow_add (q : Rat) (m n : Nat) :
    q ^ (m + n) = q ^ m * q ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [show m + (n + 1) = m + n + 1 by omega]
      rw [Rat.pow_succ, ih, Rat.pow_succ]
      grind [Rat.mul_assoc, Rat.mul_comm]

private theorem half_pow_twice_le (n : Nat) :
    ((1 : Rat) / 2) ^ (2 * n) <= ((1 : Rat) / 2) ^ n := by
  rw [show 2 * n = n + n by omega, rat_pow_add]
  have hhalf0 : (0 : Rat) <= 1 / 2 := by native_decide
  have hhalf1 : (1 : Rat) / 2 <= 1 := by native_decide
  have hpow0 : 0 <= ((1 : Rat) / 2) ^ n := Rat.pow_nonneg hhalf0
  have hpow1 : ((1 : Rat) / 2) ^ n <= 1 := by
    induction n with
    | zero =>
        rw [Rat.pow_zero]
        exact Rat.le_refl
    | succ n ih =>
        rw [Rat.pow_succ]
        calc
          ((1 : Rat) / 2) ^ n * ((1 : Rat) / 2) <=
              ((1 : Rat) / 2) ^ n * 1 :=
            Rat.mul_le_mul_of_nonneg_left hhalf1 (Rat.pow_nonneg hhalf0)
          _ = ((1 : Rat) / 2) ^ n := by rw [Rat.mul_one]
          _ <= 1 := ih (Rat.pow_nonneg hhalf0)
  calc
    ((1 : Rat) / 2) ^ n * ((1 : Rat) / 2) ^ n <=
        ((1 : Rat) / 2) ^ n * 1 :=
      Rat.mul_le_mul_of_nonneg_left hpow1 hpow0
    _ = ((1 : Rat) / 2) ^ n := by rw [Rat.mul_one]

private theorem rotationTailMagnitude_le_geometric (T : Rat) (n : Nat) :
    rotationTailMagnitude T n <=
      rotationTailMagnitude T 0 * ((1 : Rat) / 2) ^ n := by
  have htail := RationalMajorant.factorialTailTerm_le_geometric_from_start
    (C := qabs T) (N := rotationTailTerms T 0)
    (qabs_nonneg T) (rotation_tail_start T 0) (2 * n)
  have hterms : rotationTailTerms T n = rotationTailTerms T 0 + 2 * n := by
    unfold rotationTailTerms
    omega
  unfold rotationTailMagnitude
  rw [hterms]
  calc
    RationalMajorant.factorialTailTerm (qabs T) (rotationTailTerms T 0 + 2 * n) <=
        RationalMajorant.factorialTailTerm (qabs T) (rotationTailTerms T 0) *
          ((1 : Rat) / 2) ^ (2 * n) := htail
    _ <= RationalMajorant.factorialTailTerm (qabs T) (rotationTailTerms T 0) *
          ((1 : Rat) / 2) ^ n :=
      Rat.mul_le_mul_of_nonneg_left (half_pow_twice_le n)
        (RationalMajorant.factorialTailTerm_nonneg (qabs_nonneg T) _)

private theorem rotationBox_width_le_geometric (T : Rat) (n : Nat) :
    (rotationBox T n).width <=
      (8 * rotationTailMagnitude T 0) * ((1 : Rat) / 2) ^ n := by
  have htail := rotationTailMagnitude_le_geometric T n
  rw [rotationBox_width]
  unfold rotationTailRadius
  calc
    2 * (4 * rotationTailMagnitude T n) = 8 * rotationTailMagnitude T n := by
      grind [Rat.mul_assoc]
    _ <= 8 * (rotationTailMagnitude T 0 * ((1 : Rat) / 2) ^ n) :=
      Rat.mul_le_mul_of_nonneg_left htail (by native_decide)
    _ = (8 * rotationTailMagnitude T 0) * ((1 : Rat) / 2) ^ n := by
      grind [Rat.mul_assoc]

private theorem rotationBox_height_le_geometric (T : Rat) (n : Nat) :
    (rotationBox T n).height <=
      (8 * rotationTailMagnitude T 0) * ((1 : Rat) / 2) ^ n := by
  rw [rotationBox_height, ← rotationBox_width]
  exact rotationBox_width_le_geometric T n

private theorem rotationBox_widths_shrink (T : Rat) :
    ComplexRaw.WidthsShrinkToZero (rotationBox T) := by
  intro eps
  let bound : Rat := 8 * rotationTailMagnitude T 0
  let N : Nat := RationalMajorant.halfDecayShift bound eps
  refine ⟨N, ?_⟩
  intro n hn
  have hbound0 : 0 <= bound := by
    dsimp [bound]
    exact Rat.mul_nonneg (by native_decide) (rotationTailMagnitude_nonneg T 0)
  have hwidth := rotationBox_width_le_geometric T n
  have hheight := rotationBox_height_le_geometric T n
  have hfactor : ((1 : Rat) / 2) ^ n <= ((1 : Rat) / 2) ^ N := by
    let k := n - N
    have hNk : N + k = n := by
      dsimp [k]
      exact Nat.add_sub_of_le hn
    rw [← hNk, rat_pow_add]
    have hhalf0 : (0 : Rat) <= 1 / 2 := by native_decide
    have hhalf1 : (1 : Rat) / 2 <= 1 := by native_decide
    have hpow0 : 0 <= ((1 : Rat) / 2) ^ N := Rat.pow_nonneg hhalf0
    have hpow1 : ((1 : Rat) / 2) ^ k <= 1 := by
      induction k with
      | zero =>
          rw [Rat.pow_zero]
          exact Rat.le_refl
      | succ k ih =>
          rw [Rat.pow_succ]
          calc
            ((1 : Rat) / 2) ^ k * ((1 : Rat) / 2) <=
                ((1 : Rat) / 2) ^ k * 1 :=
              Rat.mul_le_mul_of_nonneg_left hhalf1 (Rat.pow_nonneg hhalf0)
            _ = ((1 : Rat) / 2) ^ k := by rw [Rat.mul_one]
            _ <= 1 := ih
    calc
      ((1 : Rat) / 2) ^ N * ((1 : Rat) / 2) ^ k <=
          ((1 : Rat) / 2) ^ N * 1 :=
        Rat.mul_le_mul_of_nonneg_left hpow1 hpow0
      _ = ((1 : Rat) / 2) ^ N := by rw [Rat.mul_one]
  have hscaled : bound * ((1 : Rat) / 2) ^ n <=
      bound * ((1 : Rat) / 2) ^ N :=
    Rat.mul_le_mul_of_nonneg_left hfactor hbound0
  have hfinal := RationalMajorant.halfDecayShift_spec hbound0 eps
  dsimp [N] at hfactor hscaled hfinal ⊢
  dsimp [bound] at hwidth hheight hscaled hfinal
  exact ⟨Rat.le_trans hwidth (Rat.le_trans hscaled hfinal),
    Rat.le_trans hheight (Rat.le_trans hscaled hfinal)⟩

/-- Geometric width metadata for the imaginary-axis exponential evaluator.
Both coordinate widths are at most the displayed rational half-decay bound. -/
def rotationExpRate (T : Rat) : ComplexRaw.Rate (rotationBox T) :=
  .geometric 0
    (8 * rotationTailMagnitude T 0)
    ((1 : Rat) / 2)
    (by native_decide)
    (by native_decide)
    (fun n _ => ⟨rotationBox_width_le_geometric T n,
      rotationBox_height_le_geometric T n⟩)

/-- A certified complex raw evaluator for the exponential series at `i*T`.

Its finite centers are rotation prefixes and its symmetric rational boxes have
an explicit factorial-tail, half-geometric convergence rate. -/
def rotationExpRaw (T : Rat) : ComplexRaw where
  compute := rotationBox T
  rate := rotationExpRate T

theorem rotationExpRaw_compute (T : Rat) (n : Nat) :
    (rotationExpRaw T).compute n = rotationBox T n := rfl

/-- The public rate bound for the checked imaginary-axis exponential
evaluator. -/
theorem rotationExpRaw_width_le_geometric (T : Rat) (n : Nat) :
    ((rotationExpRaw T).compute n).width <=
      (8 * rotationTailMagnitude T 0) * ((1 : Rat) / 2) ^ n :=
  rotationBox_width_le_geometric T n

theorem rotationExpRaw_height_le_geometric (T : Rat) (n : Nat) :
    ((rotationExpRaw T).compute n).height <=
      (8 * rotationTailMagnitude T 0) * ((1 : Rat) / 2) ^ n :=
  rotationBox_height_le_geometric T n

/-- The factorial-tail boxes around the rotation prefixes form a valid raw
complex computation.  This establishes the complex convergence layer needed
before any Euler identity can connect it to geometric trigonometry. -/
theorem rotationExpRaw_valid (T : Rat) : (rotationExpRaw T).Valid := by
  unfold ComplexRaw.Valid ComplexRaw.ValidCompute rotationExpRaw
  constructor
  · exact rotationBox_ordered T
  · constructor
    · intro n m hnm
      have hnest := rotationBox_nested T n m hnm
      exact ⟨hnest.1.1, hnest.2.1, hnest.1.2, hnest.2.2⟩
    · exact rotationBox_widths_shrink T

/-- The real coordinate boxes of the certified imaginary-axis exponential. -/
def rotationCosCompute (T : Rat) (n : Nat) : QInterval :=
  { lo := (rotationBox T n).lo.re, hi := (rotationBox T n).hi.re }

/-- The imaginary coordinate boxes of the certified imaginary-axis
exponential. -/
def rotationSinCompute (T : Rat) (n : Nat) : QInterval :=
  { lo := (rotationBox T n).lo.im, hi := (rotationBox T n).hi.im }

private theorem rotationCosCompute_width_le_geometric (T : Rat) (n : Nat) :
    (rotationCosCompute T n).width <=
      (8 * rotationTailMagnitude T 0) * ((1 : Rat) / 2) ^ n := by
  change (rotationBox T n).width <=
    (8 * rotationTailMagnitude T 0) * ((1 : Rat) / 2) ^ n
  exact rotationBox_width_le_geometric T n

private theorem rotationSinCompute_width_le_geometric (T : Rat) (n : Nat) :
    (rotationSinCompute T n).width <=
      (8 * rotationTailMagnitude T 0) * ((1 : Rat) / 2) ^ n := by
  change (rotationBox T n).height <=
    (8 * rotationTailMagnitude T 0) * ((1 : Rat) / 2) ^ n
  exact rotationBox_height_le_geometric T n

def rotationCosRate (T : Rat) : RealRaw.Rate (rotationCosCompute T) :=
  .geometric 0
    (8 * rotationTailMagnitude T 0)
    ((1 : Rat) / 2)
    (by native_decide)
    (by native_decide)
    (fun n _ => rotationCosCompute_width_le_geometric T n)

def rotationSinRate (T : Rat) : RealRaw.Rate (rotationSinCompute T) :=
  .geometric 0
    (8 * rotationTailMagnitude T 0)
    ((1 : Rat) / 2)
    (by native_decide)
    (by native_decide)
    (fun n _ => rotationSinCompute_width_le_geometric T n)

/-- The power-series cosine coordinate at a rational input, as a certified
raw real computation. -/
def rotationCosRaw (T : Rat) : RealRaw where
  compute := rotationCosCompute T
  rate := rotationCosRate T

/-- The power-series sine coordinate at a rational input, as a certified raw
real computation. -/
def rotationSinRaw (T : Rat) : RealRaw where
  compute := rotationSinCompute T
  rate := rotationSinRate T

theorem rotationCosRaw_valid (T : Rat) : (rotationCosRaw T).Valid := by
  change RealRaw.ValidCompute (rotationCosCompute T)
  have hvalid := ComplexRaw.realPart_valid (rotationExpRaw_valid T)
  simpa [rotationCosCompute, ComplexRaw.realPart, rotationExpRaw] using hvalid

theorem rotationSinRaw_valid (T : Rat) : (rotationSinRaw T).Valid := by
  change RealRaw.ValidCompute (rotationSinCompute T)
  have hvalid := ComplexRaw.imagPart_valid (rotationExpRaw_valid T)
  simpa [rotationSinCompute, ComplexRaw.imagPart, rotationExpRaw] using hvalid

theorem rotationCosRaw_compute (T : Rat) (n : Nat) :
    (rotationCosRaw T).compute n =
      { lo := LinearODE.RotationSystem.cosinePrefix T (rotationTailStart T + n) -
          rotationTailRadius T n,
        hi := LinearODE.RotationSystem.cosinePrefix T (rotationTailStart T + n) +
          rotationTailRadius T n } := rfl

theorem rotationSinRaw_compute (T : Rat) (n : Nat) :
    (rotationSinRaw T).compute n =
      { lo := LinearODE.RotationSystem.sinePrefix T (rotationTailStart T + n) -
          rotationTailRadius T n,
        hi := LinearODE.RotationSystem.sinePrefix T (rotationTailStart T + n) +
          rotationTailRadius T n } := rfl

theorem rotationCosRaw_width_le_geometric (T : Rat) (n : Nat) :
    ((rotationCosRaw T).compute n).width <=
      (8 * rotationTailMagnitude T 0) * ((1 : Rat) / 2) ^ n :=
  rotationCosCompute_width_le_geometric T n

theorem rotationSinRaw_width_le_geometric (T : Rat) (n : Nat) :
    ((rotationSinRaw T).compute n).width <=
      (8 * rotationTailMagnitude T 0) * ((1 : Rat) / 2) ^ n :=
  rotationSinCompute_width_le_geometric T n

/-!
## A uniform bounded-input rotation schedule

The preceding evaluator selects a factorial start from its particular rational
input.  For a represented parameter, such as the interval computation of
`pi/2`, it is more useful to have one schedule that works for every rational
sample in a fixed certified range.  The following construction fixes the
majorant at `2`; the later represented-input step need only control movement
of the rational samples, not a changing factorial start.
-/

/-- The common factorial start for every imaginary-axis input of absolute
value at most `2`. -/
def uniformRotationTailStart : Nat :=
  RationalMajorant.factorialTailStart 2

/-- Each uniform stage advances by an even pair of exponential terms. -/
def uniformRotationTailTerms (n : Nat) : Nat :=
  2 * (uniformRotationTailStart + n)

/-- The common scalar factorial majorant at the uniform stage. -/
def uniformRotationTailMagnitude (n : Nat) : Rat :=
  RationalMajorant.factorialTailTerm 2 (uniformRotationTailTerms n)

/-- Four times the common omitted-term bound, enough to absorb one paired
center update and keep the rational boxes nested. -/
def uniformRotationTailRadius (n : Nat) : Rat :=
  4 * uniformRotationTailMagnitude n

/-- The finite rotation prefix attached to the common bounded-input schedule. -/
def uniformRotationCenter (T : Rat) (n : Nat) : QComplex :=
  complexPrefix T (uniformRotationTailStart + n)

/- The change in a nonconstant cosine coefficient is controlled by the
shifted factorial majorant at radius two. -/
private theorem cosineCoefficient_succ_input_lipschitz (T U : Rat)
    (hT : qabs T <= 2) (hU : qabs U <= 2) (k : Nat) :
    qabs (LinearODE.RotationSystem.cosineCoefficient T (k + 1) -
        LinearODE.RotationSystem.cosineCoefficient U (k + 1)) <=
      qabs (T - U) * 2 *
        RationalMajorant.factorialTailTerm 2 (2 * k + 1) := by
  have hpower := RationalMajorant.qabs_power_div_factorial_sub_le_two
    hT hU (2 * k + 1)
  have hsign := qabs_neg_one_pow (k + 1)
  have hrewrite :
      LinearODE.RotationSystem.cosineCoefficient T (k + 1) -
          LinearODE.RotationSystem.cosineCoefficient U (k + 1) =
        (T ^ ((2 * k + 1) + 1) / factorialRat ((2 * k + 1) + 1) -
          U ^ ((2 * k + 1) + 1) / factorialRat ((2 * k + 1) + 1)) *
          ((-1 : Rat) ^ (k + 1)) := by
    unfold LinearODE.RotationSystem.cosineCoefficient
    rw [show 2 * (k + 1) = (2 * k + 1) + 1 by omega]
    grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.mul_assoc,
      Rat.mul_comm]
  rw [hrewrite, qabs_mul, hsign, Rat.mul_one]
  exact hpower

/- The change in a sine coefficient is controlled by the preceding
factorial term at the same uniform radius. -/
private theorem sineCoefficient_input_lipschitz (T U : Rat)
    (hT : qabs T <= 2) (hU : qabs U <= 2) (k : Nat) :
    qabs (LinearODE.RotationSystem.sineCoefficient T k -
        LinearODE.RotationSystem.sineCoefficient U k) <=
      qabs (T - U) * 2 *
        RationalMajorant.factorialTailTerm 2 (2 * k) := by
  have hpower := RationalMajorant.qabs_power_div_factorial_sub_le_two
    hT hU (2 * k)
  have hsign := qabs_neg_one_pow k
  have hrewrite :
      LinearODE.RotationSystem.sineCoefficient T k -
          LinearODE.RotationSystem.sineCoefficient U k =
        (T ^ ((2 * k) + 1) / factorialRat ((2 * k) + 1) -
          U ^ ((2 * k) + 1) / factorialRat ((2 * k) + 1)) *
          ((-1 : Rat) ^ k) := by
    unfold LinearODE.RotationSystem.sineCoefficient
    grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.mul_assoc,
      Rat.mul_comm]
  rw [hrewrite, qabs_mul, hsign, Rat.mul_one]
  exact hpower

/- The coordinatewise rational distance between two finite rotation
prefixes.  It is only a finite sum of rational absolute values. -/
def rotationPrefixDistance (T U : Rat) (m : Nat) : Rat :=
  qabs (LinearODE.RotationSystem.cosinePrefix T m -
      LinearODE.RotationSystem.cosinePrefix U m) +
    qabs (LinearODE.RotationSystem.sinePrefix T m -
      LinearODE.RotationSystem.sinePrefix U m)

/- The factorial budget for the first m rotation-prefix coefficient pairs. -/
def rotationPrefixSensitivity (m : Nat) : Rat :=
  2 * RationalMajorant.factorialTailPartial 2 0 (2 * m - 1)

private theorem rotationPrefixDistance_zero (T U : Rat) :
    rotationPrefixDistance T U 0 = 0 := by
  unfold rotationPrefixDistance
  change qabs ((0 : Rat) - 0) + qabs ((0 : Rat) - 0) = 0
  have hzero : qabs (0 : Rat) = 0 := by
    rw [qabs_eq_self_of_nonneg (by native_decide)]
  have hdiff : (0 : Rat) - 0 = 0 := by native_decide
  rw [hdiff, hzero]
  native_decide

private theorem rotationPrefixDistance_succ_le (T U : Rat) (m : Nat) :
    rotationPrefixDistance T U (m + 1) <=
      rotationPrefixDistance T U m +
        qabs (LinearODE.RotationSystem.cosineCoefficient T m -
          LinearODE.RotationSystem.cosineCoefficient U m) +
        qabs (LinearODE.RotationSystem.sineCoefficient T m -
          LinearODE.RotationSystem.sineCoefficient U m) := by
  unfold rotationPrefixDistance
  simp only [LinearODE.RotationSystem.cosinePrefix,
    LinearODE.RotationSystem.sinePrefix]
  have hre :
      (LinearODE.RotationSystem.cosinePrefix T m +
          LinearODE.RotationSystem.cosineCoefficient T m) -
        (LinearODE.RotationSystem.cosinePrefix U m +
          LinearODE.RotationSystem.cosineCoefficient U m) =
        (LinearODE.RotationSystem.cosinePrefix T m -
          LinearODE.RotationSystem.cosinePrefix U m) +
        (LinearODE.RotationSystem.cosineCoefficient T m -
          LinearODE.RotationSystem.cosineCoefficient U m) := by
    grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]
  have him :
      (LinearODE.RotationSystem.sinePrefix T m +
          LinearODE.RotationSystem.sineCoefficient T m) -
        (LinearODE.RotationSystem.sinePrefix U m +
          LinearODE.RotationSystem.sineCoefficient U m) =
        (LinearODE.RotationSystem.sinePrefix T m -
          LinearODE.RotationSystem.sinePrefix U m) +
        (LinearODE.RotationSystem.sineCoefficient T m -
          LinearODE.RotationSystem.sineCoefficient U m) := by
    grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]
  rw [hre, him]
  calc
    qabs (LinearODE.RotationSystem.cosinePrefix T m -
        LinearODE.RotationSystem.cosinePrefix U m +
        (LinearODE.RotationSystem.cosineCoefficient T m -
          LinearODE.RotationSystem.cosineCoefficient U m)) +
      qabs (LinearODE.RotationSystem.sinePrefix T m -
        LinearODE.RotationSystem.sinePrefix U m +
        (LinearODE.RotationSystem.sineCoefficient T m -
          LinearODE.RotationSystem.sineCoefficient U m)) <=
        (qabs (LinearODE.RotationSystem.cosinePrefix T m -
          LinearODE.RotationSystem.cosinePrefix U m) +
          qabs (LinearODE.RotationSystem.cosineCoefficient T m -
            LinearODE.RotationSystem.cosineCoefficient U m)) +
          (qabs (LinearODE.RotationSystem.sinePrefix T m -
            LinearODE.RotationSystem.sinePrefix U m) +
            qabs (LinearODE.RotationSystem.sineCoefficient T m -
              LinearODE.RotationSystem.sineCoefficient U m)) :=
      rat_add_le_add (qabs_add_le _ _) (qabs_add_le _ _)
    _ = rotationPrefixDistance T U m +
        qabs (LinearODE.RotationSystem.cosineCoefficient T m -
          LinearODE.RotationSystem.cosineCoefficient U m) +
        qabs (LinearODE.RotationSystem.sineCoefficient T m -
          LinearODE.RotationSystem.sineCoefficient U m) := by
      unfold rotationPrefixDistance
      grind [Rat.add_assoc, Rat.add_comm]

private theorem rotationPrefixSensitivity_succ_succ (m : Nat) :
    rotationPrefixSensitivity (m + 2) =
      rotationPrefixSensitivity (m + 1) +
        2 * RationalMajorant.factorialTailTerm 2 (2 * m + 1) +
        2 * RationalMajorant.factorialTailTerm 2 (2 * m + 2) := by
  unfold rotationPrefixSensitivity
  rw [show 2 * (m + 2) - 1 = (2 * m + 2) + 1 by omega,
    RationalMajorant.factorialTailPartial]
  rw [show 2 * m + 2 = (2 * m + 1) + 1 by omega,
    RationalMajorant.factorialTailPartial]
  have hindex : 2 * (m + 1) - 1 = 2 * m + 1 := by omega
  rw [hindex]
  grind [Rat.mul_add, Rat.mul_assoc, Rat.add_assoc, Rat.add_comm]

private theorem rotationPrefixDistance_le_sensitivity (T U : Rat)
    (hT : qabs T <= 2) (hU : qabs U <= 2) :
    forall m : Nat,
      rotationPrefixDistance T U m <=
        qabs (T - U) * rotationPrefixSensitivity m
  | 0 => by
      rw [rotationPrefixDistance_zero]
      unfold rotationPrefixSensitivity
      change (0 : Rat) <= qabs (T - U) * (2 * 0)
      calc
        (0 : Rat) <= 0 := Rat.le_refl
        _ = qabs (T - U) * (2 * 0) := by
          rw [Rat.mul_zero]
          exact (Rat.mul_zero _).symm
  | 1 => by
      have hstep := rotationPrefixDistance_succ_le T U 0
      have hinvOne : ((1 : Rat)⁻¹) = 1 := by native_decide
      have hcosT : LinearODE.RotationSystem.cosineCoefficient T 0 = 1 := by
        simp [LinearODE.RotationSystem.cosineCoefficient, factorialRat, factorial,
          Rat.div_def, hinvOne]
      have hcosU : LinearODE.RotationSystem.cosineCoefficient U 0 = 1 := by
        simp [LinearODE.RotationSystem.cosineCoefficient, factorialRat, factorial,
          Rat.div_def, hinvOne]
      have hcos : qabs (LinearODE.RotationSystem.cosineCoefficient T 0 -
          LinearODE.RotationSystem.cosineCoefficient U 0) = 0 := by
        rw [hcosT, hcosU]
        have hzero : qabs (0 : Rat) = 0 := by
          rw [qabs_eq_self_of_nonneg (by native_decide)]
        rw [show (1 : Rat) - 1 = 0 by native_decide, hzero]
      have hsinT : LinearODE.RotationSystem.sineCoefficient T 0 = T := by
        simp [LinearODE.RotationSystem.sineCoefficient, factorialRat, factorial,
          Rat.div_def, hinvOne]
      have hsinU : LinearODE.RotationSystem.sineCoefficient U 0 = U := by
        simp [LinearODE.RotationSystem.sineCoefficient, factorialRat, factorial,
          Rat.div_def, hinvOne]
      have hsin : qabs (LinearODE.RotationSystem.sineCoefficient T 0 -
          LinearODE.RotationSystem.sineCoefficient U 0) = qabs (T - U) := by
        rw [hsinT, hsinU]
      rw [rotationPrefixDistance_zero, hcos, hsin, Rat.add_zero,
        Rat.zero_add] at hstep
      have hsens : rotationPrefixSensitivity 1 = 2 := by native_decide
      rw [hsens]
      calc
        rotationPrefixDistance T U 1 <= qabs (T - U) := hstep
        _ = qabs (T - U) * 1 := by rw [Rat.mul_one]
        _ <= qabs (T - U) * 2 :=
          Rat.mul_le_mul_of_nonneg_left (by native_decide) (qabs_nonneg _)
  | m + 2 => by
      have ih := rotationPrefixDistance_le_sensitivity T U hT hU (m + 1)
      have hstep := rotationPrefixDistance_succ_le T U (m + 1)
      have hcos := cosineCoefficient_succ_input_lipschitz T U hT hU m
      have hsin := sineCoefficient_input_lipschitz T U hT hU (m + 1)
      have hsens := rotationPrefixSensitivity_succ_succ m
      rw [hsens]
      calc
        rotationPrefixDistance T U (m + 2) <=
            rotationPrefixDistance T U (m + 1) +
              qabs (LinearODE.RotationSystem.cosineCoefficient T (m + 1) -
                LinearODE.RotationSystem.cosineCoefficient U (m + 1)) +
              qabs (LinearODE.RotationSystem.sineCoefficient T (m + 1) -
                LinearODE.RotationSystem.sineCoefficient U (m + 1)) := hstep
        _ <= qabs (T - U) * rotationPrefixSensitivity (m + 1) +
              (qabs (T - U) * 2 *
                RationalMajorant.factorialTailTerm 2 (2 * m + 1)) +
              (qabs (T - U) * 2 *
                RationalMajorant.factorialTailTerm 2 (2 * m + 2)) :=
          rat_add_le_add (rat_add_le_add ih hcos) hsin
        _ = qabs (T - U) *
            (rotationPrefixSensitivity (m + 1) +
              2 * RationalMajorant.factorialTailTerm 2 (2 * m + 1) +
              2 * RationalMajorant.factorialTailTerm 2 (2 * m + 2)) := by
          grind [Rat.mul_add, Rat.mul_assoc, Rat.add_assoc]

/- The finite sensitivity budget is uniformly bounded by sixteen on the
fixed input range.  It is intentionally coarse: it buys one simple rational
radius for a later represented-input construction. -/
private theorem rotationPrefixSensitivity_le_sixteen (m : Nat) :
    rotationPrefixSensitivity m <= 16 := by
  unfold rotationPrefixSensitivity
  calc
    2 * RationalMajorant.factorialTailPartial 2 0 (2 * m - 1) <= 2 * 8 :=
      Rat.mul_le_mul_of_nonneg_left
        (RationalMajorant.factorialTailPartial_two_le_eight (2 * m - 1))
        (by native_decide)
    _ = 16 := by native_decide

/- A common bounded-input factorial prefix is Lipschitz in its rational
input.  The statement is still entirely finite: both sides refer only to a
specified pair of rational prefixes. -/
theorem uniformRotationCenter_input_lipschitz (T U : Rat)
    (hT : qabs T <= 2) (hU : qabs U <= 2) (n : Nat) :
    qabs ((uniformRotationCenter T n).re - (uniformRotationCenter U n).re) <=
        16 * qabs (T - U) /\
      qabs ((uniformRotationCenter T n).im - (uniformRotationCenter U n).im) <=
        16 * qabs (T - U) := by
  have hdistance := rotationPrefixDistance_le_sensitivity T U hT hU
    (uniformRotationTailStart + n)
  have hsensitivity := rotationPrefixSensitivity_le_sixteen
    (uniformRotationTailStart + n)
  have hsum : rotationPrefixDistance T U (uniformRotationTailStart + n) <=
      qabs (T - U) * 16 := by
    calc
      rotationPrefixDistance T U (uniformRotationTailStart + n) <=
          qabs (T - U) *
            rotationPrefixSensitivity (uniformRotationTailStart + n) := hdistance
      _ <= qabs (T - U) * 16 :=
        Rat.mul_le_mul_of_nonneg_left hsensitivity (qabs_nonneg _)
  have hre :
      qabs (LinearODE.RotationSystem.cosinePrefix T
          (uniformRotationTailStart + n) -
        LinearODE.RotationSystem.cosinePrefix U
          (uniformRotationTailStart + n)) <=
        rotationPrefixDistance T U (uniformRotationTailStart + n) := by
    unfold rotationPrefixDistance
    have himnonneg : 0 <= qabs (LinearODE.RotationSystem.sinePrefix T
        (uniformRotationTailStart + n) -
      LinearODE.RotationSystem.sinePrefix U
        (uniformRotationTailStart + n)) := qabs_nonneg _
    grind
  have him :
      qabs (LinearODE.RotationSystem.sinePrefix T
          (uniformRotationTailStart + n) -
        LinearODE.RotationSystem.sinePrefix U
          (uniformRotationTailStart + n)) <=
        rotationPrefixDistance T U (uniformRotationTailStart + n) := by
    unfold rotationPrefixDistance
    have hrenonneg : 0 <= qabs (LinearODE.RotationSystem.cosinePrefix T
        (uniformRotationTailStart + n) -
      LinearODE.RotationSystem.cosinePrefix U
        (uniformRotationTailStart + n)) := qabs_nonneg _
    grind
  constructor <;> unfold uniformRotationCenter complexPrefix
  · calc
      qabs (LinearODE.RotationSystem.cosinePrefix T
          (uniformRotationTailStart + n) -
        LinearODE.RotationSystem.cosinePrefix U
          (uniformRotationTailStart + n)) <=
          rotationPrefixDistance T U (uniformRotationTailStart + n) := hre
      _ <= qabs (T - U) * 16 := hsum
      _ = 16 * qabs (T - U) := by grind [Rat.mul_comm]
  · calc
      qabs (LinearODE.RotationSystem.sinePrefix T
          (uniformRotationTailStart + n) -
        LinearODE.RotationSystem.sinePrefix U
          (uniformRotationTailStart + n)) <=
          rotationPrefixDistance T U (uniformRotationTailStart + n) := him
      _ <= qabs (T - U) * 16 := hsum
      _ = 16 * qabs (T - U) := by grind [Rat.mul_comm]

/-- A symmetric complex box around the uniform bounded-input rotation
prefix. -/
def uniformRotationBox (T : Rat) (n : Nat) : QBox :=
  let c := uniformRotationCenter T n
  let r := uniformRotationTailRadius n
  { lo := { re := c.re - r, im := c.im - r },
    hi := { re := c.re + r, im := c.im + r } }

private theorem uniform_rotation_tail_start (n : Nat) :
    (2 : Rat) <= (((uniformRotationTailTerms n + 1 : Nat) : Rat) / 2) := by
  let s := uniformRotationTailStart
  have hs := RationalMajorant.factorialTailStart_satisfies (2 : Rat)
  have hmono := RationalMajorant.factorialTailStart_mono (2 : Rat) s (s + 2 * n)
    (by simpa [s, uniformRotationTailStart] using hs)
  change (2 : Rat) <= (((2 * (s + n) + 1 : Nat) : Rat) / 2)
  have hterms : s + (s + 2 * n) + 1 = 2 * (s + n) + 1 := by omega
  rw [hterms] at hmono
  exact hmono

private theorem uniformRotationTailMagnitude_nonneg (n : Nat) :
    0 <= uniformRotationTailMagnitude n := by
  unfold uniformRotationTailMagnitude
  exact RationalMajorant.factorialTailTerm_nonneg (by native_decide) _

private theorem uniformRotationTailMagnitude_next_le_quarter (n : Nat) :
    uniformRotationTailMagnitude (n + 1) <=
      uniformRotationTailMagnitude n * ((1 : Rat) / 2) ^ 2 := by
  have h := RationalMajorant.factorialTailTerm_le_geometric_from_start
    (C := (2 : Rat)) (N := uniformRotationTailTerms n)
    (by native_decide) (uniform_rotation_tail_start n) 2
  change RationalMajorant.factorialTailTerm 2 (uniformRotationTailTerms (n + 1)) <=
    RationalMajorant.factorialTailTerm 2 (uniformRotationTailTerms n) *
      ((1 : Rat) / 2) ^ 2
  have hterms : uniformRotationTailTerms (n + 1) =
      uniformRotationTailTerms n + 2 := by
    unfold uniformRotationTailTerms
    omega
  rw [hterms]
  exact h

private theorem uniformRotationTailRadius_drop_majorizes (n : Nat) :
    uniformRotationTailMagnitude n <=
      uniformRotationTailRadius n - uniformRotationTailRadius (n + 1) := by
  have hnext := uniformRotationTailMagnitude_next_le_quarter n
  have hmag0 := uniformRotationTailMagnitude_nonneg n
  have hquarter : ((1 : Rat) / 2) ^ 2 = (1 : Rat) / 4 := by native_decide
  rw [hquarter] at hnext
  have hfour : 4 * uniformRotationTailMagnitude (n + 1) <=
      uniformRotationTailMagnitude n := by
    calc
      4 * uniformRotationTailMagnitude (n + 1) <=
          4 * (uniformRotationTailMagnitude n * ((1 : Rat) / 4)) :=
        Rat.mul_le_mul_of_nonneg_left hnext (by native_decide)
      _ = uniformRotationTailMagnitude n := by
        rw [Rat.div_def]
        grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
  unfold uniformRotationTailRadius
  grind [Rat.sub_eq_add_neg]

private theorem uniformRotationCenter_succ (T : Rat) (n : Nat) :
    uniformRotationCenter T (n + 1) =
      QComplex.add
        (QComplex.add (uniformRotationCenter T n)
          (ComplexSeries.expTerm (imaginaryAxis T) (uniformRotationTailTerms n)))
        (ComplexSeries.expTerm (imaginaryAxis T) (uniformRotationTailTerms n + 1)) := by
  unfold uniformRotationCenter uniformRotationTailTerms
  rw [← expPartial_imaginary_even_split T (uniformRotationTailStart + (n + 1)),
    ← expPartial_imaginary_even_split T (uniformRotationTailStart + n)]
  rw [show 2 * (uniformRotationTailStart + (n + 1)) =
      (2 * (uniformRotationTailStart + n) + 1) + 1 by omega]
  rw [expPartial_succ, expPartial_succ]

/-- The bounded-input center is still the literal even exponential prefix. -/
theorem uniformRotationCenter_eq_expPartial (T : Rat) (n : Nat) :
    uniformRotationCenter T n =
      ComplexSeries.expPartial (imaginaryAxis T) (uniformRotationTailTerms n) := by
  unfold uniformRotationCenter uniformRotationTailTerms
  symm
  exact expPartial_imaginary_even_split T (uniformRotationTailStart + n)

private theorem uniformRotationTailMagnitude_middle_le (n : Nat) :
    RationalMajorant.factorialTailTerm 2 (uniformRotationTailTerms n + 1) <=
      uniformRotationTailMagnitude n := by
  have hhalf := RationalMajorant.factorialTailTerm_succ_le_half
    (by native_decide : (0 : Rat) <= 2) (uniformRotationTailTerms n)
    (RationalMajorant.factorialTailRatio_le_half_from_start
      2 (uniformRotationTailTerms n) 0 (uniform_rotation_tail_start n))
  have hmag0 := uniformRotationTailMagnitude_nonneg n
  change RationalMajorant.factorialTailTerm 2 (uniformRotationTailTerms n + 1) <=
      RationalMajorant.factorialTailTerm 2 (uniformRotationTailTerms n) *
        ((1 : Rat) / 2)
    at hhalf
  calc
    RationalMajorant.factorialTailTerm 2 (uniformRotationTailTerms n + 1) <=
        uniformRotationTailMagnitude n * ((1 : Rat) / 2) := by
      simpa [uniformRotationTailMagnitude] using hhalf
    _ <= uniformRotationTailMagnitude n := by
      have hhalf_le_one : (1 : Rat) / 2 <= 1 := by native_decide
      calc
        uniformRotationTailMagnitude n * ((1 : Rat) / 2) <=
            uniformRotationTailMagnitude n * 1 :=
          Rat.mul_le_mul_of_nonneg_left hhalf_le_one hmag0
        _ = uniformRotationTailMagnitude n := by rw [Rat.mul_one]

private theorem uniform_rotation_even_term_coordinate_bounds (T : Rat)
    (hT : qabs T <= 2) (n : Nat) :
    -uniformRotationTailMagnitude n <=
        (ComplexSeries.expTerm
          (imaginaryAxis T) (uniformRotationTailTerms n)).re /\
      (ComplexSeries.expTerm
          (imaginaryAxis T) (uniformRotationTailTerms n)).re <=
        uniformRotationTailMagnitude n := by
  have hterm := even_term_coordinate_bounds T (uniformRotationTailStart + n)
  have hmono := RationalMajorant.factorialTailTerm_mono (qabs_nonneg T) hT
    (2 * (uniformRotationTailStart + n))
  constructor
  · change -RationalMajorant.factorialTailTerm 2
        (2 * (uniformRotationTailStart + n)) <=
      (ComplexSeries.expTerm
        (imaginaryAxis T) (2 * (uniformRotationTailStart + n))).re
    calc
      -RationalMajorant.factorialTailTerm 2
          (2 * (uniformRotationTailStart + n)) <=
        -RationalMajorant.factorialTailTerm (qabs T)
          (2 * (uniformRotationTailStart + n)) := Rat.neg_le_neg hmono
      _ <= (ComplexSeries.expTerm
        (imaginaryAxis T) (2 * (uniformRotationTailStart + n))).re := hterm.1
  · change (ComplexSeries.expTerm
        (imaginaryAxis T) (2 * (uniformRotationTailStart + n))).re <=
      RationalMajorant.factorialTailTerm 2
        (2 * (uniformRotationTailStart + n))
    exact Rat.le_trans hterm.2 hmono

private theorem uniform_rotation_odd_term_coordinate_bounds (T : Rat)
    (hT : qabs T <= 2) (n : Nat) :
    -uniformRotationTailMagnitude n <=
        (ComplexSeries.expTerm
          (imaginaryAxis T) (uniformRotationTailTerms n + 1)).im /\
      (ComplexSeries.expTerm
          (imaginaryAxis T) (uniformRotationTailTerms n + 1)).im <=
        uniformRotationTailMagnitude n := by
  have hterm := odd_term_coordinate_bounds T (uniformRotationTailStart + n)
  have hmono := RationalMajorant.factorialTailTerm_mono (qabs_nonneg T) hT
    (2 * (uniformRotationTailStart + n) + 1)
  have hmiddle := uniformRotationTailMagnitude_middle_le n
  constructor
  · change -RationalMajorant.factorialTailTerm 2
        (2 * (uniformRotationTailStart + n)) <=
      (ComplexSeries.expTerm
        (imaginaryAxis T) (2 * (uniformRotationTailStart + n) + 1)).im
    calc
      -RationalMajorant.factorialTailTerm 2
          (2 * (uniformRotationTailStart + n)) <=
        -RationalMajorant.factorialTailTerm 2
          (2 * (uniformRotationTailStart + n) + 1) := by
            apply Rat.neg_le_neg
            simpa [uniformRotationTailMagnitude, uniformRotationTailTerms] using hmiddle
      _ <= -RationalMajorant.factorialTailTerm (qabs T)
          (2 * (uniformRotationTailStart + n) + 1) := Rat.neg_le_neg hmono
      _ <= (ComplexSeries.expTerm
        (imaginaryAxis T) (2 * (uniformRotationTailStart + n) + 1)).im := hterm.1
  · change (ComplexSeries.expTerm
        (imaginaryAxis T) (2 * (uniformRotationTailStart + n) + 1)).im <=
      RationalMajorant.factorialTailTerm 2
        (2 * (uniformRotationTailStart + n))
    calc
      (ComplexSeries.expTerm
          (imaginaryAxis T) (2 * (uniformRotationTailStart + n) + 1)).im <=
        RationalMajorant.factorialTailTerm (qabs T)
          (2 * (uniformRotationTailStart + n) + 1) := hterm.2
      _ <= RationalMajorant.factorialTailTerm 2
          (2 * (uniformRotationTailStart + n) + 1) := hmono
      _ <= RationalMajorant.factorialTailTerm 2
          (2 * (uniformRotationTailStart + n)) := by
        simpa [uniformRotationTailMagnitude, uniformRotationTailTerms] using hmiddle

private theorem uniform_rotation_even_term_im_eq_zero (T : Rat) (n : Nat) :
    (ComplexSeries.expTerm
      (imaginaryAxis T) (uniformRotationTailTerms n)).im = 0 := by
  change (ComplexSeries.expTerm
    (imaginaryAxis T) (2 * (uniformRotationTailStart + n))).im = 0
  rw [expTerm_imaginary_even]

private theorem uniform_rotation_odd_term_re_eq_zero (T : Rat) (n : Nat) :
    (ComplexSeries.expTerm
      (imaginaryAxis T) (uniformRotationTailTerms n + 1)).re = 0 := by
  change (ComplexSeries.expTerm
    (imaginaryAxis T) (2 * (uniformRotationTailStart + n) + 1)).re = 0
  rw [expTerm_imaginary_odd]

private theorem uniformRotationCenter_step_re_bounds (T : Rat)
    (hT : qabs T <= 2) (n : Nat) :
    -uniformRotationTailMagnitude n <=
        (uniformRotationCenter T (n + 1)).re - (uniformRotationCenter T n).re /\
      (uniformRotationCenter T (n + 1)).re - (uniformRotationCenter T n).re <=
        uniformRotationTailMagnitude n := by
  have hcenter := uniformRotationCenter_succ T n
  have heven := uniform_rotation_even_term_coordinate_bounds T hT n
  have hoddzero := uniform_rotation_odd_term_re_eq_zero T n
  rw [hcenter]
  change -uniformRotationTailMagnitude n <=
      ((uniformRotationCenter T n).re +
        (ComplexSeries.expTerm (imaginaryAxis T) (uniformRotationTailTerms n)).re +
          (ComplexSeries.expTerm (imaginaryAxis T) (uniformRotationTailTerms n + 1)).re) -
        (uniformRotationCenter T n).re /\
    ((uniformRotationCenter T n).re +
        (ComplexSeries.expTerm (imaginaryAxis T) (uniformRotationTailTerms n)).re +
          (ComplexSeries.expTerm (imaginaryAxis T) (uniformRotationTailTerms n + 1)).re) -
        (uniformRotationCenter T n).re <= uniformRotationTailMagnitude n
  rw [hoddzero]
  grind [Rat.sub_eq_add_neg]

private theorem uniformRotationCenter_step_im_bounds (T : Rat)
    (hT : qabs T <= 2) (n : Nat) :
    -uniformRotationTailMagnitude n <=
        (uniformRotationCenter T (n + 1)).im - (uniformRotationCenter T n).im /\
      (uniformRotationCenter T (n + 1)).im - (uniformRotationCenter T n).im <=
        uniformRotationTailMagnitude n := by
  have hcenter := uniformRotationCenter_succ T n
  have hodd := uniform_rotation_odd_term_coordinate_bounds T hT n
  have hevenzero := uniform_rotation_even_term_im_eq_zero T n
  rw [hcenter]
  change -uniformRotationTailMagnitude n <=
      ((uniformRotationCenter T n).im +
        (ComplexSeries.expTerm (imaginaryAxis T) (uniformRotationTailTerms n)).im +
          (ComplexSeries.expTerm (imaginaryAxis T) (uniformRotationTailTerms n + 1)).im) -
        (uniformRotationCenter T n).im /\
    ((uniformRotationCenter T n).im +
        (ComplexSeries.expTerm (imaginaryAxis T) (uniformRotationTailTerms n)).im +
          (ComplexSeries.expTerm (imaginaryAxis T) (uniformRotationTailTerms n + 1)).im) -
        (uniformRotationCenter T n).im <= uniformRotationTailMagnitude n
  rw [hevenzero]
  grind [Rat.sub_eq_add_neg]

theorem uniformRotationBox_width (T : Rat) (n : Nat) :
    (uniformRotationBox T n).width = 2 * uniformRotationTailRadius n := by
  unfold uniformRotationBox QBox.width
  dsimp
  grind [Rat.sub_eq_add_neg]

theorem uniformRotationBox_height (T : Rat) (n : Nat) :
    (uniformRotationBox T n).height = 2 * uniformRotationTailRadius n := by
  unfold uniformRotationBox QBox.height
  dsimp
  grind [Rat.sub_eq_add_neg]

private theorem uniformRotationBox_ordered (T : Rat) (n : Nat) :
    0 <= (uniformRotationBox T n).width /\
      0 <= (uniformRotationBox T n).height := by
  have hmag0 := uniformRotationTailMagnitude_nonneg n
  rw [uniformRotationBox_width, uniformRotationBox_height]
  unfold uniformRotationTailRadius
  constructor <;>
    exact Rat.mul_nonneg (by native_decide)
      (Rat.mul_nonneg (by native_decide) hmag0)

private theorem uniformRotationBox_nested_step (T : Rat)
    (hT : qabs T <= 2) (n : Nat) :
    QBox.NestedIn (uniformRotationBox T (n + 1)) (uniformRotationBox T n) := by
  have hre := uniformRotationCenter_step_re_bounds T hT n
  have him := uniformRotationCenter_step_im_bounds T hT n
  have hdrop := uniformRotationTailRadius_drop_majorizes n
  unfold QBox.NestedIn uniformRotationBox
  dsimp
  constructor
  · constructor <;> grind [Rat.sub_eq_add_neg]
  · constructor <;> grind [Rat.sub_eq_add_neg]

private theorem uniformRotationBox_nested (T : Rat) (hT : qabs T <= 2) :
    forall n m : Nat, n <= m ->
      QBox.NestedIn (uniformRotationBox T m) (uniformRotationBox T n)
  | n, 0, hnm => by
      have hn : n = 0 := by omega
      subst n
      exact ⟨QComplex.le_refl _, QComplex.le_refl _⟩
  | n, m + 1, hnm => by
      by_cases hlast : n = m + 1
      · subst n
        exact ⟨QComplex.le_refl _, QComplex.le_refl _⟩
      · have hnm' : n <= m := by omega
        exact qbox_nested_trans
          (uniformRotationBox_nested_step T hT m)
          (uniformRotationBox_nested T hT n m hnm')

/-- At one common factorial stage, changing the rational input by at most
`eps` only widens the rotation box by `16 * eps` in each coordinate. -/
theorem uniformRotationBox_contained_expand_of_input_near (T U eps : Rat)
    (hT : qabs T <= 2) (hU : qabs U <= 2) (n : Nat)
    (hnear : qabs (T - U) <= eps) :
    QBox.NestedIn (uniformRotationBox T n)
      (QBox.expand (uniformRotationBox U n) (16 * eps)) := by
  have hcenter := uniformRotationCenter_input_lipschitz T U hT hU n
  have hfactor : 16 * qabs (T - U) <= 16 * eps :=
    Rat.mul_le_mul_of_nonneg_left hnear (by native_decide)
  have hreupper : (uniformRotationCenter T n).re -
      (uniformRotationCenter U n).re <= 16 * eps :=
    Rat.le_trans (self_le_qabs _) (Rat.le_trans hcenter.1 hfactor)
  have hrelower : -(16 * eps) <= (uniformRotationCenter T n).re -
      (uniformRotationCenter U n).re := by
    calc
      -(16 * eps) <= -qabs ((uniformRotationCenter T n).re -
          (uniformRotationCenter U n).re) := Rat.neg_le_neg
            (Rat.le_trans hcenter.1 hfactor)
      _ <= (uniformRotationCenter T n).re -
          (uniformRotationCenter U n).re := neg_qabs_le_self _
  have himupper : (uniformRotationCenter T n).im -
      (uniformRotationCenter U n).im <= 16 * eps :=
    Rat.le_trans (self_le_qabs _) (Rat.le_trans hcenter.2 hfactor)
  have himlower : -(16 * eps) <= (uniformRotationCenter T n).im -
      (uniformRotationCenter U n).im := by
    calc
      -(16 * eps) <= -qabs ((uniformRotationCenter T n).im -
          (uniformRotationCenter U n).im) := Rat.neg_le_neg
            (Rat.le_trans hcenter.2 hfactor)
      _ <= (uniformRotationCenter T n).im -
          (uniformRotationCenter U n).im := neg_qabs_le_self _
  unfold QBox.NestedIn QBox.expand uniformRotationBox
  dsimp
  constructor
  · constructor <;> grind [Rat.sub_eq_add_neg]
  · constructor <;> grind [Rat.sub_eq_add_neg]

/-- A later finite rotation prefix at a nearby bounded rational input fits in
the earlier box after the same explicit input-error enlargement.  This is the
finite-prefix Cauchy certificate used for represented-angle evaluation. -/
theorem uniformRotationBox_future_contained_expand_of_input_near
    (T U eps : Rat) (hT : qabs T <= 2) (hU : qabs U <= 2)
    (k n : Nat) (hkn : k <= n) (hnear : qabs (T - U) <= eps) :
    QBox.NestedIn (uniformRotationBox T n)
      (QBox.expand (uniformRotationBox U k) (16 * eps)) := by
  apply QBox.nested_trans (uniformRotationBox_nested T hT k n hkn)
  exact uniformRotationBox_contained_expand_of_input_near T U eps hT hU k hnear

/-- Uniform bounded-input boxes have exactly the same coordinate widths as
the ordinary rational-input evaluator at the endpoint 2. This reuses the
already checked geometric width modulus while leaving the centers free to
vary with the bounded rational input. -/
private theorem uniformRotationBox_width_eq_rotationBox_two (T : Rat) (n : Nat) :
    (uniformRotationBox T n).width = (rotationBox 2 n).width := by
  rw [uniformRotationBox_width, rotationBox_width]
  unfold uniformRotationTailRadius rotationTailRadius
    uniformRotationTailMagnitude rotationTailMagnitude
    uniformRotationTailTerms rotationTailTerms
    uniformRotationTailStart rotationTailStart
  have hqabs : qabs (2 : Rat) = 2 := by native_decide
  rw [hqabs]

private theorem uniformRotationBox_height_eq_rotationBox_two (T : Rat) (n : Nat) :
    (uniformRotationBox T n).height = (rotationBox 2 n).height := by
  rw [uniformRotationBox_height, rotationBox_height]
  unfold uniformRotationTailRadius rotationTailRadius
    uniformRotationTailMagnitude rotationTailMagnitude
    uniformRotationTailTerms rotationTailTerms
    uniformRotationTailStart rotationTailStart
  have hqabs : qabs (2 : Rat) = 2 := by native_decide
  rw [hqabs]

theorem uniformRotationBox_widths_shrink (T : Rat) :
    ComplexRaw.WidthsShrinkToZero (uniformRotationBox T) := by
  intro eps
  obtain ⟨N, hN⟩ := rotationBox_widths_shrink 2 eps
  refine ⟨N, ?_⟩
  intro n hn
  have h := hN n hn
  constructor
  · rw [uniformRotationBox_width_eq_rotationBox_two]
    exact h.1
  · rw [uniformRotationBox_height_eq_rotationBox_two]
    exact h.2

/-- The rotation-series evaluator with one common tail schedule for all
rational inputs satisfying the bound qabs T <= 2. It is the rational
building block for represented-angle evaluation. -/
def uniformRotationExpRaw (T : Rat) : ComplexRaw where
  compute := uniformRotationBox T

theorem uniformRotationExpRaw_compute (T : Rat) (n : Nat) :
    (uniformRotationExpRaw T).compute n = uniformRotationBox T n := rfl

theorem uniformRotationExpRaw_valid (T : Rat) (hT : qabs T <= 2) :
    (uniformRotationExpRaw T).Valid := by
  unfold ComplexRaw.Valid ComplexRaw.ValidCompute uniformRotationExpRaw
  constructor
  · exact uniformRotationBox_ordered T
  · constructor
    · intro n m hnm
      have hnest := uniformRotationBox_nested T hT n m hnm
      exact ⟨hnest.1.1, hnest.2.1, hnest.1.2, hnest.2.2⟩
    · exact uniformRotationBox_widths_shrink T

/-- Certified abstract real handles for the two rational-input rotation
coordinates. -/
def rotationCos (T : Rat) : Real :=
  Real.ofRaw (rotationCosRaw T) (rotationCosRaw_valid T)

def rotationSin (T : Rat) : Real :=
  Real.ofRaw (rotationSinRaw T) (rotationSinRaw_valid T)

end RotationSeries

end ComputableAnalysis
