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

theorem fourPointFourierSum_period_four (mode : Nat) :
    fourPointFourierSum (mode + 4) = fourPointFourierSum mode := by
  have hfour : QComplex.natPow RotationSeries.imaginaryUnit 4 =
      QComplex.one := by
    native_decide
  have hshift : forall (n k : Nat),
      QComplex.natPow RotationSeries.imaginaryUnit (n + 4 * k) =
        QComplex.natPow RotationSeries.imaginaryUnit n := by
    intro n k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [show n + 4 * (k + 1) = (n + 4 * k) + 4 by omega,
          QComplex.natPow_add, hfour, QComplex.mul_one_cert, ih]
  unfold fourPointFourierSum
  have h0 : QComplex.natPow RotationSeries.imaginaryUnit ((mode + 4) * 0) =
      QComplex.natPow RotationSeries.imaginaryUnit (mode * 0) := by
    simp
  have h1 : QComplex.natPow RotationSeries.imaginaryUnit ((mode + 4) * 1) =
      QComplex.natPow RotationSeries.imaginaryUnit (mode * 1) := by
    simpa [Nat.add_mul] using hshift (mode * 1) 1
  have h2 : QComplex.natPow RotationSeries.imaginaryUnit ((mode + 4) * 2) =
      QComplex.natPow RotationSeries.imaginaryUnit (mode * 2) := by
    simpa [Nat.add_mul] using hshift (mode * 2) 2
  have h3 : QComplex.natPow RotationSeries.imaginaryUnit ((mode + 4) * 3) =
      QComplex.natPow RotationSeries.imaginaryUnit (mode * 3) := by
    simpa [Nat.add_mul] using hshift (mode * 3) 3
  rw [h0, h1, h2, h3]

theorem fourPointFourierSum_period_four_mul (mode k : Nat) :
    fourPointFourierSum (mode + 4 * k) = fourPointFourierSum mode := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [show mode + 4 * (k + 1) = (mode + 4 * k) + 4 by
        simp [Nat.mul_succ, Nat.add_assoc]]
      rw [fourPointFourierSum_period_four, ih]

theorem fourPointFourierSum_four_residue (k : Nat) :
    fourPointFourierSum (4 * k) = { re := 4, im := 0 } /\
      fourPointFourierSum (1 + 4 * k) = QComplex.zero /\
      fourPointFourierSum (2 + 4 * k) = QComplex.zero /\
      fourPointFourierSum (3 + 4 * k) = QComplex.zero := by
  have h0 := fourPointFourierSum_period_four_mul 0 k
  have h1 := fourPointFourierSum_period_four_mul 1 k
  have h2 := fourPointFourierSum_period_four_mul 2 k
  have h3 := fourPointFourierSum_period_four_mul 3 k
  constructor
  · simpa [fourPointFourierSum_zero_mode] using h0
  constructor
  · simpa [fourPointFourierSum_first_mode] using h1
  constructor
  · simpa [fourPointFourierSum_second_mode] using h2
  · simpa [fourPointFourierSum_third_mode] using h3

theorem quarterTurn_natPow_period_four (n : Nat) :
    QComplex.natPow RotationSeries.imaginaryUnit (n + 4) =
      QComplex.natPow RotationSeries.imaginaryUnit n := by
  have hfour : QComplex.natPow RotationSeries.imaginaryUnit 4 =
      QComplex.one := by
    native_decide
  rw [QComplex.natPow_add, hfour, QComplex.mul_one_cert]

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

/-! The concrete certificate above is an instance of a reusable finite
Parseval identity.  The statement is deliberately only four-point: it is an
exact rational-coordinate transform identity, not an infinite Fourier
convergence theorem. -/

def fourPointFourierTransform (x₀ x₁ x₂ x₃ : Rat) (mode : Nat) : QComplex :=
  QComplex.add
    (QComplex.add
      (QComplex.add
        (QComplex.mul (QComplex.ofRat x₀)
          (QComplex.natPow RotationSeries.imaginaryUnit (mode * 0)))
        (QComplex.mul (QComplex.ofRat x₁)
          (QComplex.natPow RotationSeries.imaginaryUnit (mode * 1))))
      (QComplex.mul (QComplex.ofRat x₂)
        (QComplex.natPow RotationSeries.imaginaryUnit (mode * 2))))
    (QComplex.mul (QComplex.ofRat x₃)
      (QComplex.natPow RotationSeries.imaginaryUnit (mode * 3)))

/-! The transform is linear over the rational sample space.  These laws are
the finite algebraic core used when a stage computation is decomposed into
Fourier modes. -/

theorem fourPointFourierTransform_add
    (x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃ : Rat) (mode : Nat) :
    fourPointFourierTransform (x₀ + y₀) (x₁ + y₁) (x₂ + y₂) (x₃ + y₃) mode =
      QComplex.add
        (fourPointFourierTransform x₀ x₁ x₂ x₃ mode)
        (fourPointFourierTransform y₀ y₁ y₂ y₃ mode) := by
  simp [fourPointFourierTransform, QComplex.ofRat, QComplex.mul,
    QComplex.add]
  constructor <;> grind [Rat.add_assoc, Rat.add_comm, Rat.add_left_comm,
    Rat.mul_add, Rat.add_mul]

theorem fourPointFourierTransform_scale
    (r x₀ x₁ x₂ x₃ : Rat) (mode : Nat) :
    fourPointFourierTransform (r * x₀) (r * x₁) (r * x₂) (r * x₃) mode =
      QComplex.scaleRat r
        (fourPointFourierTransform x₀ x₁ x₂ x₃ mode) := by
  simp [fourPointFourierTransform, QComplex.ofRat, QComplex.mul,
    QComplex.add, QComplex.scaleRat]
  constructor <;> grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_add]

theorem fourPointFourierTransform_constant_modes (c : Rat) :
    fourPointFourierTransform c c c c 0 = { re := 4 * c, im := 0 } /\
    fourPointFourierTransform c c c c 1 = QComplex.zero /\
    fourPointFourierTransform c c c c 2 = QComplex.zero /\
    fourPointFourierTransform c c c c 3 = QComplex.zero := by
  simp [fourPointFourierTransform, QComplex.natPow,
    RotationSeries.imaginaryUnit, QComplex.ofRat, QComplex.mul,
    QComplex.add, QComplex.one, QComplex.zero]
  grind [Rat.add_assoc, Rat.add_comm, Rat.mul_add, Rat.add_mul,
    Rat.mul_assoc, Rat.mul_comm]

theorem fourPointFourierTransform_modes (x₀ x₁ x₂ x₃ : Rat) :
    fourPointFourierTransform x₀ x₁ x₂ x₃ 0 =
        { re := x₀ + x₁ + x₂ + x₃, im := 0 } /\
    fourPointFourierTransform x₀ x₁ x₂ x₃ 1 =
        { re := x₀ - x₂, im := x₁ - x₃ } /\
    fourPointFourierTransform x₀ x₁ x₂ x₃ 2 =
        { re := x₀ - x₁ + x₂ - x₃, im := 0 } /\
    fourPointFourierTransform x₀ x₁ x₂ x₃ 3 =
        { re := x₀ - x₂, im := x₃ - x₁ } := by
  simp [fourPointFourierTransform, QComplex.natPow,
    RotationSeries.imaginaryUnit, QComplex.ofRat, QComplex.mul,
    QComplex.add, QComplex.one, QComplex.normSq]
  grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm,
    Rat.mul_assoc, Rat.mul_comm, Rat.mul_add, Rat.add_mul]

/-! The four-point cyclic convolution is the finite product operation whose
Fourier transform is coefficientwise multiplication.  It is stated in
rational coordinates so that this remains an exact computable identity. -/
def fourPointConvolution₀
    (x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃ : Rat) : Rat :=
  x₀ * y₀ + x₁ * y₃ + x₂ * y₂ + x₃ * y₁

def fourPointConvolution₁
    (x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃ : Rat) : Rat :=
  x₀ * y₁ + x₁ * y₀ + x₂ * y₃ + x₃ * y₂

def fourPointConvolution₂
    (x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃ : Rat) : Rat :=
  x₀ * y₂ + x₁ * y₁ + x₂ * y₀ + x₃ * y₃

def fourPointConvolution₃
    (x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃ : Rat) : Rat :=
  x₀ * y₃ + x₁ * y₂ + x₂ * y₁ + x₃ * y₀

theorem fourPointFourierTransform_cyclic_convolution
    (x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃ : Rat) :
    fourPointFourierTransform
        (fourPointConvolution₀ x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃)
        (fourPointConvolution₁ x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃)
        (fourPointConvolution₂ x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃)
        (fourPointConvolution₃ x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃) 0 =
      QComplex.mul
        (fourPointFourierTransform x₀ x₁ x₂ x₃ 0)
        (fourPointFourierTransform y₀ y₁ y₂ y₃ 0) /\
    fourPointFourierTransform
        (fourPointConvolution₀ x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃)
        (fourPointConvolution₁ x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃)
        (fourPointConvolution₂ x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃)
        (fourPointConvolution₃ x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃) 1 =
      QComplex.mul
        (fourPointFourierTransform x₀ x₁ x₂ x₃ 1)
        (fourPointFourierTransform y₀ y₁ y₂ y₃ 1) /\
    fourPointFourierTransform
        (fourPointConvolution₀ x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃)
        (fourPointConvolution₁ x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃)
        (fourPointConvolution₂ x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃)
        (fourPointConvolution₃ x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃) 2 =
      QComplex.mul
        (fourPointFourierTransform x₀ x₁ x₂ x₃ 2)
        (fourPointFourierTransform y₀ y₁ y₂ y₃ 2) /\
    fourPointFourierTransform
        (fourPointConvolution₀ x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃)
        (fourPointConvolution₁ x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃)
        (fourPointConvolution₂ x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃)
        (fourPointConvolution₃ x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃) 3 =
      QComplex.mul
        (fourPointFourierTransform x₀ x₁ x₂ x₃ 3)
        (fourPointFourierTransform y₀ y₁ y₂ y₃ 3) := by
  rcases fourPointFourierTransform_modes x₀ x₁ x₂ x₃ with
    ⟨hx₀, hx₁, hx₂, hx₃⟩
  rcases fourPointFourierTransform_modes y₀ y₁ y₂ y₃ with
    ⟨hy₀, hy₁, hy₂, hy₃⟩
  rcases fourPointFourierTransform_modes
      (fourPointConvolution₀ x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃)
      (fourPointConvolution₁ x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃)
      (fourPointConvolution₂ x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃)
      (fourPointConvolution₃ x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃) with
    ⟨hc₀, hc₁, hc₂, hc₃⟩
  rw [hc₀, hc₁, hc₂, hc₃, hx₀, hx₁, hx₂, hx₃, hy₀, hy₁, hy₂, hy₃]
  simp [QComplex.mul, fourPointConvolution₀, fourPointConvolution₁,
    fourPointConvolution₂, fourPointConvolution₃]
  constructor <;> grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm,
    Rat.add_left_comm, Rat.mul_assoc, Rat.mul_comm, Rat.mul_add, Rat.add_mul]

/-! The four modes also reconstruct the original four samples.  This is the
finite inverse-transform statement behind the orthogonality certificate. -/

theorem fourPointFourierTransform_reconstruct (x₀ x₁ x₂ x₃ : Rat) :
    let f₀ := fourPointFourierTransform x₀ x₁ x₂ x₃ 0
    let f₁ := fourPointFourierTransform x₀ x₁ x₂ x₃ 1
    let f₂ := fourPointFourierTransform x₀ x₁ x₂ x₃ 2
    let f₃ := fourPointFourierTransform x₀ x₁ x₂ x₃ 3
    f₀.re + f₁.re + f₂.re + f₃.re = 4 * x₀ /\
      f₀.re - f₂.re + f₁.im - f₃.im = 4 * x₁ /\
      f₀.re - f₁.re + f₂.re - f₃.re = 4 * x₂ /\
      f₀.re - f₂.re - f₁.im + f₃.im = 4 * x₃ := by
  dsimp
  rcases fourPointFourierTransform_modes x₀ x₁ x₂ x₃ with
    ⟨h₀, h₁, h₂, h₃⟩
  rw [h₀, h₁, h₂, h₃]
  grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm,
    Rat.mul_assoc, Rat.mul_comm, Rat.mul_add, Rat.add_mul]

/-! Reconstruction also gives uniqueness: no two rational sample vectors have
the same four finite Fourier coefficients.  This is the finite analogue of
uniqueness of Fourier coefficients, proved entirely by rational arithmetic. -/
theorem fourPointFourierTransform_injective
    (x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃ : Rat)
    (h₀ : fourPointFourierTransform x₀ x₁ x₂ x₃ 0 =
      fourPointFourierTransform y₀ y₁ y₂ y₃ 0)
    (h₁ : fourPointFourierTransform x₀ x₁ x₂ x₃ 1 =
      fourPointFourierTransform y₀ y₁ y₂ y₃ 1)
    (h₂ : fourPointFourierTransform x₀ x₁ x₂ x₃ 2 =
      fourPointFourierTransform y₀ y₁ y₂ y₃ 2)
    (h₃ : fourPointFourierTransform x₀ x₁ x₂ x₃ 3 =
      fourPointFourierTransform y₀ y₁ y₂ y₃ 3) :
    x₀ = y₀ ∧ x₁ = y₁ ∧ x₂ = y₂ ∧ x₃ = y₃ := by
  have h₀re := congrArg QComplex.re h₀
  have h₁re := congrArg QComplex.re h₁
  have h₁im := congrArg QComplex.im h₁
  have h₂re := congrArg QComplex.re h₂
  have h₃im := congrArg QComplex.im h₃
  rcases fourPointFourierTransform_modes x₀ x₁ x₂ x₃ with
    ⟨hx₀, hx₁, hx₂, hx₃⟩
  rcases fourPointFourierTransform_modes y₀ y₁ y₂ y₃ with
    ⟨hy₀, hy₁, hy₂, hy₃⟩
  rw [hx₀, hy₀] at h₀re
  rw [hx₁, hy₁] at h₁re h₁im
  rw [hx₂, hy₂] at h₂re
  rw [hx₃, hy₃] at h₃im
  grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm,
    Rat.mul_assoc, Rat.mul_comm, Rat.mul_add, Rat.add_mul]

theorem fourPointFourierTransform_parseval (x₀ x₁ x₂ x₃ : Rat) :
    QComplex.normSq (fourPointFourierTransform x₀ x₁ x₂ x₃ 0) +
        QComplex.normSq (fourPointFourierTransform x₀ x₁ x₂ x₃ 1) +
        QComplex.normSq (fourPointFourierTransform x₀ x₁ x₂ x₃ 2) +
        QComplex.normSq (fourPointFourierTransform x₀ x₁ x₂ x₃ 3) =
      4 * (x₀ ^ 2 + x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2) := by
  simp [fourPointFourierTransform, QComplex.natPow,
    RotationSeries.imaginaryUnit, QComplex.ofRat, QComplex.mul,
    QComplex.add, QComplex.one, QComplex.normSq]
  grind [Rat.pow_succ, Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm,
    Rat.mul_assoc, Rat.mul_comm, Rat.mul_add, Rat.add_mul]

/-! The same four-point transform over arbitrary rational-complex samples.
This is the first complex-valued Parseval boundary: every operation is still
finite rational-coordinate arithmetic, but the samples are no longer
restricted to the real axis. -/

def fourPointComplexFourierTransform
    (x₀ x₁ x₂ x₃ : QComplex) (mode : Nat) : QComplex :=
  QComplex.add
    (QComplex.add
      (QComplex.add
        (QComplex.mul x₀
          (QComplex.natPow RotationSeries.imaginaryUnit (mode * 0)))
        (QComplex.mul x₁
          (QComplex.natPow RotationSeries.imaginaryUnit (mode * 1))))
      (QComplex.mul x₂
        (QComplex.natPow RotationSeries.imaginaryUnit (mode * 2))))
    (QComplex.mul x₃
      (QComplex.natPow RotationSeries.imaginaryUnit (mode * 3)))

theorem fourPointComplexFourierTransform_parseval
    (x₀ x₁ x₂ x₃ : QComplex) :
    QComplex.normSq (fourPointComplexFourierTransform x₀ x₁ x₂ x₃ 0) +
        QComplex.normSq (fourPointComplexFourierTransform x₀ x₁ x₂ x₃ 1) +
        QComplex.normSq (fourPointComplexFourierTransform x₀ x₁ x₂ x₃ 2) +
        QComplex.normSq (fourPointComplexFourierTransform x₀ x₁ x₂ x₃ 3) =
      4 * (QComplex.normSq x₀ + QComplex.normSq x₁ +
        QComplex.normSq x₂ + QComplex.normSq x₃) := by
  cases x₀
  cases x₁
  cases x₂
  cases x₃
  simp [fourPointComplexFourierTransform, QComplex.natPow,
    RotationSeries.imaginaryUnit, QComplex.mul, QComplex.add,
    QComplex.one, QComplex.zero, QComplex.normSq]
  grind [Rat.add_assoc, Rat.add_comm, Rat.add_left_comm,
    Rat.mul_assoc, Rat.mul_comm, Rat.mul_add, Rat.add_mul,
    Rat.sub_eq_add_neg]

theorem fourPointComplexFourierTransform_reconstruct
    (x₀ x₁ x₂ x₃ : QComplex) :
    let f₀ := fourPointComplexFourierTransform x₀ x₁ x₂ x₃ 0
    let f₁ := fourPointComplexFourierTransform x₀ x₁ x₂ x₃ 1
    let f₂ := fourPointComplexFourierTransform x₀ x₁ x₂ x₃ 2
    let f₃ := fourPointComplexFourierTransform x₀ x₁ x₂ x₃ 3
    QComplex.add (QComplex.add f₀ f₁) (QComplex.add f₂ f₃) =
        QComplex.scaleRat 4 x₀ /\
      QComplex.add
          (QComplex.add f₀
            (QComplex.mul (QComplex.scaleRat (-1) RotationSeries.imaginaryUnit) f₁))
          (QComplex.add (QComplex.scaleRat (-1) f₂)
            (QComplex.mul RotationSeries.imaginaryUnit f₃)) =
        QComplex.scaleRat 4 x₁ /\
      QComplex.add (QComplex.add f₀ (QComplex.scaleRat (-1) f₁))
          (QComplex.add f₂ (QComplex.scaleRat (-1) f₃)) =
        QComplex.scaleRat 4 x₂ /\
      QComplex.add
          (QComplex.add f₀
            (QComplex.mul RotationSeries.imaginaryUnit f₁))
          (QComplex.add (QComplex.scaleRat (-1) f₂)
            (QComplex.mul (QComplex.scaleRat (-1) RotationSeries.imaginaryUnit) f₃)) =
        QComplex.scaleRat 4 x₃ := by
  dsimp
  cases x₀
  cases x₁
  cases x₂
  cases x₃
  simp [fourPointComplexFourierTransform, QComplex.natPow,
    RotationSeries.imaginaryUnit, QComplex.mul, QComplex.add,
    QComplex.scaleRat, QComplex.one, QComplex.zero]
  grind [Rat.add_assoc, Rat.add_comm, Rat.add_left_comm,
    Rat.mul_assoc, Rat.mul_comm, Rat.mul_add, Rat.add_mul,
    Rat.sub_eq_add_neg]

/-! Real rational samples have the usual finite conjugate symmetry: the first
and third modes pair up, while the zero and Nyquist modes are self-conjugate.
This is stated directly in rational-complex coordinates. -/
theorem fourPointFourierTransform_conjugate_symmetry
    (x₀ x₁ x₂ x₃ : Rat) :
    QComplex.conj (fourPointFourierTransform x₀ x₁ x₂ x₃ 1) =
        fourPointFourierTransform x₀ x₁ x₂ x₃ 3 /\
      QComplex.conj (fourPointFourierTransform x₀ x₁ x₂ x₃ 0) =
        fourPointFourierTransform x₀ x₁ x₂ x₃ 0 /\
      QComplex.conj (fourPointFourierTransform x₀ x₁ x₂ x₃ 2) =
        fourPointFourierTransform x₀ x₁ x₂ x₃ 2 := by
  rcases fourPointFourierTransform_modes x₀ x₁ x₂ x₃ with
    ⟨h₀, h₁, h₂, h₃⟩
  rw [h₁, h₃, h₀, h₂]
  simp [QComplex.conj]
  grind [Rat.sub_eq_add_neg]

end ComputableAnalysis
