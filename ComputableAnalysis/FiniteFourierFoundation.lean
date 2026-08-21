import ComputableAnalysis.FiniteFourierCertificate

/-!
# Finite Fourier foundation

This file lifts the four-point example to an arbitrary finite list of
rational-complex samples.  It is still a finite computation: no infinite
series, topology, or completed real number is hidden in the definitions.
The root-of-unity identities needed for orthogonality are supplied separately
by a certificate, so this interface can later be instantiated at each finite
stage of a computable Fourier algorithm.
-/

namespace ComputableAnalysis

def finiteFourierSumAux (root : QComplex) (mode : Nat) : Nat → List QComplex → QComplex
  | _, [] => QComplex.zero
  | k, x :: xs =>
      QComplex.add
        (QComplex.mul x (QComplex.natPow root (mode * k)))
        (finiteFourierSumAux root mode (k + 1) xs)

def finiteFourierSum (root : QComplex) (mode : Nat) (samples : List QComplex) : QComplex :=
  finiteFourierSumAux root mode 0 samples

def qcomplexListAdd : List QComplex → List QComplex → List QComplex
  | x :: xs, y :: ys => QComplex.add x y :: qcomplexListAdd xs ys
  | [], ys => ys
  | xs, [] => xs

def qcomplexListScale (r : Rat) : List QComplex → List QComplex
  | [] => []
  | x :: xs => QComplex.scaleRat r x :: qcomplexListScale r xs

def qcomplexListConj : List QComplex → List QComplex
  | [] => []
  | x :: xs => QComplex.conj x :: qcomplexListConj xs

def qcomplexListSum : List QComplex → QComplex
  | [] => QComplex.zero
  | x :: xs => QComplex.add x (qcomplexListSum xs)

private theorem qcomplex_add_four_rearrange
    (a b c d : QComplex) :
    QComplex.add (QComplex.add a b) (QComplex.add c d) =
      QComplex.add (QComplex.add a c) (QComplex.add b d) := by
  cases a
  cases b
  cases c
  cases d
  simp [QComplex.add]
  constructor <;> grind [Rat.add_assoc, Rat.add_comm, Rat.add_left_comm]

private theorem qcomplex_scale_zero (r : Rat) :
    QComplex.scaleRat r QComplex.zero = QComplex.zero := by
  simp [QComplex.scaleRat, QComplex.zero]

private theorem qcomplex_scale_zero_any (z : QComplex) :
    QComplex.scaleRat 0 z = QComplex.zero := by
  cases z
  simp [QComplex.scaleRat, QComplex.zero]

private theorem qcomplex_add_zero (z : QComplex) :
    QComplex.add z QComplex.zero = z := by
  cases z
  simp [QComplex.add, QComplex.zero]
  constructor <;> grind

private theorem qcomplex_zero_add (z : QComplex) :
    QComplex.add QComplex.zero z = z := by
  cases z
  simp [QComplex.add, QComplex.zero]
  constructor <;> grind

private theorem qcomplex_add_assoc (a b c : QComplex) :
    QComplex.add a (QComplex.add b c) =
      QComplex.add (QComplex.add a b) c := by
  cases a
  cases b
  cases c
  simp [QComplex.add]
  constructor <;> grind [Rat.add_assoc]

private theorem qcomplex_scale_mul
    (r : Rat) (x z : QComplex) :
    QComplex.mul (QComplex.scaleRat r x) z =
      QComplex.scaleRat r (QComplex.mul x z) := by
  cases x
  cases z
  simp [QComplex.scaleRat, QComplex.mul]
  constructor <;> grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_add,
    Rat.add_mul]

private theorem qcomplex_scale_add
    (r : Rat) (x y : QComplex) :
    QComplex.scaleRat r (QComplex.add x y) =
      QComplex.add (QComplex.scaleRat r x) (QComplex.scaleRat r y) := by
  cases x
  cases y
  simp [QComplex.scaleRat, QComplex.add]
  constructor <;> grind [Rat.mul_add]

private theorem qcomplex_mul_comm (x y : QComplex) :
    QComplex.mul x y = QComplex.mul y x := by
  cases x
  cases y
  simp [QComplex.mul]
  constructor <;> grind [Rat.add_comm, Rat.mul_comm]

private theorem qcomplex_zero_mul (z : QComplex) :
    QComplex.mul QComplex.zero z = QComplex.zero := by
  cases z
  simp [QComplex.mul, QComplex.zero]
  constructor <;> grind

private theorem qcomplex_natPow_one (n : Nat) :
    QComplex.natPow QComplex.one n = QComplex.one := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [QComplex.natPow_succ, ih, QComplex.mul_one_cert]

theorem finiteFourierSum_empty (root : QComplex) (mode : Nat) :
    finiteFourierSum root mode [] = QComplex.zero := by
  rfl

theorem finiteFourierSum_cons (root : QComplex) (mode k : Nat)
    (x : QComplex) (xs : List QComplex) :
    finiteFourierSumAux root mode k (x :: xs) =
      QComplex.add
        (QComplex.mul x (QComplex.natPow root (mode * k)))
        (finiteFourierSumAux root mode (k + 1) xs) := by
  rfl

theorem finiteFourierSum_prepend_zero
    (root : QComplex) (mode : Nat) (xs : List QComplex) :
    finiteFourierSum root mode (QComplex.zero :: xs) =
      finiteFourierSumAux root mode 1 xs := by
  simp only [finiteFourierSum, finiteFourierSumAux]
  rw [qcomplex_zero_mul, qcomplex_zero_add]

theorem finiteFourierSum_aux_add
    (root : QComplex) (mode k : Nat)
    (xs ys : List QComplex) :
    finiteFourierSumAux root mode k (qcomplexListAdd xs ys) =
      QComplex.add
        (finiteFourierSumAux root mode k xs)
        (finiteFourierSumAux root mode k ys) := by
  induction xs generalizing ys k with
  | nil =>
      simp only [qcomplexListAdd, finiteFourierSumAux]
      exact (qcomplex_zero_add _).symm
  | cons x xs ih =>
      cases ys with
      | nil =>
          simp only [qcomplexListAdd, finiteFourierSumAux]
          exact (qcomplex_add_zero _).symm
      | cons y ys =>
          simp only [qcomplexListAdd, finiteFourierSumAux]
          rw [ih (ys := ys) (k := k + 1)]
          rw [QComplex.add_mul_cert]
          exact qcomplex_add_four_rearrange _ _ _ _

theorem finiteFourierSum_add
    (root : QComplex) (mode : Nat) (xs ys : List QComplex) :
    finiteFourierSum root mode (qcomplexListAdd xs ys) =
      QComplex.add (finiteFourierSum root mode xs)
        (finiteFourierSum root mode ys) := by
  exact finiteFourierSum_aux_add root mode 0 xs ys

theorem finiteFourierSum_aux_append
    (root : QComplex) (mode k : Nat)
    (xs ys : List QComplex) :
    finiteFourierSumAux root mode k (xs ++ ys) =
      QComplex.add
        (finiteFourierSumAux root mode k xs)
        (finiteFourierSumAux root mode (k + xs.length) ys) := by
  induction xs generalizing k with
  | nil =>
      simp only [List.nil_append, List.length_nil, Nat.add_zero,
        finiteFourierSumAux]
      exact (qcomplex_zero_add _).symm
  | cons x xs ih =>
      simp only [List.cons_append, List.length_cons, finiteFourierSumAux]
      rw [ih (k := k + 1)]
      have hindex : k + 1 + xs.length = k + (xs.length + 1) := by omega
      rw [hindex]
      exact qcomplex_add_assoc _ _ _

theorem finiteFourierSum_append
    (root : QComplex) (mode : Nat)
    (xs ys : List QComplex) :
    finiteFourierSum root mode (xs ++ ys) =
      QComplex.add
        (finiteFourierSum root mode xs)
        (finiteFourierSumAux root mode xs.length ys) := by
  simpa [finiteFourierSum] using
    (finiteFourierSum_aux_append root mode 0 xs ys)

/-! Shifting the sample index contributes one common phase factor.  This is
the finite block law used when a longer stage is assembled from translated
blocks; it is purely a rational-complex identity. -/
theorem finiteFourierSum_aux_phase
    (root : QComplex) (mode k : Nat) (xs : List QComplex) :
    finiteFourierSumAux root mode k xs =
      QComplex.mul
        (QComplex.natPow root (mode * k))
        (finiteFourierSumAux root mode 0 xs) := by
  induction xs generalizing k with
  | nil =>
      simp only [finiteFourierSumAux]
      rw [qcomplex_mul_comm]
      exact (qcomplex_zero_mul _).symm
  | cons x xs ih =>
      simp only [finiteFourierSumAux]
      rw [ih (k := k + 1)]
      have hindex : mode * (k + 1) = mode * k + mode := by
        rw [Nat.mul_add, Nat.mul_one]
      rw [hindex, QComplex.natPow_add]
      rw [ih (k := 1)]
      simp [QComplex.natPow, QComplex.mul_one_cert]
      rw [QComplex.mul_add_cert]
      rw [qcomplex_mul_comm x (QComplex.natPow root (mode * k))]
      rw [QComplex.mul_assoc_cert]

theorem finiteFourierSum_phase
    (root : QComplex) (mode : Nat) (xs : List QComplex) (k : Nat) :
    finiteFourierSumAux root mode k xs =
      QComplex.mul
        (QComplex.natPow root (mode * k))
        (finiteFourierSum root mode xs) := by
  simpa [finiteFourierSum] using
    (finiteFourierSum_aux_phase root mode k xs)

theorem finiteFourierSum_append_phase
    (root : QComplex) (mode : Nat)
    (xs ys : List QComplex) :
    finiteFourierSum root mode (xs ++ ys) =
      QComplex.add
        (finiteFourierSum root mode xs)
        (QComplex.mul
          (QComplex.natPow root (mode * xs.length))
          (finiteFourierSum root mode ys)) := by
  rw [finiteFourierSum_append]
  rw [finiteFourierSum_phase root mode ys xs.length]

/-! A one-step recurrence for the finite coefficient evaluator.  The tail is
shifted by one sample, hence it carries the common phase `root^mode`.  This
is the finite algebraic law used when a computable Fourier stage appends one
new sample. -/
theorem finiteFourierSum_cons_phase
    (root : QComplex) (mode : Nat)
    (x : QComplex) (xs : List QComplex) :
    finiteFourierSum root mode (x :: xs) =
      QComplex.add x
        (QComplex.mul
          (QComplex.natPow root mode)
          (finiteFourierSum root mode xs)) := by
  rw [show x :: xs = [x] ++ xs by simp, finiteFourierSum_append_phase]
  simp [finiteFourierSum, finiteFourierSumAux, QComplex.natPow,
    QComplex.mul_one_cert]
  rw [qcomplex_add_zero]

/-! With the rational quarter-turn root, every finite sample list has the
same four-step mode periodicity as the four-point transform. -/
theorem finiteFourierSum_quarterTurn_mode_period_four
    (mode : Nat) (samples : List QComplex) :
    finiteFourierSum RotationSeries.imaginaryUnit (mode + 4) samples =
      finiteFourierSum RotationSeries.imaginaryUnit mode samples := by
  have hshift : forall (n k : Nat),
      QComplex.natPow RotationSeries.imaginaryUnit (n + 4 * k) =
        QComplex.natPow RotationSeries.imaginaryUnit n := by
    intro n k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [show n + 4 * (k + 1) = (n + 4 * k) + 4 by
          simp [Nat.mul_succ, Nat.add_assoc],
          quarterTurn_natPow_period_four, ih]
  have hphase : forall (j : Nat),
      QComplex.natPow RotationSeries.imaginaryUnit ((mode + 4) * j) =
        QComplex.natPow RotationSeries.imaginaryUnit (mode * j) := by
    intro j
    simpa [Nat.add_mul] using hshift (mode * j) j
  have haux : forall (k : Nat) (xs : List QComplex),
      finiteFourierSumAux RotationSeries.imaginaryUnit (mode + 4) k xs =
        finiteFourierSumAux RotationSeries.imaginaryUnit mode k xs := by
    intro k xs
    induction xs generalizing k with
    | nil => rfl
    | cons x xs ih =>
        simp only [finiteFourierSumAux]
        rw [hphase k, ih (k + 1)]
  exact haux 0 samples

theorem finiteFourierSum_quarterTurn_mode_period_four_mul
    (mode k : Nat) (samples : List QComplex) :
    finiteFourierSum RotationSeries.imaginaryUnit (mode + 4 * k) samples =
      finiteFourierSum RotationSeries.imaginaryUnit mode samples := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [show mode + 4 * (k + 1) = (mode + 4 * k) + 4 by
        simp [Nat.mul_succ, Nat.add_assoc]]
      rw [finiteFourierSum_quarterTurn_mode_period_four, ih]

theorem finiteFourierSum_aux_one
    (mode k : Nat) (xs : List QComplex) :
    finiteFourierSumAux QComplex.one mode k xs = qcomplexListSum xs := by
  induction xs generalizing k with
  | nil => rfl
  | cons x xs ih =>
      simp only [finiteFourierSumAux, qcomplexListSum]
      rw [qcomplex_natPow_one, QComplex.mul_one_cert, ih]

theorem finiteFourierSum_one
    (mode : Nat) (xs : List QComplex) :
    finiteFourierSum QComplex.one mode xs = qcomplexListSum xs := by
  exact finiteFourierSum_aux_one mode 0 xs

/-! The zero mode is the ordinary finite sum, independently of the chosen
root.  This is the finite analogue of the zeroth Fourier coefficient and is
the bridge used when a coefficient family is summed before taking a limit. -/
theorem finiteFourierSum_zero_mode
    (root : QComplex) (xs : List QComplex) :
    finiteFourierSum root 0 xs = qcomplexListSum xs := by
  have haux : forall k : Nat, forall ys : List QComplex,
      finiteFourierSumAux root 0 k ys = qcomplexListSum ys := by
    intro k ys
    induction ys generalizing k with
    | nil => rfl
    | cons y ys ih =>
        simp only [finiteFourierSumAux, qcomplexListSum]
        rw [ih (k := k + 1)]
        simp [QComplex.natPow, QComplex.mul_one_cert]
  exact haux 0 xs

theorem qcomplexListSum_replicate (n : Nat) (c : QComplex) :
    qcomplexListSum (List.replicate n c) =
      QComplex.scaleRat (n : Rat) c := by
  induction n with
  | zero =>
      simp [qcomplexListSum, QComplex.scaleRat, QComplex.zero]
  | succ n ih =>
      simp only [List.replicate_succ, qcomplexListSum]
      rw [ih]
      cases c
      simp [QComplex.add, QComplex.scaleRat]
      constructor <;> grind [Rat.add_mul]

theorem finiteFourierSum_zero_mode_replicate
    (root : QComplex) (n : Nat) (c : QComplex) :
    finiteFourierSum root 0 (List.replicate n c) =
      QComplex.scaleRat (n : Rat) c := by
  rw [finiteFourierSum_zero_mode, qcomplexListSum_replicate]

private theorem qcomplex_scaleRat_succ (n : Nat) (c : QComplex) :
    QComplex.scaleRat ((n + 1 : Nat) : Rat) c =
      QComplex.add c (QComplex.scaleRat (n : Rat) c) := by
  cases c
  simp [QComplex.scaleRat, QComplex.add]
  constructor <;> grind

private theorem qcomplex_one_mul (z : QComplex) :
    QComplex.mul QComplex.one z = z := by
  cases z
  simp [QComplex.mul, QComplex.one]
  constructor <;> grind

private theorem qcomplex_mode_power_one_of_phase_one
    (root : QComplex) (mode : Nat)
    (hphase : QComplex.natPow root mode = QComplex.one) :
    forall k : Nat, QComplex.natPow root (mode * k) = QComplex.one := by
  intro k
  induction k with
  | zero => simp [QComplex.natPow]
  | succ k ih =>
      rw [Nat.mul_succ, QComplex.natPow_add, ih, hphase]
      exact QComplex.mul_one_cert _

private theorem replicate_append (c : QComplex) (n m : Nat) :
    List.replicate (n + m) c = List.replicate n c ++ List.replicate m c := by
  induction n with
  | zero => simp
  | succ n ih =>
      simp only [Nat.succ_add, List.replicate_succ, List.cons_append]
      rw [ih]

theorem finiteFourierSum_replicate_of_phase_one
    (root : QComplex) (mode n : Nat) (c : QComplex)
    (hphase : QComplex.natPow root mode = QComplex.one) :
    finiteFourierSum root mode (List.replicate n c) =
      QComplex.scaleRat (n : Rat) c := by
  have hpower := qcomplex_mode_power_one_of_phase_one root mode hphase
  induction n with
  | zero =>
      simp [finiteFourierSum_empty, QComplex.scaleRat, QComplex.zero]
  | succ n ih =>
      rw [List.replicate_succ, finiteFourierSum_cons_phase]
      rw [hphase, qcomplex_one_mul, ih]
      exact (qcomplex_scaleRat_succ n c).symm

theorem finiteFourierSum_aux_scale
    (r : Rat) (root : QComplex) (mode k : Nat)
    (xs : List QComplex) :
    finiteFourierSumAux root mode k (qcomplexListScale r xs) =
      QComplex.scaleRat r (finiteFourierSumAux root mode k xs) := by
  induction xs generalizing k with
  | nil =>
      simp only [qcomplexListScale, finiteFourierSumAux]
      exact (qcomplex_scale_zero r).symm
  | cons x xs ih =>
      simp only [qcomplexListScale, finiteFourierSumAux]
      rw [ih (k := k + 1)]
      rw [qcomplex_scale_add, qcomplex_scale_mul]

theorem finiteFourierSum_scale
    (r : Rat) (root : QComplex) (mode : Nat) (xs : List QComplex) :
    finiteFourierSum root mode (qcomplexListScale r xs) =
      QComplex.scaleRat r (finiteFourierSum root mode xs) := by
  exact finiteFourierSum_aux_scale r root mode 0 xs

theorem finiteFourierSum_zero_scale
    (root : QComplex) (mode : Nat) (xs : List QComplex) :
    finiteFourierSum root mode (qcomplexListScale 0 xs) =
      QComplex.zero := by
  rw [finiteFourierSum_scale]
  exact qcomplex_scale_zero_any _

theorem finiteFourierSum_aux_conj
    (root : QComplex) (mode k : Nat) (xs : List QComplex) :
    QComplex.conj (finiteFourierSumAux root mode k xs) =
      finiteFourierSumAux (QComplex.conj root) mode k (qcomplexListConj xs) := by
  induction xs generalizing k with
  | nil => rfl
  | cons x xs ih =>
      simp only [qcomplexListConj, finiteFourierSumAux, QComplex.conj_add,
        QComplex.conj_mul, QComplex.conj_natPow]
      rw [ih (k := k + 1)]

theorem finiteFourierSum_conj
    (root : QComplex) (mode : Nat) (xs : List QComplex) :
    QComplex.conj (finiteFourierSum root mode xs) =
      finiteFourierSum (QComplex.conj root) mode (qcomplexListConj xs) := by
  exact finiteFourierSum_aux_conj root mode 0 xs

theorem finiteFourierSum_singleton
    (root x : QComplex) (mode : Nat) :
    finiteFourierSum root mode [x] =
      QComplex.mul x (QComplex.natPow root 0) := by
  simp [finiteFourierSum, finiteFourierSumAux]
  exact qcomplex_add_zero _

/-! The original four-point rational transform is an instance of the general
finite-list evaluator at the quarter-turn root.  This bridge lets its
orthogonality, reconstruction, and Parseval certificates be reused as tests
of the general API. -/
theorem finiteFourierSum_fourPoint_bridge
    (x₀ x₁ x₂ x₃ : Rat) (mode : Nat) :
    finiteFourierSum RotationSeries.imaginaryUnit mode
        [QComplex.ofRat x₀, QComplex.ofRat x₁,
          QComplex.ofRat x₂, QComplex.ofRat x₃] =
      fourPointFourierTransform x₀ x₁ x₂ x₃ mode := by
  simp [finiteFourierSum, finiteFourierSumAux,
    fourPointFourierTransform]
  rw [qcomplex_add_zero, qcomplex_add_assoc, qcomplex_add_assoc]

theorem finiteFourierSum_quarterTurn_constant_block_mode_one
    (c : QComplex) :
    finiteFourierSum RotationSeries.imaginaryUnit 1 [c, c, c, c] =
      QComplex.zero := by
  cases c
  simp [finiteFourierSum, finiteFourierSumAux, RotationSeries.imaginaryUnit,
    QComplex.natPow, QComplex.mul, QComplex.add, QComplex.zero]
  constructor <;> grind [Rat.add_assoc, Rat.add_comm, Rat.mul_add,
    Rat.add_mul, Rat.mul_assoc, Rat.mul_comm]

theorem finiteFourierSum_quarterTurn_constant_block_mode_two
    (c : QComplex) :
    finiteFourierSum RotationSeries.imaginaryUnit 2 [c, c, c, c] =
      QComplex.zero := by
  cases c
  simp [finiteFourierSum, finiteFourierSumAux, RotationSeries.imaginaryUnit,
    QComplex.natPow, QComplex.mul, QComplex.add, QComplex.zero]
  constructor <;> grind [Rat.add_assoc, Rat.add_comm, Rat.mul_add,
    Rat.add_mul, Rat.mul_assoc, Rat.mul_comm]

theorem finiteFourierSum_quarterTurn_constant_block_mode_three
    (c : QComplex) :
    finiteFourierSum RotationSeries.imaginaryUnit 3 [c, c, c, c] =
      QComplex.zero := by
  cases c
  simp [finiteFourierSum, finiteFourierSumAux, RotationSeries.imaginaryUnit,
    QComplex.natPow, QComplex.mul, QComplex.add, QComplex.zero]
  constructor <;> grind [Rat.add_assoc, Rat.add_comm, Rat.mul_add,
    Rat.add_mul, Rat.mul_assoc, Rat.mul_comm]

private theorem finiteFourierSum_replicate_block_phase_one
    (root : QComplex) (mode : Nat)
    (hphase : QComplex.natPow root (mode * 4) = QComplex.one) :
    forall k : Nat,
      QComplex.natPow root (mode * (4 * k)) = QComplex.one := by
  intro k
  induction k with
  | zero => simp [QComplex.natPow]
  | succ k ih =>
      rw [Nat.mul_succ, Nat.mul_add, QComplex.natPow_add, ih, hphase]
      exact QComplex.mul_one_cert _

theorem finiteFourierSum_replicate_block_zero_of_phase_one
    (root : QComplex) (mode : Nat) (c : QComplex) (k : Nat)
    (hblock : finiteFourierSum root mode [c, c, c, c] = QComplex.zero)
    (hphase : QComplex.natPow root (mode * 4) = QComplex.one) :
    finiteFourierSum root mode (List.replicate (4 * k) c) =
      QComplex.zero := by
  have hperiod := finiteFourierSum_replicate_block_phase_one
    root mode hphase
  induction k with
  | zero => simp [finiteFourierSum_empty, QComplex.zero]
  | succ k ih =>
      rw [show 4 * (k + 1) = 4 * k + 4 by omega,
        replicate_append, finiteFourierSum_append_phase]
      have hlength : (List.replicate (4 * k) c).length = 4 * k := by
        simp
      have hrep4 : List.replicate 4 c = [c, c, c, c] := by
        rfl
      rw [hlength, ih, hperiod k, hrep4, hblock]
      rw [qcomplex_one_mul, qcomplex_zero_add]

end ComputableAnalysis
