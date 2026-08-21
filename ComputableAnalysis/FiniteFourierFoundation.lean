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

end ComputableAnalysis
