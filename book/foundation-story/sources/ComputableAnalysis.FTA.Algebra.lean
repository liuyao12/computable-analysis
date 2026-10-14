import ComputableAnalysis.RepresentedPolynomial

/-! Finite complex arithmetic identities lifted to exact raw-value equality.
Rational samples are used only in the proof; evaluation uses the original raw
representatives. No equality test on real or complex numbers is used. -/
namespace ComputableAnalysis.RepresentedPolynomial

def ofQComplex (a : QComplex) : ComplexCert :=
  ⟨ComplexRaw.ofQComplex a, ComplexRaw.ofQComplex_valid a⟩

def neg (a : ComplexCert) : ComplexCert :=
  ⟨ComplexRaw.neg a.raw, ComplexRaw.neg_valid a.valid⟩

def sub (a b : ComplexCert) : ComplexCert := add a (neg b)

def conj (a : ComplexCert) : ComplexCert :=
  ⟨ComplexRaw.conj a.raw, ComplexRaw.conj_valid a.raw a.valid⟩

namespace Arithmetic

inductive Expression where
  | parameter (a : ComplexCert)
  | constant (a : QComplex)
  | add (a b : Expression)
  | neg (a : Expression)
  | mul (a b : Expression)
  | conj (a : Expression)

def Expression.value : Expression → ComplexCert
  | .parameter a => a
  | .constant a => ofQComplex a
  | .add a b => RepresentedPolynomial.add a.value b.value
  | .neg a => RepresentedPolynomial.neg a.value
  | .mul a b => RepresentedPolynomial.mul a.value b.value
  | .conj a => RepresentedPolynomial.conj a.value

def Expression.sample (s : ComplexCert → QComplex) : Expression → QComplex
  | .parameter a => s a
  | .constant a => a
  | .add a b => QComplex.add (a.sample s) (b.sample s)
  | .neg a => QComplex.neg (a.sample s)
  | .mul a b => QComplex.mul (a.sample s) (b.sample s)
  | .conj a => QComplex.conj (a.sample s)

theorem Expression.contains (e : Expression) (n : Nat)
    (s : ComplexCert → QComplex)
    (hs : ∀ a, (a.raw.compute n).lo ≤ s a ∧ s a ≤ (a.raw.compute n).hi) :
    (e.value.raw.compute n).lo ≤ e.sample s ∧
      e.sample s ≤ (e.value.raw.compute n).hi := by
  induction e with
  | parameter a => exact hs a
  | constant a => exact ⟨QComplex.le_refl _, QComplex.le_refl _⟩
  | add a b ha hb => exact QBox.add_contains ha.1 ha.2 hb.1 hb.2
  | mul a b ha hb => exact QBox.mul_contains ha.1 ha.2 hb.1 hb.2
  | neg a ha =>
      change (-((a.value.raw.compute n).hi.re) ≤ -(a.sample s).re ∧
        -((a.value.raw.compute n).hi.im) ≤ -(a.sample s).im) ∧
        (-(a.sample s).re ≤ -((a.value.raw.compute n).lo.re) ∧
        -(a.sample s).im ≤ -((a.value.raw.compute n).lo.im))
      exact ⟨⟨Rat.neg_le_neg ha.2.1, Rat.neg_le_neg ha.2.2⟩,
        ⟨Rat.neg_le_neg ha.1.1, Rat.neg_le_neg ha.1.2⟩⟩
  | conj a ha =>
      change ((a.value.raw.compute n).lo.re ≤ (a.sample s).re ∧
        -((a.value.raw.compute n).hi.im) ≤ -(a.sample s).im) ∧
        ((a.sample s).re ≤ (a.value.raw.compute n).hi.re ∧
        -(a.sample s).im ≤ -((a.value.raw.compute n).lo.im))
      exact ⟨⟨ha.1.1, Rat.neg_le_neg ha.2.2⟩,
        ⟨ha.2.1, Rat.neg_le_neg ha.1.2⟩⟩

/-- A finite rational identity gives equality of the represented values. -/
theorem Expression.equiv_of_samples (e f : Expression)
    (h : ∀ s, e.sample s = f.sample s) : e.value.raw.Equiv f.value.raw := by
  intro n
  let s : ComplexCert → QComplex := fun a => (a.raw.compute n).lo
  have hs : ∀ a, (a.raw.compute n).lo ≤ s a ∧ s a ≤ (a.raw.compute n).hi :=
    fun a => ⟨QComplex.le_refl _, ComplexRaw.valid_ordered a.valid n⟩
  have he := e.contains n s hs
  have hf := f.contains n s hs
  rw [h s] at he
  apply (ComplexRaw.compareAt_overlap_iff _ _ n n).2
  exact ⟨QComplex.le_trans he.1 hf.2, QComplex.le_trans hf.1 he.2⟩

end Arithmetic

open Arithmetic

private theorem qext {a b : QComplex} (hre : a.re = b.re) (him : a.im = b.im) : a = b := by
  cases a
  cases b
  simp_all

private def param := Expression.parameter

private def difference (a b : Expression) : Expression := .add a (.neg b)

theorem add_zero (a : ComplexCert) : (add a zero).raw.Equiv a.raw := by
  apply Expression.equiv_of_samples (.add (param a) (.constant QComplex.zero)) (param a)
  intro s
  apply qext <;> simp [Expression.sample, param, QComplex.add, QComplex.zero] <;> grind

theorem zero_add (a : ComplexCert) : (add zero a).raw.Equiv a.raw := by
  apply Expression.equiv_of_samples (.add (.constant QComplex.zero) (param a)) (param a)
  intro s
  apply qext <;> simp [Expression.sample, param, QComplex.add, QComplex.zero] <;> grind

theorem sub_self (a : ComplexCert) : (sub a a).raw.Equiv zero.raw := by
  apply Expression.equiv_of_samples (difference (param a) (param a)) (.constant QComplex.zero)
  intro s
  apply qext <;> simp [Expression.sample, difference, param, QComplex.add, QComplex.neg, QComplex.zero] <;> grind

theorem zero_mul (a : ComplexCert) : (mul zero a).raw.Equiv zero.raw := by
  apply Expression.equiv_of_samples (.mul (.constant QComplex.zero) (param a)) (.constant QComplex.zero)
  intro s
  apply qext <;> simp [Expression.sample, param, QComplex.mul, QComplex.zero] <;> grind

theorem conj_zero : (conj zero).raw.Equiv zero.raw := by
  apply Expression.equiv_of_samples (.conj (.constant QComplex.zero)) (.constant QComplex.zero)
  intro s
  simp [Expression.sample, QComplex.conj, QComplex.zero]

theorem conj_add (a b : ComplexCert) :
    (conj (add a b)).raw.Equiv (add (conj a) (conj b)).raw := by
  apply Expression.equiv_of_samples (.conj (.add (param a) (param b)))
    (.add (.conj (param a)) (.conj (param b)))
  intro s
  simp [Expression.sample, param, QComplex.conj, QComplex.add]
  grind

theorem conj_mul (a b : ComplexCert) :
    (conj (mul a b)).raw.Equiv (mul (conj a) (conj b)).raw := by
  apply Expression.equiv_of_samples (.conj (.mul (param a) (param b)))
    (.mul (.conj (param a)) (.conj (param b)))
  intro s
  simp [Expression.sample, param, QComplex.conj, QComplex.mul]
  grind

/-- The finite algebraic step in synthetic division, for arbitrary represented
coefficients and arguments. -/
theorem deflation_step (c r x b q : ComplexCert) :
    (add c (mul x (add b (mul (sub x r) q)))).raw.Equiv
      (add (add c (mul r b)) (mul (sub x r) (add b (mul x q)))).raw := by
  apply Expression.equiv_of_samples
    (.add (param c) (.mul (param x) (.add (param b) (.mul (difference (param x) (param r)) (param q)))))
    (.add (.add (param c) (.mul (param r) (param b)))
      (.mul (difference (param x) (param r)) (.add (param b) (.mul (param x) (param q)))))
  intro s
  apply qext <;>
    simp [Expression.sample, param, difference, QComplex.add, QComplex.neg, QComplex.mul] <;> grind

end ComputableAnalysis.RepresentedPolynomial
