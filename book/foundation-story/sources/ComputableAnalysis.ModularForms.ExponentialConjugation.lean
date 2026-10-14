import ComputableAnalysis.ModularForms.ExponentialRationalConjugation
import ComputableAnalysis.ModularForms.ExponentialCenterApproximation
import ComputableAnalysis.ModularForms.ExponentialAddition

/-! Actual entire exponential conjugation at every valid represented complex input. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

def exponentialConjugateInput (z : Scalar) : Scalar := ⟨conj z.val,conj_valid _ z.property⟩

theorem exponentialCenterError_nonnegative (z : Scalar) (n : Nat) : 0≤exponentialCenterError z n := by
  have hC := exponentialBudget_nonnegative _ (exponentialRatio_positive (exponentialInputRadius z))
  have hK := Rat.le_of_lt (exponentialRatio_positive (exponentialInputRadius z))
  exact Rat.mul_nonneg
    (Rat.mul_nonneg (Rat.mul_nonneg (by decide) hC) (Rat.pow_nonneg hK))
    (centerError_nonnegative z.val z.property n)

theorem rationalCenter_conjugation (z : Scalar) (n : Nat) :
    rationalCenter (exponentialConjugateInput z) n =
      (⟨ofQComplex (QComplex.conj (z.val.compute n).center),ofQComplex_valid _⟩ : Scalar) := by
  apply Subtype.ext
  change ofQComplex (QBox.conj (z.val.compute n)).center = ofQComplex (QComplex.conj (z.val.compute n).center)
  congr 1
  simp only [QBox.center,QBox.conj,QComplex.conj]
  congr 1 <;> grind only

theorem entireExponential_conjugation (z : Scalar) :
    (conj (entireExponentialValue z).val).Equiv (entireExponentialValue (exponentialConjugateInput z)).val := by
  let w := exponentialConjugateInput z
  apply conjugateLimit_comparison _ _ (entireExponentialValue z).property (entireExponentialValue w).property
    (fun n => (entireExponentialValue (rationalCenter z n)).val)
    (fun n => (entireExponentialValue (rationalCenter w n)).val)
    (fun n => (entireExponentialValue (rationalCenter z n)).property)
    (fun n => (entireExponentialValue (rationalCenter w n)).property)
    (exponentialCenterError z) (exponentialCenterError w)
    (exponentialCenterError_shrinks z) (exponentialCenterError_shrinks w)
    (exponentialCenterError_nonnegative z) (exponentialCenterError_nonnegative w)
    (exponential_center_error z) (exponential_center_error w)
  intro n
  dsimp [w]
  rw [rationalCenter_conjugation z n]
  exact entireExponential_rational_conjugation (z.val.compute n).center

theorem entireExponential_conjugate_product (z : Scalar) :
    (mul (entireExponentialValue z).val (conj (entireExponentialValue z).val)).Equiv
      (entireExponentialValue ⟨add z.val (conj z.val),add_valid z.property (conj_valid _ z.property)⟩).val := by
  have he := mul_equiv (entireExponentialValue z).property (entireExponentialValue z).property
    (conj_valid _ (entireExponentialValue z).property)
    (entireExponentialValue (exponentialConjugateInput z)).property
    (equiv_refl _ (entireExponentialValue z).property) (entireExponential_conjugation z)
  exact equiv_trans
    (mul_valid (entireExponentialValue z).property (conj_valid _ (entireExponentialValue z).property))
    (mul_valid (entireExponentialValue z).property (entireExponentialValue (exponentialConjugateInput z)).property)
    (entireExponentialValue ⟨add z.val (conj z.val),add_valid z.property (conj_valid _ z.property)⟩).property
    he (entireExponential_addition z (exponentialConjugateInput z))

end ComputableAnalysis.ModularForms
