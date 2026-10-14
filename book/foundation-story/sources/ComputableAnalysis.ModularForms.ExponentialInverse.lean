import ComputableAnalysis.ModularForms.ExponentialAddition
import ComputableAnalysis.ModularForms.ExponentialDerivative
import ComputableAnalysis.ModularForms.Nome

/-! The explicit inverse of the entire factorial exponential. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert

theorem entireExponential_inverse (x : Scalar) :
    (mul (entireExponentialValue x).val
      (entireExponentialValue ⟨neg x.val, neg_valid x.property⟩).val).Equiv one := by
  let y : Scalar := ⟨neg x.val, neg_valid x.property⟩
  let z : Scalar := ⟨add x.val y.val, add_valid x.property y.property⟩
  let o : Scalar := ⟨zero, ofQComplex_valid _⟩
  have hz : z.val.Equiv o.val := add_neg_equiv x.val x.property
  exact equiv_trans
    (mul_valid (entireExponentialValue x).property (entireExponentialValue y).property)
    (entireExponentialValue z).property (ofQComplex_valid _)
    (entireExponential_addition x y)
    (equiv_trans (entireExponentialValue z).property (entireExponentialValue o).property
      (ofQComplex_valid _) (entireExponentialValue_congr z o hz) entireExponential_zero)

/-- The exponential at an arbitrary valid input cannot represent zero. -/
theorem entireExponential_ne_zero (x : Scalar) :
    ¬(entireExponentialValue x).val.Equiv zero := by
  intro hzero
  let y : Scalar := ⟨neg x.val, neg_valid x.property⟩
  have hp := mul_equiv (entireExponentialValue x).property (ofQComplex_valid _)
    (entireExponentialValue y).property (entireExponentialValue y).property
    hzero (equiv_refl _ (entireExponentialValue y).property)
  have hz := equiv_trans
    (mul_valid (entireExponentialValue x).property (entireExponentialValue y).property)
    (mul_valid (ofQComplex_valid _) (entireExponentialValue y).property)
    (ofQComplex_valid _) hp (zero_mul_equiv _ (entireExponentialValue y).property)
  have ho := equiv_trans (ofQComplex_valid _) 
    (mul_valid (entireExponentialValue x).property (entireExponentialValue y).property)
    (ofQComplex_valid _) (equiv_symm (entireExponential_inverse x)) hz
  have hb := (compareAt_overlap_iff one zero 0 0).mp (ho 0)
  change ((1 : Rat) ≤ 0 ∧ (0 : Rat) ≤ 0) ∧ ((0 : Rat) ≤ 1 ∧ (0 : Rat) ≤ 0) at hb
  have hn : ¬((1 : Rat) ≤ 0) := by decide +kernel
  exact hn hb.1.1

theorem nome_nonzero (z : Scalar) (hz : InUpperHalfPlane z.val) :
    NonzeroBoxSearch.Nonzero (nome.eval z hz) :=
  entireExponential_ne_zero (nomeExponentMap.eval z hz)

end ComputableAnalysis.ModularForms
