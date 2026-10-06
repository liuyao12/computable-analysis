import ComputableAnalysis.ModularForms.Nome
import ComputableAnalysis.ModularForms.ExponentialConjugation
import ComputableAnalysis.ModularForms.RealExponentialCore

/-! Exact squared-magnitude formula for the actual entire exponential. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

/-- Adding a represented complex value to its conjugate gives twice its real coordinate. -/
theorem scalar_add_conjugate_real_embedding (z : Scalar) :
    (add z.val (conj z.val)).Equiv (ofRealRaw (RealRaw.scaleRat 2 z.val.realPart)) := by
  intro n
  obtain ⟨hr,hi⟩ := valid_ordered z.property n
  apply (compareAt_overlap_iff _ _ n n).mpr
  simp only [add,conj,ofRealRaw,RealRaw.scaleRat,RealRaw.scaleRatCompute,
    if_pos (show (0:Rat)≤2 by decide +kernel),realPart,QBox.add,QBox.conj,QComplex.add]
  constructor <;> constructor <;> grind

/-- The actual conjugate product of exp(z) is the actual real exponential of twice Re(z). -/
theorem entireExponential_squared_magnitude (z : Scalar) :
    (mul (entireExponentialValue z).val (conj (entireExponentialValue z).val)).Equiv
      (entireExponentialValue ⟨ofRealRaw (RealRaw.scaleRat 2 z.val.realPart),
        ofRealRaw_valid _ (RealRaw.scaleRat_valid (realPart_valid z.property))⟩).val := by
  let s : Scalar := ⟨add z.val (conj z.val),add_valid z.property (conj_valid _ z.property)⟩
  let r : Scalar := ⟨ofRealRaw (RealRaw.scaleRat 2 z.val.realPart),
    ofRealRaw_valid _ (RealRaw.scaleRat_valid (realPart_valid z.property))⟩
  exact equiv_trans
    (mul_valid (entireExponentialValue z).property (conj_valid _ (entireExponentialValue z).property))
    (entireExponentialValue s).property (entireExponentialValue r).property
    (entireExponential_conjugate_product z)
    (entireExponentialValue_congr s r (scalar_add_conjugate_real_embedding z))

/-- Squared magnitude as an exact identity of valid represented real values. -/
theorem entireExponential_squared_magnitude_real (z : Scalar) :
    (mul (entireExponentialValue z).val (conj (entireExponentialValue z).val)).realPart.Equiv
      (entireExponentialValue ⟨ofRealRaw (RealRaw.scaleRat 2 z.val.realPart),
        ofRealRaw_valid _ (RealRaw.scaleRat_valid (realPart_valid z.property))⟩).val.realPart :=
  realPart_equiv (entireExponential_squared_magnitude z)

/-- Squared magnitude of the actual nome at every represented upper-half-plane input. -/
theorem nome_squared_magnitude (z : Scalar) (hz : InUpperHalfPlane z.val) :
    (mul (nome.eval z hz).val (conj (nome.eval z hz).val)).Equiv
      (entireExponentialValue ⟨ofRealRaw (RealRaw.scaleRat 2
        (nomeExponentMap.eval z hz).val.realPart),ofRealRaw_valid _
          (RealRaw.scaleRat_valid (realPart_valid (nomeExponentMap.eval z hz).property))⟩).val :=
  entireExponential_squared_magnitude (nomeExponentMap.eval z hz)

end ComputableAnalysis.ModularForms
