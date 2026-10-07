import ComputableAnalysis.ModularForms.ExponentialLogarithmAgreement
import ComputableAnalysis.ModularForms.ExponentialInverse

/-! A constructed local logarithm of the actual nome at any represented
upper-half-plane center. The seed is the actual nome exponent; no logarithm
value or endpoint exponential identity is assumed. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

def nomeLogarithmChart (a : Scalar) (ha : InUpperHalfPlane a.val) : DomainFunctions.Map :=
  compose (affine (nomeExponentMap.eval a ha) oneScalar)
    (RelativeLogarithm.function (nome.eval a ha) (nome_nonzero a ha))

def nomeLogarithmChart_holomorphic (a : Scalar) (ha : InUpperHalfPlane a.val) :
    Holomorphic (nomeLogarithmChart a ha) :=
  (DomainFunctions.affine_holomorphic (nomeExponentMap.eval a ha) oneScalar).compose
    (RelativeLogarithm.holomorphic (nome.eval a ha) (nome_nonzero a ha))

theorem nomeLogarithmChart_center_mem (a : Scalar) (ha : InUpperHalfPlane a.val) :
    (nomeLogarithmChart a ha).domain (nome.eval a ha) :=
  ⟨RelativeLogarithm.center_mem (nome.eval a ha) (nome_nonzero a ha), trivial⟩

theorem nomeLogarithmChart_value (a : Scalar) (ha : InUpperHalfPlane a.val)
    (q : Scalar) (hq : (nomeLogarithmChart a ha).domain q) :
    ((nomeLogarithmChart a ha).eval q hq).val.Equiv
      (MatrixExponential.propagatedBranch (nome.eval a ha) (nome_nonzero a ha)
        (nomeExponentMap.eval a ha) q hq.1).val :=
  add_equiv (equiv_refl _ (nomeExponentMap.eval a ha).property)
    (one_mul_equiv _ ((RelativeLogarithm.function (nome.eval a ha) (nome_nonzero a ha)).eval q hq.1).property)

/-- The chart represents an actual local logarithm of its input. -/
theorem nomeLogarithmChart_exponential (a : Scalar) (ha : InUpperHalfPlane a.val)
    (q : Scalar) (hq : (nomeLogarithmChart a ha).domain q) :
    (entireExponentialValue ((nomeLogarithmChart a ha).eval q hq)).val.Equiv q.val :=
  equiv_trans (entireExponentialValue ((nomeLogarithmChart a ha).eval q hq)).property
    (entireExponentialValue (MatrixExponential.propagatedBranch (nome.eval a ha) (nome_nonzero a ha)
      (nomeExponentMap.eval a ha) q hq.1)).property q.property
    (entireExponentialValue_congr _ _ (nomeLogarithmChart_value a ha q hq))
    (entireExponential_propagatedLogarithm (nome.eval a ha) (nome_nonzero a ha)
      (nomeExponentMap.eval a ha) (equiv_refl _ (nome.eval a ha).property) q hq.1)

/-- At its center the constructed chart recovers the actual nome exponent. -/
theorem nomeLogarithmChart_center (a : Scalar) (ha : InUpperHalfPlane a.val) :
    ((nomeLogarithmChart a ha).eval (nome.eval a ha) (nomeLogarithmChart_center_mem a ha)).val.Equiv
      (nomeExponentMap.eval a ha).val := by
  let L := (RelativeLogarithm.function (nome.eval a ha) (nome_nonzero a ha)).eval
    (nome.eval a ha) (RelativeLogarithm.center_mem _ _)
  have h := add_equiv (equiv_refl _ (nomeExponentMap.eval a ha).property)
    (equiv_trans (mul_valid oneScalar.property L.property) L.property (ofQComplex_valid _)
      (one_mul_equiv _ L.property) (RelativeLogarithm.initial _ _))
  exact equiv_trans ((nomeLogarithmChart a ha).eval (nome.eval a ha) (nomeLogarithmChart_center_mem a ha)).property
    (add_valid (nomeExponentMap.eval a ha).property (ofQComplex_valid _))
    (nomeExponentMap.eval a ha).property h (add_zero_equiv _ (nomeExponentMap.eval a ha).property)

end ComputableAnalysis.ModularForms
