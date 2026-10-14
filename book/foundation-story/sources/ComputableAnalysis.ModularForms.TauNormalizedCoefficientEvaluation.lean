import ComputableAnalysis.ModularForms.TauNormalizedPolynomialLimit

/-! Exact evaluation of normalized finite Euler coefficient sequences. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

/-- Evaluation commutes exactly with the coefficient shift induced by the nome. -/
theorem normalizedDiscriminantCoefficients_evaluation (q : Scalar) (N L : Nat) :
    (integerCoefficientPrefix (normalizedDiscriminantCoefficients N) q (L+1)).val.Equiv
      (mul (integerCoefficientPrefix (discriminantProduct N) q L).val q.val) := by
  have hq := q.property
  induction L with
  | zero =>
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := (integerCoefficientPrefix _ q 1).property)
      (hright := mul_valid (integerCoefficientPrefix _ q 0).property hq)
    change (0+ComplexRawQuotient.scaleRat 0 1)=0*ComplexRawQuotient.ofRaw q.val hq
    rw [ComplexRawQuotient.scaleRat_zeroScalar]
    grind only
  | succ L ih =>
    let A := integerCoefficientPrefix (normalizedDiscriminantCoefficients N) q (L+1)
    let B := integerCoefficientPrefix (discriminantProduct N) q L
    have hi := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := A.property)
      (hright := mul_valid B.property hq) ih
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := (integerCoefficientPrefix _ q ((L+1)+1)).property)
      (hright := mul_valid (integerCoefficientPrefix _ q (L+1)).property hq)
    let a := ComplexRawQuotient.ofRaw A.val A.property
    let b := ComplexRawQuotient.ofRaw B.val B.property
    let Q := ComplexRawQuotient.ofRaw q.val hq
    let P := ComplexRawQuotient.ofRaw (LocalODE.power q.val L) (LocalODE.power_valid _ hq L)
    change a=b*Q at hi
    change a+ComplexRawQuotient.scaleRat ((discriminantProduct N L):Rat) (P*Q)=
      (b+ComplexRawQuotient.scaleRat ((discriminantProduct N L):Rat) P)*Q
    rw [hi,ComplexRawQuotient.scaleRat_mul]
    grind only

/-- The full normalized coefficient polynomial is the actual finite approximation. -/
theorem normalizedDiscriminantPolynomial_coefficient_evaluation (q : Scalar) (N : Nat) :
    (integerCoefficientPrefix (normalizedDiscriminantCoefficients N) q
      (discriminantProductDegree N+2)).val.Equiv (normalizedDiscriminantPolynomial q N).val :=
  normalizedDiscriminantCoefficients_evaluation q N (discriminantProductDegree N+1)

/-- Literal normalized coefficient evaluations approximate the actual holomorphic map. -/
theorem tauNormalizedEulerMap_close_normalized_coefficients (q : Scalar)
    (hq : tauEulerNomeDomain q) (N : Nat) :
    Small (sub (tauNormalizedEulerMap.eval q hq).val
      (integerCoefficientPrefix (normalizedDiscriminantCoefficients N) q
        (discriminantProductDegree N+2)).val)
      (2*tauEulerProductTail (1/1024) N*(1/1024)) := by
  exact Small.congr
    (sub_valid (tauNormalizedEulerMap.eval q hq).property (normalizedDiscriminantPolynomial q N).property)
    (sub_valid (tauNormalizedEulerMap.eval q hq).property (integerCoefficientPrefix _ q _).property)
    (FunctionTheory.sub_congr (equiv_refl _ (tauNormalizedEulerMap.eval q hq).property)
      (equiv_symm (normalizedDiscriminantPolynomial_coefficient_evaluation q N)))
    (tauNormalizedEulerMap_close_integer_polynomial q hq N)

/-- Every stable low-degree prefix agrees exactly with the tau-series prefix. -/
theorem normalizedDiscriminantCoefficients_prefix_stable (q : Scalar) (N L : Nat)
    (hL : L≤N+2) :
    (integerCoefficientPrefix (normalizedDiscriminantCoefficients N) q L).val.Equiv
      (integerCoefficientPrefix tau q L).val := by
  induction L with
  | zero => exact equiv_refl _ (ofQComplex_valid _)
  | succ L ih =>
    have hc := normalizedDiscriminantCoefficients_stable N L (by omega)
    have ht : (scaleRat ((normalizedDiscriminantCoefficients N L):Rat) (LocalODE.power q.val L)).Equiv
        (scaleRat ((tau L):Rat) (LocalODE.power q.val L)) := by
      rw [hc]
      exact equiv_refl _ (scaleRat_valid (LocalODE.power_valid _ q.property L))
    exact add_equiv (ih (by omega)) ht

end ComputableAnalysis.ModularForms
