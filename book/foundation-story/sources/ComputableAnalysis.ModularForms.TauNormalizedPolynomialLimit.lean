import ComputableAnalysis.ModularForms.TauNormalizedEulerMap

/-! Actual normalized integer polynomials converging to the Euler map. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

/-- Normalized coefficients of the literal finite product. -/
def normalizedDiscriminantCoefficients (N : Nat) : Coefficients
  | 0 => 0
  | n+1 => discriminantProduct N n

/-- Each fixed coefficient stabilizes to the actual arithmetic tau function. -/
theorem normalizedDiscriminantCoefficients_stable (N n : Nat) (hn : n≤N+1) :
    normalizedDiscriminantCoefficients N n=tau n := by
  cases n with
  | zero => rfl
  | succ n => exact (tau_eq_finiteProduct n N (by omega)).symm

/-- Full finite coefficient polynomial, multiplied by the nome. -/
def normalizedDiscriminantPolynomial (q : Scalar) (N : Nat) : Scalar :=
  scalarProduct (integerCoefficientPrefix (discriminantProduct N) q
    (discriminantProductDegree N+1)) q

/-- Exact represented equality to the normalized literal finite Euler product. -/
theorem normalizedDiscriminantPolynomial_exact (q : Scalar) (N : Nat) :
    (normalizedDiscriminantPolynomial q N).val.Equiv
      (mul (finiteDiscriminantEulerProduct q N).val q.val) :=
  mul_equiv (integerCoefficientPrefix _ q _).property (finiteDiscriminantEulerProduct q N).property
    q.property q.property (discriminantProduct_exact_evaluation q N) (equiv_refl _ q.property)

/-- The actual integer coefficient polynomials converge with explicit errors. -/
theorem tauNormalizedEulerMap_close_integer_polynomial (q : Scalar)
    (hq : tauEulerNomeDomain q) (N : Nat) :
    Small (sub (tauNormalizedEulerMap.eval q hq).val (normalizedDiscriminantPolynomial q N).val)
      (2*tauEulerProductTail (1/1024) N*(1/1024)) := by
  have h := tauNormalizedEulerMap_close_prefix q hq N
  exact Small.congr
    (sub_valid (tauNormalizedEulerMap.eval q hq).property
      (mul_valid (finiteDiscriminantEulerProduct q N).property q.property))
    (sub_valid (tauNormalizedEulerMap.eval q hq).property (normalizedDiscriminantPolynomial q N).property)
    (FunctionTheory.sub_congr (equiv_refl _ (tauNormalizedEulerMap.eval q hq).property)
      (equiv_symm (normalizedDiscriminantPolynomial_exact q N))) h

/-- Shrinking errors certify convergence of the complete integer polynomials. -/
theorem normalizedDiscriminantPolynomial_error_shrinks :
    ShrinksToZero (fun N => 2*tauEulerProductTail (1/1024) N*(1/1024)) := by
  have h := SeriesLimitLaws.shrinks_scale _
    (tauEulerProductTail_shrinks (1/1024) (by decide +kernel) Rat.le_refl)
    (2*(1/1024)) (by decide +kernel)
  have he : (fun N => 2*tauEulerProductTail (1/1024) N*(1/1024))=
      (fun N => (2*(1/1024))*tauEulerProductTail (1/1024) N) := by
    funext N
    grind only
  rw [he]
  exact h

end ComputableAnalysis.ModularForms
