import ComputableAnalysis.FTA.RealAlgebra

/-! Formal differentiation over arbitrary valid represented coefficients.
The evaluator, deflation rule, and representation invariance are finite
algebra. No analytic differentiability theorem is assumed. -/
namespace ComputableAnalysis.RepresentedPolynomial
open Arithmetic

/-- Coefficientwise addition, retaining possible trailing zero coefficients. -/
def coefficientAdd : Coefficients → Coefficients → Coefficients
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => add a b :: coefficientAdd p q

/-- Formal derivative using the Horner identity `(c + X*q)' = q + X*q'`. -/
def derivative : Coefficients → Coefficients
  | [] => []
  | _ :: p => coefficientAdd p (zero :: derivative p)

/-- Direct Horner evaluation of the formal derivative. -/
def derivativeEval : Coefficients → ComplexCert → ComplexCert
  | [], _ => zero
  | _ :: p, z => add (eval p z) (mul z (derivativeEval p z))

private theorem arithmetic_ext {a b : QComplex}
    (hr : a.re = b.re) (hi : a.im = b.im) : a = b := by
  cases a; cases b; simp_all

theorem eval_coefficientAdd (p q : Coefficients) (z : ComplexCert) :
    (eval (coefficientAdd p q) z).raw.Equiv (add (eval p z) (eval q z)).raw := by
  induction p generalizing q with
  | nil => exact ComplexRaw.equiv_symm (zero_add _)
  | cons a p ih =>
      cases q with
      | nil => exact ComplexRaw.equiv_symm (add_zero _)
      | cons b q =>
          refine certTrans (certAddCongr (certRefl (add a b))
            (certMulCongr (certRefl z) (ih q))) ?_
          apply Expression.equiv_of_samples
            (.add (.add (.parameter a) (.parameter b))
              (.mul (.parameter z) (.add (.parameter (eval p z)) (.parameter (eval q z)))))
            (.add (.add (.parameter a) (.mul (.parameter z) (.parameter (eval p z))))
              (.add (.parameter b) (.mul (.parameter z) (.parameter (eval q z)))))
          intro s
          apply arithmetic_ext <;> simp [Expression.sample, QComplex.add, QComplex.mul] <;> grind

theorem eval_derivative (p : Coefficients) (z : ComplexCert) :
    (eval (derivative p) z).raw.Equiv (derivativeEval p z).raw := by
  induction p with
  | nil => exact certRefl zero
  | cons a p ih =>
      exact certTrans (eval_coefficientAdd p (zero :: derivative p) z)
        (certAddCongr (certRefl (eval p z))
          (certTrans (zero_add _) (certMulCongr (certRefl z) ih)))

theorem derivativeEval_equiv {p q : Coefficients} (hpq : Equivalent p q)
    {z w : ComplexCert} (hzw : z.raw.Equiv w.raw) :
    (derivativeEval p z).raw.Equiv (derivativeEval q w).raw := by
  induction hpq with
  | nil => exact certRefl zero
  | @cons a b p q _ hpq ih =>
      exact certAddCongr (eval_equiv hpq hzw) (certMulCongr hzw ih)

theorem derivativeEval_real (p : Coefficients) (hp : RealCoefficients p)
    (z : ComplexCert) (hz : IsReal z) : IsReal (derivativeEval p z) := by
  have eval_real : ∀ p : Coefficients, RealCoefficients p → IsReal (eval p z) := by
    intro q hq
    induction q with
    | nil => exact IsReal.zero
    | cons a q ih => exact IsReal.add hq.1 (IsReal.mul hz (ih hq.2))
  induction p with
  | nil => exact IsReal.zero
  | cons a p ih => exact IsReal.add (eval_real p hp.2) (IsReal.mul hz (ih hp.2))

/-- Differentiating synthetic division removes the constant remainder.
This holds even when the division point is not a root. -/
theorem derivativeEval_deflation (p : Coefficients) (r z : ComplexCert) :
    (derivativeEval p z).raw.Equiv
      (add (eval (syntheticDivide r p).1 z)
        (mul (sub z r) (derivativeEval (syntheticDivide r p).1 z))).raw := by
  induction p with
  | nil =>
      exact ComplexRaw.equiv_symm (certTrans
        (certAddCongr (certRefl zero) (certMulZero _)) (zero_add zero))
  | cons a p ih =>
      cases p with
      | nil =>
          exact certTrans (certAddCongr (certRefl zero) (certMulZero z))
            (ComplexRaw.equiv_symm (certAddCongr (certRefl zero) (certMulZero _)))
      | cons b p =>
          refine certTrans (certAddCongr (syntheticDivide_spec r z (b :: p))
            (certMulCongr (certRefl z) ih)) ?_
          let e := eval (syntheticDivide r (b :: p)).1 z
          let d := derivativeEval (syntheticDivide r (b :: p)).1 z
          let c := (syntheticDivide r (b :: p)).2
          apply Expression.equiv_of_samples
            (.add (.add (.parameter c)
              (.mul (.add (.parameter z) (.neg (.parameter r))) (.parameter e)))
              (.mul (.parameter z) (.add (.parameter e)
                (.mul (.add (.parameter z) (.neg (.parameter r))) (.parameter d)))))
            (.add (.add (.parameter c) (.mul (.parameter z) (.parameter e)))
              (.mul (.add (.parameter z) (.neg (.parameter r)))
                (.add (.parameter e) (.mul (.parameter z) (.parameter d)))))
          intro s
          apply arithmetic_ext <;> simp [Expression.sample, QComplex.add, QComplex.neg,
            QComplex.mul] <;> grind

/-- The derivative at the division point is the quotient evaluated there. -/
theorem derivativeEval_at_division (p : Coefficients) (z : ComplexCert) :
    (derivativeEval p z).raw.Equiv (eval (syntheticDivide z p).1 z).raw :=
  certTrans (derivativeEval_deflation p z z)
    (certTrans (certAddCongr (certRefl _)
      (certTrans (certMulCongr (sub_self z) (certRefl _)) (zero_mul _))) (add_zero _))

/-- Formal derivative of the product of the supplied linear factors. -/
def rootProductDerivative : List ComplexCert → ComplexCert → ComplexCert
  | [], _ => zero
  | r :: rs, z => add (rootProduct rs z) (mul (sub z r) (rootProductDerivative rs z))

/-- FTA splitting together with its derivative identity. Roots are selected
by the established FTA, then synthetic division is iterated by degree. -/
theorem monic_factorization_with_derivative (p : Coefficients) (hp : Monic p) :
    ∃ rs : List ComplexCert, rs.length = p.length - 1 ∧
      (∀ z, (eval p z).raw.Equiv (rootProduct rs z).raw) ∧
      (∀ z, (derivativeEval p z).raw.Equiv (rootProductDerivative rs z).raw) := by
  classical
  by_cases hd : 2 ≤ p.length
  · obtain ⟨r, hr⟩ := monic_root_existence p hp hd
    let q := (syntheticDivide r p).1
    obtain ⟨rs, hlen, heval, hderiv⟩ := monic_factorization_with_derivative q
      (syntheticDivide_monic r p hp hd)
    refine ⟨r :: rs, ?_, ?_, ?_⟩
    · have hq := syntheticDivide_length r p
      change rs.length + 1 = _
      dsimp [q] at hlen
      omega
    · intro z
      exact certTrans (syntheticDivide_factor hr z)
        (certMulCongr (certRefl _) (heval z))
    · intro z
      exact certTrans (derivativeEval_deflation p r z)
        (certAddCongr (heval z) (certMulCongr (certRefl _) (hderiv z)))
  · obtain ⟨q, rfl⟩ := hp
    have hq : q = [] := List.length_eq_zero_iff.mp (by
      have hlen : (q ++ [one]).length = q.length + 1 := by simp
      omega)
    subst q
    refine ⟨[], rfl, ?_, ?_⟩
    · intro z
      exact certTrans (certAddCongr (certRefl one) (certMulZero z)) (add_zero one)
    · intro z
      exact certTrans (certAddCongr (certRefl zero) (certMulZero z)) (zero_add zero)
termination_by p.length
decreasing_by rw [syntheticDivide_length]; omega

theorem derivativeEval_scale (c : ComplexCert) (p : Coefficients) (z : ComplexCert) :
    (derivativeEval (p.map (mul c)) z).raw.Equiv (mul c (derivativeEval p z)).raw := by
  induction p with
  | nil => exact ComplexRaw.equiv_symm (certMulZero c)
  | cons a p ih =>
      refine certTrans (certAddCongr (eval_scale c p z) (certMulCongr (certRefl z) ih)) ?_
      apply Expression.equiv_of_samples
        (.add (.mul (.parameter c) (.parameter (eval p z)))
          (.mul (.parameter z) (.mul (.parameter c) (.parameter (derivativeEval p z)))))
        (.mul (.parameter c) (.add (.parameter (eval p z))
          (.mul (.parameter z) (.parameter (derivativeEval p z)))))
      intro s
      apply arithmetic_ext <;> simp [Expression.sample, QComplex.add, QComplex.mul] <;> grind

theorem normalize_coefficients (q : Coefficients) (c b : ComplexCert)
    (hcb : (mul c b).raw.Equiv one.raw) :
    Equivalent (q ++ [c]) ((normalize q b).map (mul c)) := by
  induction q with
  | nil => exact .cons (ComplexRaw.equiv_symm (certMulOne c)) .nil
  | cons a q ih =>
      refine .cons (ComplexRaw.equiv_symm ?_) ih
      have hassoc : (mul c (mul b a)).raw.Equiv (mul (mul c b) a).raw := by
        apply Expression.equiv_of_samples
          (.mul (.parameter c) (.mul (.parameter b) (.parameter a)))
          (.mul (.mul (.parameter c) (.parameter b)) (.parameter a))
        intro s
        exact (QComplex.mul_assoc_cert _ _ _).symm
      exact certTrans hassoc (certTrans (certMulCongr hcb (certRefl a)) (certOneMul a))

/-- Complete splitting and its derivative identity with arbitrary nonzero
leading coefficient. Both identities hold at every represented argument. -/
theorem complex_factorization_with_derivative (q : Coefficients) (c : ComplexCert)
    (hc : ¬ c.raw.Equiv zero.raw) :
    ∃ rs : List ComplexCert, rs.length = q.length ∧
      (∀ z, (eval (q ++ [c]) z).raw.Equiv (mul c (rootProduct rs z)).raw) ∧
      (∀ z, (derivativeEval (q ++ [c]) z).raw.Equiv (mul c (rootProductDerivative rs z)).raw) := by
  obtain ⟨b, hb⟩ := exists_inverse c hc
  obtain ⟨rs, hlen, he, hd⟩ := monic_factorization_with_derivative (normalize q b)
    ⟨q.map (mul b), rfl⟩
  refine ⟨rs, by simpa [normalize] using hlen, ?_, ?_⟩
  · intro z
    exact certTrans (normalize_spec q c b hb z) (certMulCongr (certRefl c) (he z))
  · intro z
    exact certTrans (derivativeEval_equiv (normalize_coefficients q c b hb) (certRefl z))
      (certTrans (derivativeEval_scale c _ z) (certMulCongr (certRefl c) (hd z)))

end ComputableAnalysis.RepresentedPolynomial
