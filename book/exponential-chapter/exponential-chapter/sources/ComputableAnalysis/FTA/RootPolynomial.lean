import ComputableAnalysis.FTA.PolynomialDerivative
import ComputableAnalysis.FTA.Normalization

namespace ComputableAnalysis.RepresentedPolynomial
open Arithmetic

/-- Coefficients of multiplication by the supplied linear factor. -/
def linearMultiply (r : ComplexCert) (p : Coefficients) : Coefficients :=
  coefficientAdd (p.map (mul (neg r))) (zero :: p)

/-- An executable polynomial formed from its supplied represented roots. -/
def rootPolynomial : List ComplexCert → Coefficients
  | [] => [one]
  | r :: rs => linearMultiply r (rootPolynomial rs)

private theorem coefficientAdd_append_one (p q : Coefficients)
    (h : p.length ≤ q.length) :
    coefficientAdd p (q ++ [one]) = coefficientAdd p q ++ [one] := by
  induction p generalizing q with
  | nil => rfl
  | cons a p ih =>
      cases q with
      | nil => simp at h
      | cons b q =>
          simp only [List.length_cons] at h
          change add a b :: coefficientAdd p (q ++ [one]) = _
          rw [ih q (by omega)]
          rfl

private theorem coefficientAdd_length (p q : Coefficients) :
    (coefficientAdd p q).length = max p.length q.length := by
  induction p generalizing q with
  | nil => simp [coefficientAdd]
  | cons a p ih =>
      cases q with
      | nil => simp [coefficientAdd]
      | cons b q =>
          simp only [coefficientAdd, List.length_cons, ih]
          omega

theorem linearMultiply_monic (r : ComplexCert) (p : Coefficients) (hp : Monic p) :
    Monic (linearMultiply r p) := by
  obtain ⟨q, rfl⟩ := hp
  refine ⟨coefficientAdd ((q ++ [one]).map (mul (neg r))) (zero :: q), ?_⟩
  unfold linearMultiply
  change coefficientAdd _ ((zero :: q) ++ [one]) = _
  exact coefficientAdd_append_one _ _ (by simp)

theorem rootPolynomial_monic (rs : List ComplexCert) : Monic (rootPolynomial rs) := by
  induction rs with
  | nil => exact ⟨[], rfl⟩
  | cons r rs ih => exact linearMultiply_monic r _ ih

theorem rootPolynomial_length (rs : List ComplexCert) :
    (rootPolynomial rs).length = rs.length + 1 := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
      simp [rootPolynomial, linearMultiply, coefficientAdd_length, ih]

theorem eval_linearMultiply (r : ComplexCert) (p : Coefficients) (z : ComplexCert) :
    (eval (linearMultiply r p) z).raw.Equiv (mul (sub z r) (eval p z)).raw := by
  refine certTrans (eval_coefficientAdd _ _ z) ?_
  refine certTrans (certAddCongr (eval_scale _ _ _) (zero_add _)) ?_
  apply Expression.equiv_of_samples
    (.add (.mul (.neg (.parameter r)) (.parameter (eval p z)))
      (.mul (.parameter z) (.parameter (eval p z))))
    (.mul (.add (.parameter z) (.neg (.parameter r))) (.parameter (eval p z)))
  intro s
  have ext {a b : QComplex} (hr : a.re = b.re) (hi : a.im = b.im) : a = b := by
    cases a; cases b; simp_all
  apply ext <;> simp [Expression.sample, QComplex.add, QComplex.neg, QComplex.mul] <;> grind

theorem eval_rootPolynomial (rs : List ComplexCert) (z : ComplexCert) :
    (eval (rootPolynomial rs) z).raw.Equiv (rootProduct rs z).raw := by
  induction rs with
  | nil => exact certTrans (certAddCongr (certRefl one) (certMulZero z)) (add_zero one)
  | cons r rs ih =>
      exact certTrans (eval_linearMultiply r _ z) (certMulCongr (certRefl _) ih)

end ComputableAnalysis.RepresentedPolynomial
