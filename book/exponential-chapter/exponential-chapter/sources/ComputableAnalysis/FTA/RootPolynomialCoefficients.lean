import ComputableAnalysis.FTA.RootPolynomialSymmetry
import ComputableAnalysis.RiemannHilbert.ScalarAlgebra

namespace ComputableAnalysis.RepresentedPolynomial
open RiemannHilbert

def certClass (a : ComplexCert) : ScalarAlgebra.Value :=
  ComplexRawQuotient.ofRaw a.raw a.valid

def coefficientClass : Coefficients → Nat → ScalarAlgebra.Value
  | [], _ => 0
  | a :: _, 0 => certClass a
  | _ :: p, k + 1 => coefficientClass p k

private theorem class_add (a b : ComplexCert) : certClass (add a b) = certClass a + certClass b := rfl
private theorem class_mul (a b : ComplexCert) : certClass (mul a b) = certClass a * certClass b := rfl
private theorem class_neg (a : ComplexCert) : certClass (neg a) = -certClass a := rfl
private theorem class_zero : certClass zero = 0 := rfl

theorem coefficientClass_add (p q : Coefficients) (k : Nat) :
    coefficientClass (coefficientAdd p q) k = coefficientClass p k + coefficientClass q k := by
  induction p generalizing q k with
  | nil =>
      simp only [coefficientAdd, coefficientClass]
      grind
  | cons a p ih =>
      cases q with
      | nil =>
          simp only [coefficientAdd, coefficientClass]
          grind
      | cons b q =>
          cases k with
          | zero => exact class_add a b
          | succ k => exact ih q k

theorem coefficientClass_scale (c : ComplexCert) (p : Coefficients) (k : Nat) :
    coefficientClass (p.map (mul c)) k = certClass c * coefficientClass p k := by
  induction p generalizing k with
  | nil =>
      simp only [List.map_nil, coefficientClass]
      grind
  | cons a p ih =>
      cases k with
      | zero => exact class_mul c a
      | succ k => exact ih k

theorem coefficientClass_linear_zero (r : ComplexCert) (p : Coefficients) :
    coefficientClass (linearMultiply r p) 0 = -certClass r * coefficientClass p 0 := by
  simp [linearMultiply, coefficientClass_add, coefficientClass_scale, class_neg,
    coefficientClass, class_zero]
  grind

theorem coefficientClass_linear_succ (r : ComplexCert) (p : Coefficients) (k : Nat) :
    coefficientClass (linearMultiply r p) (k+1) =
      -certClass r * coefficientClass p (k+1) + coefficientClass p k := by
  simp [linearMultiply, coefficientClass_add, coefficientClass_scale, class_neg, coefficientClass]

private theorem equivalent_of_classes {p q : Coefficients} (hlen : p.length = q.length)
    (h : ∀ k, coefficientClass p k = coefficientClass q k) : Equivalent p q := by
  induction p generalizing q with
  | nil => cases q with
      | nil => exact .nil
      | cons b q => simp at hlen
  | cons a p ih =>
      cases q with
      | nil => simp at hlen
      | cons b q =>
          refine .cons (ComplexRawQuotient.equiv_of_ofRaw_eq (h 0)) ?_
          exact ih (by simpa using hlen) (fun k => h (k+1))

private theorem equivalent_classes {p q : Coefficients} (h : Equivalent p q) :
    p.length = q.length ∧ ∀ k, coefficientClass p k = coefficientClass q k := by
  induction h with
  | nil => exact ⟨rfl, fun _ => rfl⟩
  | @cons a b p q hab _ ih =>
      refine ⟨by simp [ih.1], ?_⟩
      intro k
      cases k with
      | zero => exact ComplexRawQuotient.ofRaw_eq_ofRaw hab
      | succ k => exact ih.2 k

private theorem coefficientAdd_length' (p q : Coefficients) :
    (coefficientAdd p q).length = max p.length q.length := by
  induction p generalizing q with
  | nil => simp [coefficientAdd]
  | cons a p ih =>
      cases q with
      | nil => simp [coefficientAdd]
      | cons b q =>
          simp only [coefficientAdd, List.length_cons, ih]
          omega

private theorem linear_length (r : ComplexCert) (p : Coefficients) :
    (linearMultiply r p).length = p.length + 1 := by
  simp [linearMultiply, coefficientAdd_length']

/-- Multiplying by equivalent supplied factors preserves every coefficient value. -/
theorem linearMultiply_equivalent {r s : ComplexCert} (hrs : r.raw.Equiv s.raw)
    {p q : Coefficients} (hpq : Equivalent p q) :
    Equivalent (linearMultiply r p) (linearMultiply s q) := by
  obtain ⟨hlen, hc⟩ := equivalent_classes hpq
  have hr : certClass r = certClass s := ComplexRawQuotient.ofRaw_eq_ofRaw hrs
  apply equivalent_of_classes (by simp [linear_length, hlen])
  intro k
  cases k with
  | zero => simp [coefficientClass_linear_zero, hr, hc]
  | succ k => simp [coefficientClass_linear_succ, hr, hc]

/-- Two linear factors commute at the level of represented coefficients. -/
theorem linearMultiply_comm (r s : ComplexCert) (p : Coefficients) :
    Equivalent (linearMultiply r (linearMultiply s p)) (linearMultiply s (linearMultiply r p)) := by
  apply equivalent_of_classes (by simp [linear_length])
  intro k
  cases k with
  | zero =>
      simp only [coefficientClass_linear_zero]
      grind
  | succ k =>
      cases k with
      | zero =>
          simp only [coefficientClass_linear_succ, coefficientClass_linear_zero]
          grind
      | succ k =>
          simp only [coefficientClass_linear_succ]
          grind

/-- Root permutation preserves each coefficient's exact represented value. -/
theorem rootPolynomial_perm {rs ss : List ComplexCert} (h : rs.Perm ss) :
    Equivalent (rootPolynomial rs) (rootPolynomial ss) := by
  induction h with
  | nil => exact equivalent_refl _
  | cons r _ ih => exact linearMultiply_equivalent (certRefl r) ih
  | swap r s rs => exact linearMultiply_comm s r _
  | trans _ _ ih₁ ih₂ =>
      have trans {p q t : Coefficients} (hpq : Equivalent p q) (hqt : Equivalent q t) : Equivalent p t := by
        induction hpq generalizing t with
        | nil => cases hqt; exact .nil
        | cons hab _ ih =>
            cases hqt with
            | cons hbc hqt => exact .cons (certTrans hab hbc) (ih hqt)
      exact trans ih₁ ih₂

/-- Changing representatives of the roots preserves all coefficient values. -/
theorem rootPolynomial_equivalent {rs ss : List ComplexCert} (h : Equivalent rs ss) :
    Equivalent (rootPolynomial rs) (rootPolynomial ss) := by
  induction h with
  | nil => exact equivalent_refl _
  | cons hrs _ ih => exact linearMultiply_equivalent hrs ih

/-- A supplied polynomial coefficient, with zero beyond the list. -/
def coefficient : Coefficients → Nat → ComplexCert
  | [], _ => zero
  | a :: _, 0 => a
  | _ :: p, k+1 => coefficient p k

private theorem coefficient_class (p : Coefficients) (k : Nat) :
    certClass (coefficient p k) = coefficientClass p k := by
  induction p generalizing k with
  | nil => rfl
  | cons a p ih => cases k with
      | zero => rfl
      | succ k => exact ih k

theorem coefficient_equiv {p q : Coefficients} (h : Equivalent p q) (k : Nat) :
    (coefficient p k).raw.Equiv (coefficient q k).raw := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
  change certClass (coefficient p k) = certClass (coefficient q k)
  rw [coefficient_class,coefficient_class]
  exact (equivalent_classes h).2 k

theorem coefficient_linearMultiply_zero (r : ComplexCert) (p : Coefficients) :
    (coefficient (linearMultiply r p) 0).raw.Equiv (mul (neg r) (coefficient p 0)).raw := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
  change certClass (coefficient (linearMultiply r p) 0) = certClass (mul (neg r) (coefficient p 0))
  simp only [coefficient_class,coefficientClass_linear_zero,class_mul,class_neg]

theorem coefficient_linearMultiply_succ (r : ComplexCert) (p : Coefficients) (k : Nat) :
    (coefficient (linearMultiply r p) (k+1)).raw.Equiv
      (add (mul (neg r) (coefficient p (k+1))) (coefficient p k)).raw := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
  change certClass (coefficient (linearMultiply r p) (k+1)) =
    certClass (add (mul (neg r) (coefficient p (k+1))) (coefficient p k))
  simp only [coefficient_class,coefficientClass_linear_succ,class_add,class_mul,class_neg]

end ComputableAnalysis.RepresentedPolynomial
