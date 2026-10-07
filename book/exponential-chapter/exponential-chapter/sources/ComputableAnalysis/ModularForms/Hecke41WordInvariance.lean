import ComputableAnalysis.ModularForms.Hecke41RootPolynomial

namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory RepresentedPolynomial

private theorem coefficient_trans {p q t : Coefficients}
    (hpq : Equivalent p q) (hqt : Equivalent q t) : Equivalent p t := by
  induction hpq generalizing t with
  | nil => cases hqt; exact .nil
  | cons hab _ ih =>
      cases hqt with
      | cons hbc hqt => exact .cons (certTrans hab hbc) (ih hqt)

/-- Correspondence evaluator domains respect represented equality. -/
theorem hecke41RootPolynomial_domain_congr (z w : Scalar) (he : z.val.Equiv w.val)
    (hd : ∀ i, latticeJMap.domain (hecke41Point i z)) (i : Fin 42) :
    latticeJMap.domain (hecke41Point i w) :=
  (latticeJMap.domain_congr _ _ (hecke41Point_congr i z w he)).mp (hd i)

/-- Every coefficient respects represented equality of the underlying point. -/
theorem hecke41RootPolynomial_congr (z w : Scalar) (he : z.val.Equiv w.val)
    (hdz : ∀ i, latticeJMap.domain (hecke41Point i z))
    (hdw : ∀ i, latticeJMap.domain (hecke41Point i w)) :
    Equivalent (hecke41RootPolynomial z hdz) (hecke41RootPolynomial w hdw) := by
  apply rootPolynomial_equivalent
  apply equivalent_ofFn
  intro i
  exact latticeJMap.eval_congr _ _ (hdz i) (hdw i) (hecke41Point_congr i z w he)

/-- Literal finite words in the two standard modular matrices. -/
inductive ModularWord where
  | identity
  | S
  | T
  | multiply (g h : ModularWord)

def ModularWord.matrix : ModularWord → SL2Z
  | .identity => SL2Z.identity
  | .S => SL2Z.S
  | .T => SL2Z.T
  | .multiply g h => SL2Z.multiply g.matrix h.matrix

/-- Domain transport along a word is constructed, using actual action composition. -/
theorem hecke41RootPolynomial_word_domain (g : ModularWord) (z : Scalar)
    (hz : InUpperHalfPlane z.val) (hd : ∀ i, latticeJMap.domain (hecke41Point i z)) :
    ∀ i, latticeJMap.domain (hecke41Point i (fractionalLinear g.matrix z hz)) := by
  induction g generalizing z with
  | identity =>
      exact hecke41RootPolynomial_domain_congr z _ (equiv_symm (fractionalLinear_identity z hz)) hd
  | S => exact hecke41RootPolynomial_S_domain z hz hd
  | T => exact hecke41RootPolynomial_T_domain z hz hd
  | multiply g h ihg ihh =>
      have hd₁ := ihh z hz hd
      have hd₂ := ihg (fractionalLinear h.matrix z hz) (fractionalLinear_mem h.matrix z hz) hd₁
      exact hecke41RootPolynomial_domain_congr _ _ (fractionalLinear_compose g.matrix h.matrix z hz) hd₂

/-- Exact coefficient invariance for every supplied finite modular word. -/
theorem hecke41RootPolynomial_word_coefficients (g : ModularWord) (z : Scalar)
    (hz : InUpperHalfPlane z.val) (hd : ∀ i, latticeJMap.domain (hecke41Point i z)) :
    Equivalent (hecke41RootPolynomial (fractionalLinear g.matrix z hz)
      (hecke41RootPolynomial_word_domain g z hz hd)) (hecke41RootPolynomial z hd) := by
  induction g generalizing z with
  | identity => exact hecke41RootPolynomial_congr _ z (fractionalLinear_identity z hz) _ hd
  | S => exact hecke41RootPolynomial_S_coefficients z hz hd
  | T => exact hecke41RootPolynomial_T_coefficients z hz hd
  | multiply g h ihg ihh =>
      have hd₁ := hecke41RootPolynomial_word_domain h z hz hd
      have hd₂ := hecke41RootPolynomial_word_domain g (fractionalLinear h.matrix z hz)
        (fractionalLinear_mem h.matrix z hz) hd₁
      have hc := hecke41RootPolynomial_congr _ _
        (equiv_symm (fractionalLinear_compose g.matrix h.matrix z hz))
        (hecke41RootPolynomial_word_domain (.multiply g h) z hz hd) hd₂
      exact coefficient_trans hc (coefficient_trans
        (ihg (fractionalLinear h.matrix z hz) (fractionalLinear_mem h.matrix z hz) hd₁)
        (ihh z hz hd))

/-- Inverse generators expressed using literal positive words. -/
def ModularWord.inverseS : ModularWord := .multiply (.multiply .S .S) .S

def ModularWord.inverseT : ModularWord :=
  .multiply (.multiply (.multiply (.multiply (.multiply (.multiply .S .T) .S) .T) .S) .S) .S

theorem ModularWord.inverseS_matrix : inverseS.matrix = SL2Z.inverse SL2Z.S := by
  rfl

theorem ModularWord.inverseT_matrix : inverseT.matrix = SL2Z.inverse SL2Z.T := by
  rfl

end ComputableAnalysis.ModularForms
