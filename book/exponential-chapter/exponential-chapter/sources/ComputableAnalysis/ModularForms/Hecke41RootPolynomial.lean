import ComputableAnalysis.ModularForms.Hecke41PointReindexing
import ComputableAnalysis.FTA.RootPolynomialCoefficients

namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory RepresentedPolynomial

/-- Only actual evaluator domains are supplied; invariance is proved below. -/
def hecke41JCert (z : Scalar) (hd : ∀ i, latticeJMap.domain (hecke41Point i z))
    (i : Fin 42) : ComplexCert :=
  ⟨(latticeJMap.eval (hecke41Point i z) (hd i)).val,
    (latticeJMap.eval (hecke41Point i z) (hd i)).property⟩

def hecke41RootPolynomial (z : Scalar) (hd : ∀ i, latticeJMap.domain (hecke41Point i z)) :
    Coefficients := rootPolynomial (List.ofFn (hecke41JCert z hd))

private theorem S_index_perm :
    (List.ofFn hecke41SIndex).Perm (List.ofFn (fun i : Fin 42 => i)) := by
  decide +kernel

private theorem T_index_perm :
    (List.ofFn hecke41TIndex).Perm (List.ofFn (fun i : Fin 42 => i)) := by
  decide +kernel

theorem hecke41RootPolynomial_monic (z : Scalar)
    (hd : ∀ i, latticeJMap.domain (hecke41Point i z)) : Monic (hecke41RootPolynomial z hd) :=
  rootPolynomial_monic _

theorem hecke41RootPolynomial_length (z : Scalar)
    (hd : ∀ i, latticeJMap.domain (hecke41Point i z)) : (hecke41RootPolynomial z hd).length = 43 := by
  simp [hecke41RootPolynomial, rootPolynomial_length]

theorem hecke41RootPolynomial_S_domain (z : Scalar) (hz : InUpperHalfPlane z.val)
    (hd : ∀ i, latticeJMap.domain (hecke41Point i z)) (i : Fin 42) :
    latticeJMap.domain (hecke41Point i (fractionalLinear SL2Z.S z hz)) :=
  hecke41Point_reindex_j_domain i (hecke41SIndex i) SL2Z.S (hecke41SWitness i)
    (hecke41S_reindex i) z hz (hd _)

theorem hecke41RootPolynomial_T_domain (z : Scalar) (hz : InUpperHalfPlane z.val)
    (hd : ∀ i, latticeJMap.domain (hecke41Point i z)) (i : Fin 42) :
    latticeJMap.domain (hecke41Point i (fractionalLinear SL2Z.T z hz)) :=
  hecke41Point_reindex_j_domain i (hecke41TIndex i) SL2Z.T (hecke41TWitness i)
    (hecke41T_reindex i) z hz (hd _)

private theorem eval_reindex (f g : Fin 42 → ComplexCert) (p : Fin 42 → Fin 42)
    (hp : (List.ofFn p).Perm (List.ofFn (fun i : Fin 42 => i)))
    (h : ∀ i, (f i).raw.Equiv (g (p i)).raw) (x : ComplexCert) :
    (eval (rootPolynomial (List.ofFn f)) x).raw.Equiv
      (eval (rootPolynomial (List.ofFn g)) x).raw := by
  have he := eval_rootPolynomial_equiv (equivalent_ofFn f (fun i => g (p i)) h) (certRefl x)
  have hm := hp.map g
  simp only [List.map_ofFn, Function.comp_def] at hm
  exact certTrans he (eval_rootPolynomial_perm hm x)

/-- Actual root polynomial evaluation is invariant under the modular generator S. -/
theorem hecke41RootPolynomial_S (z : Scalar) (hz : InUpperHalfPlane z.val)
    (hd : ∀ i, latticeJMap.domain (hecke41Point i z)) (x : ComplexCert) :
    (eval (hecke41RootPolynomial (fractionalLinear SL2Z.S z hz)
      (hecke41RootPolynomial_S_domain z hz hd)) x).raw.Equiv
      (eval (hecke41RootPolynomial z hd) x).raw := by
  apply eval_reindex _ _ hecke41SIndex S_index_perm
  intro i
  exact hecke41Point_reindex_j i (hecke41SIndex i) SL2Z.S (hecke41SWitness i)
    (hecke41S_reindex i) z hz (hd _)

/-- Actual root polynomial evaluation is invariant under the modular generator T. -/
theorem hecke41RootPolynomial_T (z : Scalar) (hz : InUpperHalfPlane z.val)
    (hd : ∀ i, latticeJMap.domain (hecke41Point i z)) (x : ComplexCert) :
    (eval (hecke41RootPolynomial (fractionalLinear SL2Z.T z hz)
      (hecke41RootPolynomial_T_domain z hz hd)) x).raw.Equiv
      (eval (hecke41RootPolynomial z hd) x).raw := by
  apply eval_reindex _ _ hecke41TIndex T_index_perm
  intro i
  exact hecke41Point_reindex_j i (hecke41TIndex i) SL2Z.T (hecke41TWitness i)
    (hecke41T_reindex i) z hz (hd _)

private theorem coefficient_reindex (f g : Fin 42 → ComplexCert) (p : Fin 42 → Fin 42)
    (hp : (List.ofFn p).Perm (List.ofFn (fun i : Fin 42 => i)))
    (h : ∀ i, (f i).raw.Equiv (g (p i)).raw) :
    Equivalent (rootPolynomial (List.ofFn f)) (rootPolynomial (List.ofFn g)) := by
  have he := rootPolynomial_equivalent (equivalent_ofFn f (fun i => g (p i)) h)
  have hm := hp.map g
  simp only [List.map_ofFn, Function.comp_def] at hm
  have ht := rootPolynomial_perm hm
  have trans {p q t : Coefficients} (hpq : Equivalent p q) (hqt : Equivalent q t) : Equivalent p t := by
    induction hpq generalizing t with
    | nil => cases hqt; exact .nil
    | cons hab _ ih =>
        cases hqt with
        | cons hbc hqt => exact .cons (certTrans hab hbc) (ih hqt)
  exact trans he ht

/-- Every coefficient value is invariant under the modular generator S. -/
theorem hecke41RootPolynomial_S_coefficients (z : Scalar) (hz : InUpperHalfPlane z.val)
    (hd : ∀ i, latticeJMap.domain (hecke41Point i z)) :
    Equivalent (hecke41RootPolynomial (fractionalLinear SL2Z.S z hz)
      (hecke41RootPolynomial_S_domain z hz hd)) (hecke41RootPolynomial z hd) := by
  apply coefficient_reindex _ _ hecke41SIndex S_index_perm
  intro i
  exact hecke41Point_reindex_j i (hecke41SIndex i) SL2Z.S (hecke41SWitness i)
    (hecke41S_reindex i) z hz (hd _)

/-- Every coefficient value is invariant under the modular generator T. -/
theorem hecke41RootPolynomial_T_coefficients (z : Scalar) (hz : InUpperHalfPlane z.val)
    (hd : ∀ i, latticeJMap.domain (hecke41Point i z)) :
    Equivalent (hecke41RootPolynomial (fractionalLinear SL2Z.T z hz)
      (hecke41RootPolynomial_T_domain z hz hd)) (hecke41RootPolynomial z hd) := by
  apply coefficient_reindex _ _ hecke41TIndex T_index_perm
  intro i
  exact hecke41Point_reindex_j i (hecke41TIndex i) SL2Z.T (hecke41TWitness i)
    (hecke41T_reindex i) z hz (hd _)

end ComputableAnalysis.ModularForms
