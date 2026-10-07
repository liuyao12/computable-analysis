import ComputableAnalysis.FTA.Deflation

/-! The exact algebraic implication from root existence to complete complex
factorization. Root existence is an explicit hypothesis here, not an axiom or
a proved FTA. Multiplicities are retained in the resulting finite root list. -/
namespace ComputableAnalysis.RepresentedPolynomial

def one : ComplexCert := ofQComplex QComplex.one

def Monic (p : Coefficients) : Prop := ∃ q, p = q ++ [one]

def rootProduct : List ComplexCert → ComplexCert → ComplexCert
  | [], _ => one
  | r :: roots, x => mul (sub x r) (rootProduct roots x)

/-- The monic root-existence statement needed for FTA. This names the
statement proved in `RootExistence.lean`; the algebraic implication below
states its dependency explicitly. -/
def MonicRootExistence : Prop :=
  ∀ p : Coefficients, Monic p → 2 ≤ p.length → ∃ z : ComplexCert, Root p z

private theorem trans {a b c : ComplexCert}
    (hab : a.raw.Equiv b.raw) (hbc : b.raw.Equiv c.raw) : a.raw.Equiv c.raw :=
  ComplexRaw.equiv_trans a.valid b.valid c.valid hab hbc

private theorem constant_eval (c x : ComplexCert) : (eval [c] x).raw.Equiv c.raw := by
  apply Arithmetic.Expression.equiv_of_samples
    (.add (.parameter c) (.mul (.parameter x) (.constant QComplex.zero))) (.parameter c)
  intro s
  cases hcs : s c
  simp [Arithmetic.Expression.sample, QComplex.add, QComplex.mul, QComplex.zero, hcs]
  constructor <;> grind

/-- The root predicate does not accept a nonzero constant polynomial. -/
theorem one_has_no_root (x : ComplexCert) : ¬ Root [one] x := by
  intro h
  have hzero := trans (ComplexRaw.equiv_symm (constant_eval one x)) h
  have hstage := (ComplexRaw.compareAt_overlap_iff _ _ 0 0).1 (hzero 0)
  have hbad : (1 : Rat) ≤ 0 := hstage.1.1
  contradiction

/-- The degree-one case is an exact identity for arbitrary represented roots. -/
theorem monic_linear_root (a : ComplexCert) : Root [neg a, one] a := by
  apply Arithmetic.Expression.equiv_of_samples
    (.add (.neg (.parameter a))
      (.mul (.parameter a) (.add (.constant QComplex.one)
        (.mul (.parameter a) (.constant QComplex.zero)))))
    (.constant QComplex.zero)
  intro s
  simp [Arithmetic.Expression.sample, QComplex.add, QComplex.neg,
    QComplex.mul, QComplex.zero, QComplex.one]
  constructor <;> grind

/-- Synthetic division preserves the last coefficient literally. In
particular, dividing a nonconstant monic polynomial leaves a monic quotient. -/
theorem syntheticDivide_monic (r : ComplexCert) (p : Coefficients)
    (hp : Monic p) (hdegree : 2 ≤ p.length) : Monic (syntheticDivide r p).1 := by
  obtain ⟨q, rfl⟩ := hp
  induction q with
  | nil => simp at hdegree
  | cons c q ih =>
      cases q with
      | nil => exact ⟨[], rfl⟩
      | cons d q =>
          obtain ⟨tail, ht⟩ := ih (by simp)
          refine ⟨(syntheticDivide r ((d :: q) ++ [one])).2 :: tail, ?_⟩
          change (syntheticDivide r ((d :: q) ++ [one])).2 ::
            (syntheticDivide r ((d :: q) ++ [one])).1 = _
          rw [ht]
          rfl

private theorem factorization_by_degree (hroot : MonicRootExistence) (n : Nat) :
    ∀ p : Coefficients, Monic p → p.length = n + 1 →
      ∃ roots : List ComplexCert, roots.length = n ∧
        ∀ x : ComplexCert, (eval p x).raw.Equiv (rootProduct roots x).raw := by
  induction n with
  | zero =>
      intro p hp hlen
      obtain ⟨q, rfl⟩ := hp
      have hq : q = [] := by
        have : q.length = 0 := by simpa using hlen
        exact List.length_eq_zero_iff.mp this
      subst q
      exact ⟨[], rfl, fun x => constant_eval one x⟩
  | succ n ih =>
      intro p hp hlen
      have hdegree : 2 ≤ p.length := by omega
      obtain ⟨r, hr⟩ := hroot p hp hdegree
      let q := (syntheticDivide r p).1
      have hq : Monic q := syntheticDivide_monic r p hp hdegree
      have hqlen : q.length = n + 1 := by
        dsimp [q]
        rw [syntheticDivide_length, hlen]
        omega
      obtain ⟨roots, hlength, hfactor⟩ := ih q hq hqlen
      refine ⟨r :: roots, by simp [hlength], ?_⟩
      intro x
      exact trans (syntheticDivide_factor hr x)
        (ComplexRaw.mul_equiv (sub x r).valid (sub x r).valid
          (eval q x).valid (rootProduct roots x).valid
          (ComplexRaw.equiv_refl _ (sub x r).valid) (hfactor x))

/-- If every nonconstant monic polynomial has a root, every monic polynomial
splits completely. The equality holds at every represented complex argument. -/
theorem factorization_of_root_existence (hroot : MonicRootExistence)
    (p : Coefficients) (hp : Monic p) :
    ∃ roots : List ComplexCert, roots.length = p.length - 1 ∧
      ∀ x : ComplexCert, (eval p x).raw.Equiv (rootProduct roots x).raw := by
  have hlen : p.length - 1 + 1 = p.length := by
    obtain ⟨q, rfl⟩ := hp
    simp
  exact factorization_by_degree hroot (p.length - 1) p hp hlen.symm

end ComputableAnalysis.RepresentedPolynomial
