import ComputableAnalysis.FTA.RootPolynomial

namespace ComputableAnalysis.RepresentedPolynomial
open Arithmetic

/-- Equivalent supplied roots and arguments give the same product value. -/
theorem rootProduct_equiv {rs ss : List ComplexCert} (h : Equivalent rs ss)
    {z w : ComplexCert} (hz : z.raw.Equiv w.raw) :
    (rootProduct rs z).raw.Equiv (rootProduct ss w).raw := by
  induction h with
  | nil => exact certRefl one
  | @cons r s rs ss hrs _ ih =>
      exact certMulCongr (certAddCongr hz (ComplexRaw.neg_equiv hrs)) ih

/-- Ordering supplied roots does not affect the polynomial's value. -/
theorem rootProduct_perm {rs ss : List ComplexCert} (h : rs.Perm ss) (z : ComplexCert) :
    (rootProduct rs z).raw.Equiv (rootProduct ss z).raw := by
  induction h with
  | nil => exact certRefl one
  | cons r _ ih => exact certMulCongr (certRefl _) ih
  | swap r s rs =>
      apply Expression.equiv_of_samples
        (.mul (.parameter (sub z s)) (.mul (.parameter (sub z r)) (.parameter (rootProduct rs z))))
        (.mul (.parameter (sub z r)) (.mul (.parameter (sub z s)) (.parameter (rootProduct rs z))))
      intro t
      have ext {a b : QComplex} (hr : a.re = b.re) (hi : a.im = b.im) : a = b := by
        cases a; cases b; simp_all
      apply ext <;> simp [Expression.sample, QComplex.mul] <;> grind
  | trans _ _ ih₁ ih₂ => exact certTrans ih₁ ih₂

theorem eval_rootPolynomial_perm {rs ss : List ComplexCert} (h : rs.Perm ss)
    (z : ComplexCert) :
    (eval (rootPolynomial rs) z).raw.Equiv (eval (rootPolynomial ss) z).raw :=
  certTrans (eval_rootPolynomial rs z)
    (certTrans (rootProduct_perm h z) (ComplexRaw.equiv_symm (eval_rootPolynomial ss z)))

theorem eval_rootPolynomial_equiv {rs ss : List ComplexCert} (h : Equivalent rs ss)
    {z w : ComplexCert} (hz : z.raw.Equiv w.raw) :
    (eval (rootPolynomial rs) z).raw.Equiv (eval (rootPolynomial ss) w).raw :=
  certTrans (eval_rootPolynomial rs z)
    (certTrans (rootProduct_equiv h hz) (ComplexRaw.equiv_symm (eval_rootPolynomial ss w)))

theorem equivalent_ofFn {n : Nat} (f g : Fin n → ComplexCert)
    (h : ∀ i, (f i).raw.Equiv (g i).raw) : Equivalent (List.ofFn f) (List.ofFn g) := by
  induction n with
  | zero =>
      simp
      exact .nil
  | succ n ih =>
      rw [List.ofFn_succ, List.ofFn_succ]
      exact .cons (h 0) (ih _ _ (fun i => h i.succ))

end ComputableAnalysis.RepresentedPolynomial
