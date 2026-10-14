import ComputableAnalysis.RiemannHilbert.LogarithmContinuationRefinement

/-! The actual logarithm increment of a finite chart chain. Its relation
to continued germ values, concatenation, admissible refinement and represented
names is proved; the scalar exponential is the endpoint ratio. -/
namespace ComputableAnalysis.RiemannHilbert.LogarithmContinuation
open ComplexRaw FunctionTheory LocalODE DomainFunctions NonzeroBoxSearch
set_option maxHeartbeats 1000000
set_option autoImplicit false

def increment {c d : Scalar} {hc : Nonzero c} {hd : Nonzero d} : Chain c hc d hd → Scalar
  | .nil _ _ => ⟨zero,ofQComplex_valid _⟩
  | @Chain.step c d e hc _ _ hcd tail => scalarSum ((RelativeLogarithm.function c hc).eval d hcd) (increment tail)

theorem value_increment {c d : Scalar} {hc : Nonzero c} {hd : Nonzero d}
    (p : Chain c hc d hd) (a : Scalar) : (value p a).val.Equiv (scalarSum a (increment p)).val := by
  induction p generalizing a with
  | nil => exact equiv_symm (add_zero_equiv _ a.property)
  | @step c d e hc hd he hcd tail ih =>
      have h := ih ((LogarithmBranchCharts.function c hc a).eval d hcd)
      apply equiv_trans (value (.step hcd tail) a).property
        (scalarSum ((LogarithmBranchCharts.function c hc a).eval d hcd) (increment tail)).property
        (scalarSum a (increment (.step hcd tail))).property h
      apply ComplexRawQuotient.equiv_of_ofRaw_eq
        (hleft := (scalarSum ((LogarithmBranchCharts.function c hc a).eval d hcd) (increment tail)).property)
        (hright := (scalarSum a (increment (.step hcd tail))).property)
      let A := ComplexRawQuotient.ofRaw a.val a.property
      let L := ComplexRawQuotient.ofRaw ((RelativeLogarithm.function c hc).eval d hcd).val
        ((RelativeLogarithm.function c hc).eval d hcd).property
      let T := ComplexRawQuotient.ofRaw (increment tail).val (increment tail).property
      change (A+L)+T=A+(L+T)
      grind only

theorem increment_value {c d : Scalar} {hc : Nonzero c} {hd : Nonzero d}
    (p : Chain c hc d hd) : (increment p).val.Equiv (value p ⟨zero,ofQComplex_valid _⟩).val :=
  equiv_symm (equiv_trans (value p ⟨zero,ofQComplex_valid _⟩).property
    (add_valid (ofQComplex_valid _) (increment p).property) (increment p).property
    (value_increment p _) (zero_add_equiv _ (increment p).property))

theorem increment_append {c d e : Scalar} {hc : Nonzero c} {hd : Nonzero d} {he : Nonzero e}
    (p : Chain c hc d hd) (q : Chain d hd e he) :
    (increment (append p q)).val.Equiv (scalarSum (increment p) (increment q)).val := by
  induction p with
  | nil => exact equiv_symm (zero_add_equiv _ (increment q).property)
  | @step c d f hc hd hf hcd tail ih =>
      have h := add_equiv (equiv_refl _ ((RelativeLogarithm.function c hc).eval d hcd).property) (ih q)
      apply equiv_trans (increment (append (.step hcd tail) q)).property
        (scalarSum ((RelativeLogarithm.function c hc).eval d hcd) (scalarSum (increment tail) (increment q))).property
        (scalarSum (increment (.step hcd tail)) (increment q)).property h
      exact equiv_symm (add_assoc_equiv _ _ _ ((RelativeLogarithm.function c hc).eval d hcd).property
        (increment tail).property (increment q).property)

theorem increment_refines {c d : Scalar} {hc : Nonzero c} {hd : Nonzero d}
    {p q : Chain c hc d hd} (h : Refines p q) : (increment p).val.Equiv (increment q).val :=
  equiv_trans (increment p).property (value p ⟨zero,ofQComplex_valid _⟩).property (increment q).property (increment_value p)
    (equiv_trans (value p ⟨zero,ofQComplex_valid _⟩).property (value q ⟨zero,ofQComplex_valid _⟩).property (increment q).property
      (value_refines h _) (equiv_symm (increment_value q)))

theorem increment_rename (g : Scalar → Scalar) (hg : ∀ z, (g z).val.Equiv z.val)
    {c d : Scalar} {hc : Nonzero c} {hd : Nonzero d} (p : Chain c hc d hd) :
    (increment p).val.Equiv (increment (rename g hg p)).val :=
  equiv_trans (increment p).property (value p ⟨zero,ofQComplex_valid _⟩).property (increment (rename g hg p)).property (increment_value p)
    (equiv_trans (value p ⟨zero,ofQComplex_valid _⟩).property
      (value (rename g hg p) ⟨zero,ofQComplex_valid _⟩).property (increment (rename g hg p)).property
      (value_rename g hg p _ _ (equiv_refl _ (ofQComplex_valid _))) (equiv_symm (increment_value _)))

theorem increment_exponential {c d : Scalar} {hc : Nonzero c} {hd : Nonzero d}
    (p : Chain c hc d hd) : (MatrixExponential.scalarExponential (increment p)).val.Equiv
      (mul (RepresentedReciprocal.inverse c hc).val d.val) := by
  induction p with
  | nil c hc =>
      exact equiv_trans (MatrixExponential.scalarExponential (increment (.nil c hc))).property
        (ofQComplex_valid _) (mul_valid (RepresentedReciprocal.inverse c hc).property c.property)
        MatrixExponential.scalarExponential_zero (equiv_symm (RepresentedReciprocal.inverse_mul c hc))
  | @step c d e hc hd he hcd tail ih =>
      let L := (RelativeLogarithm.function c hc).eval d hcd
      have hmul := mul_equiv (MatrixExponential.scalarExponential L).property
        (mul_valid (RepresentedReciprocal.inverse c hc).property d.property)
        (MatrixExponential.scalarExponential (increment tail)).property
        (mul_valid (RepresentedReciprocal.inverse d hd).property e.property)
        (MatrixExponential.scalarExponential_relative c hc d hcd) ih
      have hcancel : (mul (mul (RepresentedReciprocal.inverse c hc).val d.val)
          (mul (RepresentedReciprocal.inverse d hd).val e.val)).Equiv
          (mul (RepresentedReciprocal.inverse c hc).val e.val) := by
        apply ComplexRawQuotient.equiv_of_ofRaw_eq
          (hleft := mul_valid (mul_valid (RepresentedReciprocal.inverse c hc).property d.property)
            (mul_valid (RepresentedReciprocal.inverse d hd).property e.property))
          (hright := mul_valid (RepresentedReciprocal.inverse c hc).property e.property)
        have hi := ComplexRawQuotient.ofRaw_eq_ofRaw
          (hleft := mul_valid d.property (RepresentedReciprocal.inverse d hd).property) (hright := ofQComplex_valid _)
          (RepresentedReciprocal.mul_inverse d hd)
        let C := ComplexRawQuotient.ofRaw (RepresentedReciprocal.inverse c hc).val (RepresentedReciprocal.inverse c hc).property
        let D := ComplexRawQuotient.ofRaw d.val d.property
        let R := ComplexRawQuotient.ofRaw (RepresentedReciprocal.inverse d hd).val (RepresentedReciprocal.inverse d hd).property
        let E := ComplexRawQuotient.ofRaw e.val e.property
        change D*R=1 at hi
        change (C*D)*(R*E)=C*E
        grind only
      exact equiv_trans (MatrixExponential.scalarExponential (increment (.step hcd tail))).property
        (mul_valid (MatrixExponential.scalarExponential L).property (MatrixExponential.scalarExponential (increment tail)).property)
        (mul_valid (RepresentedReciprocal.inverse c hc).property e.property)
        (MatrixExponential.scalarExponential_add L (increment tail))
        (equiv_trans
          (mul_valid (MatrixExponential.scalarExponential L).property (MatrixExponential.scalarExponential (increment tail)).property)
          (mul_valid (mul_valid (RepresentedReciprocal.inverse c hc).property d.property)
            (mul_valid (RepresentedReciprocal.inverse d hd).property e.property))
          (mul_valid (RepresentedReciprocal.inverse c hc).property e.property) hmul hcancel)

end ComputableAnalysis.RiemannHilbert.LogarithmContinuation
