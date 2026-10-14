import ComputableAnalysis.ModularForms.ExponentialNegativeSeparation
import ComputableAnalysis.ModularForms.ExponentialInverse

/-! The real coordinate is constant on each actual exponential fiber.
No global classification of the imaginary periods is assumed. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert
private def scalarClass (z : Scalar) := ComplexRawQuotient.ofRaw z.val z.property

/-- Negation preserves membership in the actual exponential kernel. -/
theorem entireExponential_kernel_neg (z : Scalar)
    (he : (entireExponentialValue z).val.Equiv one) :
    (entireExponentialValue ⟨neg z.val,neg_valid z.property⟩).val.Equiv one := by
  have hp := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid (entireExponentialValue z).property
      (entireExponentialValue ⟨neg z.val,neg_valid z.property⟩).property)
    (hright := ofQComplex_valid _) (entireExponential_inverse z)
  have hz := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := (entireExponentialValue z).property) (hright := ofQComplex_valid _) he
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (entireExponentialValue ⟨neg z.val,neg_valid z.property⟩).property)
    (hright := ofQComplex_valid _)
  let Z := scalarClass (entireExponentialValue z)
  let W := scalarClass (entireExponentialValue ⟨neg z.val,neg_valid z.property⟩)
  change Z*W=1 at hp
  change Z=1 at hz
  change W=1
  grind only

/-- Every actual exponential kernel element has exactly zero real part. -/
theorem entireExponential_kernel_real_zero (z : Scalar)
    (he : (entireExponentialValue z).val.Equiv one) :
    z.val.realPart.Equiv (RealRaw.ofRat 0) := by
  have hn : ¬ (RealRaw.neg z.val.realPart).Pos :=
    fun hp => entireExponential_negative_realPart_ne_one z hp he
  have hp : ¬ z.val.realPart.Pos := by
    intro hp
    let w : Scalar := ⟨neg z.val,neg_valid z.property⟩
    have hwp : (RealRaw.neg w.val.realPart).Pos := by
      obtain ⟨N,hN⟩ := hp
      refine ⟨N,?_⟩
      change 0< -(-((z.val.compute N).lo.re))
      change 0<(z.val.compute N).lo.re at hN
      grind only
    exact entireExponential_negative_realPart_ne_one w hwp (entireExponential_kernel_neg z he)
  intro n
  apply (RealRaw.compareAt_overlap_iff _ _ n n).mpr
  have hl : (z.val.compute n).lo.re≤0 := by
    have h : ¬0<(z.val.compute n).lo.re := fun h => hp ⟨n,h⟩
    grind only
  have hh : 0≤(z.val.compute n).hi.re := by
    have h : ¬0< -((z.val.compute n).hi.re) := fun h => hn ⟨n,h⟩
    grind only
  exact ⟨hl,hh⟩

/-- Equal actual exponential values make the input difference a kernel element. -/
theorem entireExponential_fiber_difference (z w : Scalar)
    (he : (entireExponentialValue z).val.Equiv (entireExponentialValue w).val) :
    (entireExponentialValue ⟨sub z.val w.val,sub_valid z.property w.property⟩).val.Equiv one := by
  let d : Scalar := ⟨sub z.val w.val,sub_valid z.property w.property⟩
  have hsum : (DomainFunctions.scalarSum d w).val.Equiv z.val := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := (DomainFunctions.scalarSum d w).property) (hright := z.property)
    let Z := scalarClass z
    let W := scalarClass w
    change (Z-W)+W=Z
    grind only
  have hprod := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid (entireExponentialValue d).property (entireExponentialValue w).property)
    (hright := (entireExponentialValue (DomainFunctions.scalarSum d w)).property)
    (entireExponential_addition d w)
  have hsame := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := (entireExponentialValue (DomainFunctions.scalarSum d w)).property)
    (hright := (entireExponentialValue w).property)
    (equiv_trans (entireExponentialValue (DomainFunctions.scalarSum d w)).property
      (entireExponentialValue z).property (entireExponentialValue w).property
      (entireExponentialValue_congr _ _ hsum) he)
  have hinv := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid (entireExponentialValue w).property
      (entireExponentialValue ⟨neg w.val,neg_valid w.property⟩).property)
    (hright := ofQComplex_valid _) (entireExponential_inverse w)
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (entireExponentialValue d).property) (hright := ofQComplex_valid _)
  let D := scalarClass (entireExponentialValue d)
  let W := scalarClass (entireExponentialValue w)
  let I := scalarClass (entireExponentialValue ⟨neg w.val,neg_valid w.property⟩)
  let E := scalarClass (entireExponentialValue (DomainFunctions.scalarSum d w))
  change D*W=E at hprod
  change E=W at hsame
  change W*I=1 at hinv
  change D=1
  grind only

/-- The real coordinate agrees on every actual exponential fiber, for
arbitrary valid represented inputs and without any separation hypothesis. -/
theorem entireExponential_fiber_realPart (z w : Scalar)
    (he : (entireExponentialValue z).val.Equiv (entireExponentialValue w).val) :
    z.val.realPart.Equiv w.val.realPart := by
  have hz := entireExponential_kernel_real_zero
    ⟨sub z.val w.val,sub_valid z.property w.property⟩
    (entireExponential_fiber_difference z w he)
  intro n
  have h := (RealRaw.compareAt_overlap_iff _ _ n n).mp (hz n)
  apply (RealRaw.compareAt_overlap_iff _ _ n n).mpr
  change (z.val.compute n).lo.re+ -((w.val.compute n).hi.re)≤0 ∧
    0≤(z.val.compute n).hi.re+ -((w.val.compute n).lo.re) at h
  change (z.val.compute n).lo.re≤(w.val.compute n).hi.re ∧
    (w.val.compute n).lo.re≤(z.val.compute n).hi.re
  grind only

end ComputableAnalysis.ModularForms
