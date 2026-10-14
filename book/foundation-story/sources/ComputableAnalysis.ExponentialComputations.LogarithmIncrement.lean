import ComputableAnalysis.ExponentialComputations.PositiveLogarithm
import ComputableAnalysis.ExponentialComputations.LogarithmRemainder
import ComputableAnalysis.ModularForms.PositiveReciprocalAgreement

/-! A quantitative increment law for the global real logarithm, proved from
its constructed local power series and the already checked inverse laws. -/
namespace ComputableAnalysis.ExponentialComputations
open ComplexRaw FunctionTheory RiemannHilbert LocalODE DomainFunctions ModularForms
set_option maxHeartbeats 1000000

private theorem real_embedding_bound {z : ComplexRaw} {R : Rat}
    (hR : 0 ≤ R) (h : Small z R) : Small (ofRealRaw z.realPart) R := by
  refine ⟨h.1,h.2.1,?_,?_⟩
  · intro n m; change -R ≤ 0; grind only
  · intro n m; exact hR

/-- The normalized coordinate is the reciprocal times the displacement. -/
theorem relativePoint_displacement (c z : Scalar) (hc : NonzeroBoxSearch.Nonzero c) :
    (RelativeLogarithm.point c hc z).val.Equiv
      (mul (RepresentedReciprocal.inverse c hc).val (sub z.val c.val)) := by
  have hi := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid (RepresentedReciprocal.inverse c hc).property c.property)
    (hright := ofQComplex_valid _) (RepresentedReciprocal.inverse_mul c hc)
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (RelativeLogarithm.point c hc z).property)
    (hright := mul_valid (RepresentedReciprocal.inverse c hc).property (sub_valid z.property c.property))
  let C := ComplexRawQuotient.ofRaw c.val c.property
  let Z := ComplexRawQuotient.ofRaw z.val z.property
  let I := ComplexRawQuotient.ofRaw (RepresentedReciprocal.inverse c hc).val
    (RepresentedReciprocal.inverse c hc).property
  change I*C=1 at hi
  change -1+I*Z=I*(Z-C)
  grind only

/-- The global real logarithm increment agrees with its computed local chart. -/
theorem log_increment (c z : PositiveInput)
    (hz : RelativeLogarithm.domain (realAxis c.val) (positive_real_nonzero c.val c.property) (realAxis z.val)) :
    (RealRaw.sub (log z).val (log c).val).Equiv
      (((RelativeLogarithm.function (realAxis c.val) (positive_real_nonzero c.val c.property)).eval
        (realAxis z.val) hz).val.realPart) := by
  let C := realAxis c.val
  let hc := positive_real_nonzero c.val c.property
  let L := (RelativeLogarithm.function C hc).eval (realAxis z.val) hz
  let A := MatrixExponential.propagatedBranch C hc (complexLog c) (realAxis z.val) hz
  have hexp := entireExponential_propagatedLogarithm C hc (complexLog c) (complexLog_exponential c)
    (realAxis z.val) hz
  have h := entireExponential_fiber_realPart A (complexLog z)
    (equiv_trans (entireExponentialValue A).property (realAxis z.val).property
      (entireExponentialValue (complexLog z)).property hexp (equiv_symm (complexLog_exponential z)))
  have hsum : (RealRaw.add (log c).val L.val.realPart).Equiv (log z).val := h
  exact RealRaw.equiv_trans
    (RealRaw.sub_valid (log z).property (log c).property)
    (RealRaw.sub_valid (RealRaw.add_valid (log c).property (realPart_valid L.property)) (log c).property)
    (realPart_valid L.property)
    (RealRaw.sub_equiv (log z).property (RealRaw.add_valid (log c).property (realPart_valid L.property))
      (log c).property (log c).property (RealRaw.equiv_symm hsum) (RealRaw.equiv_refl _ (log c).property))
    (RealRaw.add_sub_cancel_left_equiv (log c).property (realPart_valid L.property))

/-- A quadratic logarithm remainder with any justified bound on the actual
reciprocal. The conclusion is about the global logarithm on positive inputs. -/
theorem log_increment_error (c z : PositiveInput) (B H : Rat) (hB : 0 ≤ B) (hH : 0 ≤ H)
    (hi : Small (RepresentedReciprocal.inverse (realAxis c.val)
      (positive_real_nonzero c.val c.property)).val B)
    (hstep : Small (sub (realAxis z.val).val (realAxis c.val).val) H)
    (hmesh : 2*B*H ≤ (1:Rat)/128) :
    Small (ofRealRaw (RealRaw.sub (RealRaw.sub (log z).val (log c).val)
      (mul (RepresentedReciprocal.inverse (realAxis c.val)
        (positive_real_nonzero c.val c.property)).val
        (sub (realAxis z.val).val (realAxis c.val).val)).realPart)) (16*(2*B*H)^2) := by
  let C := realAxis c.val
  let Z := realAxis z.val
  let hc := positive_real_nonzero c.val c.property
  let w := RelativeLogarithm.point C hc Z
  let d : Scalar := ⟨mul (RepresentedReciprocal.inverse C hc).val (sub Z.val C.val),
    mul_valid (RepresentedReciprocal.inverse C hc).property (sub_valid Z.property C.property)⟩
  have hwd := relativePoint_displacement C Z hc
  have hb := Small.mul (RepresentedReciprocal.inverse C hc).property (sub_valid Z.property C.property)
    hB hH hi hstep
  have hw : Small w.val (2*B*H) :=
    Small.congr d.property w.property (equiv_symm hwd) hb
  have hsize : 0 ≤ 2*B*H := Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) hB) hH
  have hz : RelativeLogarithm.domain C hc Z :=
    ⟨2*B*H,hsize,by change 2*B*H<(1:Rat)/32; grind only,hw⟩
  let L := LocalLogarithm.function.eval w hz
  have he := localLogarithm_linear_error w hz (2*B*H) hsize hw
  have hinc := log_increment c z hz
  have hdiff := RealRaw.sub_equiv
    (RealRaw.sub_valid (log z).property (log c).property) (realPart_valid L.property)
    (realPart_valid d.property) (realPart_valid w.property) hinc (RealRaw.equiv_symm (realPart_equiv hwd))
  have hdiff' : (RealRaw.sub (RealRaw.sub (log z).val (log c).val) d.val.realPart).Equiv
      (sub L.val w.val).realPart := by
    intro n
    have hh := (RealRaw.compareAt_overlap_iff _ _ n n).mp (hdiff n)
    apply (RealRaw.compareAt_overlap_iff _ _ n n).mpr
    change (((log z).val.compute n).lo-((log c).val.compute n).hi)-(d.val.compute n).hi.re ≤
        (L.val.compute n).hi.re + -(w.val.compute n).lo.re ∧
      (L.val.compute n).lo.re + -(w.val.compute n).hi.re ≤
        (((log z).val.compute n).hi-((log c).val.compute n).lo)-(d.val.compute n).lo.re
    change (((log z).val.compute n).lo-((log c).val.compute n).hi)-(d.val.compute n).hi.re ≤
        (L.val.compute n).hi.re-(w.val.compute n).lo.re ∧
      (L.val.compute n).lo.re-(w.val.compute n).hi.re ≤
        (((log z).val.compute n).hi-((log c).val.compute n).lo)-(d.val.compute n).lo.re at hh
    simpa only [Rat.sub_eq_add_neg] using hh
  have hemb := ofRealRaw_equiv_of_equiv
    (RealRaw.sub_valid (RealRaw.sub_valid (log z).property (log c).property) (realPart_valid d.property))
    (realPart_valid (sub_valid L.property w.property)) hdiff'
  exact Small.congr (ofRealRaw_valid _ (realPart_valid (sub_valid L.property w.property)))
    (ofRealRaw_valid _ (RealRaw.sub_valid (RealRaw.sub_valid (log z).property (log c).property)
      (realPart_valid d.property))) (equiv_symm hemb)
    (real_embedding_bound (Rat.mul_nonneg (by decide +kernel) (Rat.pow_nonneg hsize)) he)
end ComputableAnalysis.ExponentialComputations
