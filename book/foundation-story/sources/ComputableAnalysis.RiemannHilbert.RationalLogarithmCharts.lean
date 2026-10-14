import ComputableAnalysis.RiemannHilbert.LogarithmContinuationPaths
import ComputableAnalysis.RiemannHilbert.ReciprocalExamples

/-! Finite rational certificates for genuine logarithm chart membership.
The certificate is connected to the represented reciprocal and normalized
coordinate; rational arithmetic alone is not treated as analytic evidence. -/
namespace ComputableAnalysis.RiemannHilbert.RationalLogarithmCharts
open ComplexRaw FunctionTheory LocalODE NonzeroBoxSearch ReciprocalExamples

def normalized (c d : QComplex) : QComplex :=
  QComplex.add (QComplex.neg QComplex.one) (QComplex.mul (RationalReciprocal.inverse c) d)

theorem raw_normalized (c d : QComplex) :
    (add (neg one) (ofQComplex (QComplex.mul (RationalReciprocal.inverse c) d))).Equiv (ofQComplex (normalized c d)) := by
  intro k
  apply (compareAt_overlap_iff _ _ k k).2
  apply QBox.overlaps_of_common_point (point := normalized c d)
  · have hn := QBox.neg_contains (A := QBox.point QComplex.one) ⟨QComplex.le_refl _,QComplex.le_refl _⟩
    exact QBox.add_contains hn.1 hn.2 (QComplex.le_refl _) (QComplex.le_refl _)
  · exact ⟨QComplex.le_refl _,QComplex.le_refl _⟩

theorem point_value (c d : QComplex) (hc : QComplex.normSq c ≠ 0) :
    (RelativeLogarithm.point (rational c) (rational_nonzero c hc) (rational d)).val.Equiv (ofQComplex (normalized c d)) := by
  have hm := mul_equiv (RepresentedReciprocal.inverse (rational c) (rational_nonzero c hc)).property
    (ofQComplex_valid _) (rational d).property (rational d).property (rational_inverse c hc)
    (equiv_refl _ (rational d).property)
  have hm' := equiv_trans (mul_valid (RepresentedReciprocal.inverse (rational c) (rational_nonzero c hc)).property (rational d).property)
    (mul_valid (ofQComplex_valid _) (rational d).property) (ofQComplex_valid _)
    hm (RationalReciprocal.raw_mul_constants _ d)
  exact equiv_trans (RelativeLogarithm.point (rational c) (rational_nonzero c hc) (rational d)).property
    (add_valid (neg_valid (ofQComplex_valid _)) (ofQComplex_valid _)) (ofQComplex_valid _)
    (add_equiv (equiv_refl _ (neg_valid (ofQComplex_valid _))) hm') (raw_normalized c d)

theorem domain_of_bounds (c d : QComplex) (hc : QComplex.normSq c ≠ 0) (r : Rat)
    (hr : 0 ≤ r) (hR : r < LocalLogarithm.radius.val)
    (hb : -r ≤ (normalized c d).re ∧ (normalized c d).re ≤ r ∧
      -r ≤ (normalized c d).im ∧ (normalized c d).im ≤ r) :
    RelativeLogarithm.domain (rational c) (rational_nonzero c hc) (rational d) := by
  apply Centered.interior_congr LocalLogarithm.radius.val ⟨ofQComplex (normalized c d),ofQComplex_valid _⟩ _
    (equiv_symm (point_value c d hc))
  exact ⟨r,hr,hR,⟨fun _ _ => hb.1,fun _ _ => hb.2.1,fun _ _ => hb.2.2.1,fun _ _ => hb.2.2.2⟩⟩

theorem represented_domain (c d : QComplex) (hc : QComplex.normSq c ≠ 0)
    (z w : Scalar) (hz : Nonzero z) (hzc : z.val.Equiv (rational c).val)
    (hwd : w.val.Equiv (rational d).val)
    (h : RelativeLogarithm.domain (rational c) (rational_nonzero c hc) (rational d)) :
    RelativeLogarithm.domain z hz w :=
  (RelativeLogarithm.domain_congr z (rational c) hz (rational_nonzero c hc) hzc w (rational d) hwd).2 h

end ComputableAnalysis.RiemannHilbert.RationalLogarithmCharts
