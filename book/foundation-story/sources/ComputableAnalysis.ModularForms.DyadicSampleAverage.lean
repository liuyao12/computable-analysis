import ComputableAnalysis.ModularForms.RationalBisection
import ComputableAnalysis.RiemannHilbert.RepresentedAffineSegments

/-! Executable midpoint averages on rational bisection trees. Local sample
error bounds pass to every refinement without growing with sample count. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert

def dyadicSampleAverage (f : Rat → Scalar) (I : QInterval) : Nat → Scalar
  | 0 => f I.midpoint
  | n+1 =>
    let l := dyadicSampleAverage f (bisectInterval I false) n
    let r := dyadicSampleAverage f (bisectInterval I true) n
    ⟨scaleRat (1/2) (add l.val r.val), scaleRat_valid (add_valid l.property r.property)⟩

theorem midpoint_mem (I : QInterval) (hI : I.lo≤I.hi) :
    I.lo≤I.midpoint ∧ I.midpoint≤I.hi := by
  unfold QInterval.midpoint
  grind only

theorem halfAverage_difference (a b c : Scalar) :
    (sub (scaleRat (1/2) (add a.val b.val)) c.val).Equiv
      (scaleRat (1/2) (add (sub a.val c.val) (sub b.val c.val))) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := sub_valid (scaleRat_valid (add_valid a.property b.property)) c.property)
    (hright := scaleRat_valid (add_valid (sub_valid a.property c.property)
      (sub_valid b.property c.property)))
  let A := ComplexRawQuotient.ofRaw a.val a.property
  let B := ComplexRawQuotient.ofRaw b.val b.property
  let C := ComplexRawQuotient.ofRaw c.val c.property
  change ComplexRawQuotient.scaleRat (1/2) (A+B)-C =
    ComplexRawQuotient.scaleRat (1/2) ((A-C)+(B-C))
  have hc : ComplexRawQuotient.scaleRat (1/2) C+
      ComplexRawQuotient.scaleRat (1/2) C=C := by
    rw [ComplexRawQuotient.add_scaleRat, show (1:Rat)/2+1/2=1 by decide +kernel,
      ComplexRawQuotient.scaleRat_one]
  have hn (X : ScalarAlgebra.Value) :
      ComplexRawQuotient.scaleRat (1/2) (-X)= -ComplexRawQuotient.scaleRat (1/2) X := by
    rw [ComplexRawQuotient.neg_eq_scaleRat_neg_one, ComplexRawQuotient.scaleRat_scaleRat,
      ComplexRawQuotient.neg_scaleRat]
    congr 1
    grind only
  change _=ComplexRawQuotient.scaleRat (1/2) ((A+ -C)+(B+ -C))
  rw [ComplexRawQuotient.scaleRat_add, ComplexRawQuotient.scaleRat_add,
    ComplexRawQuotient.scaleRat_add, hn, ComplexRawQuotient.scaleRat_add]
  grind only

theorem dyadicSampleAverage_error (f : Rat → Scalar) (c : Scalar)
    (I : QInterval) (hI : I.lo≤I.hi) (E : Rat)
    (hlocal : ∀ u : Rat, I.lo≤u → u≤I.hi → Small (sub (f u).val c.val) E)
    (n : Nat) : Small (sub (dyadicSampleAverage f I n).val c.val) E := by
  induction n generalizing I with
  | zero => exact hlocal I.midpoint (midpoint_mem I hI).1 (midpoint_mem I hI).2
  | succ n ih =>
    have hl := bisectInterval_bounds I hI false
    have hr := bisectInterval_bounds I hI true
    have bl := ih (bisectInterval I false) hl.2.1 (by
      intro u hu0 hu1
      exact hlocal u (Rat.le_trans hl.1 hu0) (Rat.le_trans hu1 hl.2.2))
    have br := ih (bisectInterval I true) hr.2.1 (by
      intro u hu0 hu1
      exact hlocal u (Rat.le_trans hr.1 hu0) (Rat.le_trans hu1 hr.2.2))
    have hb := LocalODE.small_scale (by decide +kernel : (0:Rat)≤1/2)
      (LocalODE.small_add bl br)
    have he : (1:Rat)/2*(E+E)=E := by grind only
    rw [he] at hb
    exact Small.congr
      (scaleRat_valid (add_valid
        (sub_valid (dyadicSampleAverage f (bisectInterval I false) n).property c.property)
        (sub_valid (dyadicSampleAverage f (bisectInterval I true) n).property c.property)))
      (sub_valid (dyadicSampleAverage f I (n+1)).property c.property)
      (equiv_symm (halfAverage_difference
        (dyadicSampleAverage f (bisectInterval I false) n)
        (dyadicSampleAverage f (bisectInterval I true) n) c)) hb

theorem dyadicSampleAverage_bound (f : Rat → Scalar) (I : QInterval)
    (B : Rat) (samples : ∀ u, Small (f u).val B) (n : Nat) :
    Small (dyadicSampleAverage f I n).val B := by
  induction n generalizing I with
  | zero => exact samples I.midpoint
  | succ n ih =>
    have hb := LocalODE.small_scale (by decide +kernel : (0:Rat)≤1/2)
      (LocalODE.small_add (ih (bisectInterval I false)) (ih (bisectInterval I true)))
    have he : (1:Rat)/2*(B+B)=B := by grind only
    rw [he] at hb
    exact hb

end ComputableAnalysis.ModularForms
