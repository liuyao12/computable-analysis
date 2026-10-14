import ComputableAnalysis.RiemannHilbert.CauchyMomentBounds

/-! Comparison of independently valid represented values through rational
samples. Only finite enclosures and shrinking errors are supplied. -/
namespace ComputableAnalysis.RiemannHilbert.SampledLimitAgreement
open ComplexRaw FunctionTheory LocalODE
set_option autoImplicit false

theorem enclosure_error (f : ComplexRaw) (hf : f.Valid) (q : QComplex) (E : Rat)
    (hE : 0 ≤ E) (n : Nat)
    (he : (f.compute n).NestedIn (QBox.expand (QBox.point q) E)) :
    Small (sub f (ofQComplex q)) E := by
  have h := small_from_box (sub f (ofQComplex q)) (sub_valid hf (ofQComplex_valid _)) n
  apply h.mono
  change (q.re-E ≤ (f.compute n).lo.re ∧ q.im-E ≤ (f.compute n).lo.im) ∧
    ((f.compute n).hi.re ≤ q.re+E ∧ (f.compute n).hi.im ≤ q.im+E) at he
  change max 0 (max (-((f.compute n).lo.re + -q.re))
    (max ((f.compute n).hi.re + -q.re)
      (max (-((f.compute n).lo.im + -q.im)) ((f.compute n).hi.im + -q.im)))) ≤ E
  grind

theorem rational_difference {a b : QComplex} {B : Rat}
    (h : QComplex.normBound (QComplex.sub a b) ≤ B) :
    Small (sub (ofQComplex a) (ofQComplex b)) B := by
  have hb := CauchyTaylor.l1_coordinates h
  refine ⟨?_,?_,?_,?_⟩
  · intro _ _; exact hb.1
  · intro _ _; exact hb.2.1
  · intro _ _; exact hb.2.2.1
  · intro _ _; exact hb.2.2.2

theorem bound (f p : ComplexRaw) (hf : f.Valid) (hp : p.Valid)
    (a b : Nat → QComplex) (B : Rat) (e : Nat → Rat) (he0 : ∀ n, 0 ≤ e n)
    (he : ShrinksToZero e)
    (hfa : ∀ n, (f.compute n).NestedIn (QBox.expand (QBox.point (a n)) (e n)))
    (hpb : ∀ n, (QBox.point (b n)).NestedIn (p.compute n))
    (hab : ∀ n, QComplex.normBound (QComplex.sub (a n) (b n)) ≤ B) :
    Small (sub f p) B := by
  apply SeriesLimitLaws.small_closed _ B (fun k => 2*(RepresentedCauchySum.error k).val)
    (SeriesLimitLaws.shrinks_scale _ RepresentedCauchySum.error_shrinks 2 (by decide))
  intro k
  let eps := RepresentedCauchySum.error k
  obtain ⟨N,hN⟩ := hp.2.2 eps
  obtain ⟨M,hM⟩ := he eps
  let n := max N M
  have hn := hN n (Nat.le_max_left _ _)
  have hm := hM n (Nat.le_max_right _ _)
  have hpa := BoxApproximation.point_error ⟨p,hp⟩ n (b n) eps.val
    (Rat.le_of_lt eps.property) (hpb n) hn.1 hn.2
  have hfa' := enclosure_error f hf (a n) (e n) (he0 n) n (hfa n)
  have hab' := rational_difference (hab n)
  have hs := small_add (small_add hfa' hab')
    (RepresentedCauchySum.small_sub_symm _ _ _ hpa)
  have hv := SeriesLimitLaws.difference_via f p (ofQComplex (a n)) (ofQComplex (b n))
    hf hp (ofQComplex_valid _) (ofQComplex_valid _)
  have hh := Small.congr
    (add_valid (add_valid (sub_valid hf (ofQComplex_valid _))
      (sub_valid (ofQComplex_valid _) (ofQComplex_valid _))) (sub_valid (ofQComplex_valid _) hp))
    (sub_valid hf hp) (equiv_symm hv) hs
  exact hh.mono (by change e n+B+eps.val ≤ B+2*eps.val; grind only)

end ComputableAnalysis.RiemannHilbert.SampledLimitAgreement
