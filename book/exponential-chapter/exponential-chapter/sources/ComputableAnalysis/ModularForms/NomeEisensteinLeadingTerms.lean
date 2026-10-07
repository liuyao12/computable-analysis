import ComputableAnalysis.ModularForms.WeightedLambertLeadingTerm

/-! First-order Fourier estimates for the actual normalized Eisenstein values. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

private theorem affine_residual (c : Rat) (w q : Scalar) :
    (scaleRat c (sub w.val q.val)).Equiv
      (sub (add one (scaleRat c w.val)) (add one (scaleRat c q.val))) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := scaleRat_valid (sub_valid w.property q.property))
    (hright := sub_valid (add_valid (ofQComplex_valid _) (scaleRat_valid w.property))
      (add_valid (ofQComplex_valid _) (scaleRat_valid q.property)))
  let W := ComplexRawQuotient.ofRaw w.val w.property
  let Q := ComplexRawQuotient.ofRaw q.val q.property
  change ComplexRawQuotient.scaleRat c (W-Q)=
    (1+ComplexRawQuotient.scaleRat c W)-(1+ComplexRawQuotient.scaleRat c Q)
  change ComplexRawQuotient.scaleRat c (W+ -Q)=
    (1+ComplexRawQuotient.scaleRat c W)-(1+ComplexRawQuotient.scaleRat c Q)
  rw [ComplexRawQuotient.scaleRat_add,ComplexRawQuotient.neg_eq_scaleRat_neg_one Q,
    ComplexRawQuotient.scaleRat_scaleRat,show c*(-1)= -c by grind only,
    ←ComplexRawQuotient.neg_scaleRat]
  generalize ComplexRawQuotient.scaleRat c W=X,ComplexRawQuotient.scaleRat c Q=Y
  grind only

private theorem lambert_local (r : Rat) (hr : 0≤r) (hg : 128*r≤(1:Rat)/2) : 4*r≤(1:Rat)/2 := by grind only
private theorem lambert_ratio (r : Rat) (hr : 0≤r) (hg : 128*r≤(1:Rat)/2) (k : Nat) (hk : k=3 ∨ k=5) :
    weightedLambertRatio r k≤(1:Rat)/2 := by
  unfold weightedLambertRatio
  rcases hk with h | h
  · rw [h,show (2:Rat)^3=8 by decide +kernel]; grind only
  · rw [h,show (2:Rat)^5=32 by decide +kernel]; grind only

/-- The actual normalized weight-four value has the certified linear Fourier term. -/
theorem nomeEisensteinFour_linear_bound (q : Scalar) (r : Rat) (hr : 0≤r) (hg : 128*r≤(1:Rat)/2)
    (hq : Small q.val r) :
    Small (sub (nomeEisensteinFour q r hr hg hq).val (add one (scaleRat 240 q.val))) (130560*r*r) := by
  let w : Scalar := ⟨weightedLambertSum q r 3 hr (lambert_local r hr hg) hq,
    weightedLambertSum_valid q r 3 hr (lambert_local r hr hg) hq (lambert_ratio r hr hg 3 (Or.inl rfl))⟩
  have h := LocalODE.small_scale (show (0:Rat)≤240 by decide +kernel)
    (weightedLambertSum_linear_bound q r 3 hr (lambert_local r hr hg) hq (lambert_ratio r hr hg 3 (Or.inl rfl)))
  have hrate : 240*((64*(2:Rat)^3+32)*r*r)=130560*r*r := by
    rw [show (2:Rat)^3=8 by decide +kernel]
    grind only
  rw [hrate] at h
  exact Small.congr (scaleRat_valid (sub_valid w.property q.property))
    (sub_valid (nomeEisensteinFour q r hr hg hq).property (add_valid (ofQComplex_valid _) (scaleRat_valid q.property)))
    (affine_residual 240 w q) h

/-- The actual normalized weight-six value has the certified linear Fourier term. -/
theorem nomeEisensteinSix_linear_bound (q : Scalar) (r : Rat) (hr : 0≤r) (hg : 128*r≤(1:Rat)/2)
    (hq : Small q.val r) :
    Small (sub (nomeEisensteinSix q r hr hg hq).val (add one (scaleRat (-504) q.val))) (1048320*r*r) := by
  let w : Scalar := ⟨weightedLambertSum q r 5 hr (lambert_local r hr hg) hq,
    weightedLambertSum_valid q r 5 hr (lambert_local r hr hg) hq (lambert_ratio r hr hg 5 (Or.inr rfl))⟩
  have h := SeriesLimitLaws.small_neg (LocalODE.small_scale (show (0:Rat)≤504 by decide +kernel)
    (weightedLambertSum_linear_bound q r 5 hr (lambert_local r hr hg) hq (lambert_ratio r hr hg 5 (Or.inr rfl))))
  have hrate : 504*((64*(2:Rat)^5+32)*r*r)=1048320*r*r := by
    rw [show (2:Rat)^5=32 by decide +kernel]
    grind only
  rw [hrate] at h
  have he : (neg (scaleRat 504 (sub w.val q.val))).Equiv (scaleRat (-504) (sub w.val q.val)) := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := neg_valid (scaleRat_valid (sub_valid w.property q.property)))
      (hright := scaleRat_valid (sub_valid w.property q.property))
    change -(ComplexRawQuotient.scaleRat 504 (ComplexRawQuotient.ofRaw w.val w.property-ComplexRawQuotient.ofRaw q.val q.property))=
      ComplexRawQuotient.scaleRat (-504) (ComplexRawQuotient.ofRaw w.val w.property-ComplexRawQuotient.ofRaw q.val q.property)
    exact ComplexRawQuotient.neg_scaleRat 504 _
  have hs := Small.congr (neg_valid (scaleRat_valid (sub_valid w.property q.property)))
    (scaleRat_valid (sub_valid w.property q.property)) he h
  exact Small.congr (scaleRat_valid (sub_valid w.property q.property))
    (sub_valid (nomeEisensteinSix q r hr hg hq).property (add_valid (ofQComplex_valid _) (scaleRat_valid q.property)))
    (affine_residual (-504) w q) hs

end ComputableAnalysis.ModularForms
