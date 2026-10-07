import ComputableAnalysis.ModularForms.RepresentedPolynomialDifferenceBounds

/-! Uniform bounds for actual Eisenstein values on a small nome disk. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

private theorem one_small : Small one 1 := by
  refine ⟨?_,?_,?_,?_⟩
  · intro a b; change (-1:Rat)≤1; decide +kernel
  · intro a b; change (1:Rat)≤1; decide +kernel
  · intro a b; change (-1:Rat)≤0; decide +kernel
  · intro a b; change (0:Rat)≤1; decide +kernel

private theorem negative_scale_small (c : Rat) (x : Scalar) (B : Rat) (hc : 0≤c) (hx : Small x.val B) :
    Small (scaleRat (-c) x.val) (c*B) := by
  have he : (neg (scaleRat c x.val)).Equiv (scaleRat (-c) x.val) := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := neg_valid (scaleRat_valid x.property)) (hright := scaleRat_valid x.property)
    change -(ComplexRawQuotient.scaleRat c (ComplexRawQuotient.ofRaw x.val x.property))=
      ComplexRawQuotient.scaleRat (-c) (ComplexRawQuotient.ofRaw x.val x.property)
    exact ComplexRawQuotient.neg_scaleRat c _
  exact Small.congr (neg_valid (scaleRat_valid x.property)) (scaleRat_valid x.property) he
    (SeriesLimitLaws.small_neg (LocalODE.small_scale hc hx))

private theorem local_guard (r : Rat) (hr : 0≤r) (hg : 128*r≤(1:Rat)/2) : 4*r≤(1:Rat)/2 := by grind only
private theorem ratio_guard (r : Rat) (hr : 0≤r) (hg : 128*r≤(1:Rat)/2) (k : Nat) (hk : k=3 ∨ k=5) :
    weightedLambertRatio r k≤(1:Rat)/2 := by
  unfold weightedLambertRatio
  rcases hk with h | h
  · rw [h,show (2:Rat)^3=8 by decide +kernel]; grind only
  · rw [h,show (2:Rat)^5=32 by decide +kernel]; grind only

/-- A uniform coordinate bound for the actual normalized weight-four value in a small disk. -/
theorem nomeEisensteinFour_small_disk_bound (q : Scalar) (r : Rat) (hr : 0≤r)
    (hg : 128*r≤(1:Rat)/2) (hq : Small q.val r) (hsmall : r≤(1:Rat)/65536) :
    Small (nomeEisensteinFour q r hr hg hq).val 2 := by
  have h := LocalODE.small_add one_small (LocalODE.small_scale (show (0:Rat)≤240 by decide +kernel)
    (weightedLambertSum_bound q r 3 hr (local_guard r hr hg) hq (ratio_guard r hr hg 3 (Or.inl rfl))))
  apply h.mono
  grind only

/-- A uniform coordinate bound for the actual normalized weight-six value in a small disk. -/
theorem nomeEisensteinSix_small_disk_bound (q : Scalar) (r : Rat) (hr : 0≤r)
    (hg : 128*r≤(1:Rat)/2) (hq : Small q.val r) (hsmall : r≤(1:Rat)/65536) :
    Small (nomeEisensteinSix q r hr hg hq).val 2 := by
  let w : Scalar := ⟨weightedLambertSum q r 5 hr (local_guard r hr hg) hq,
    weightedLambertSum_valid q r 5 hr (local_guard r hr hg) hq (ratio_guard r hr hg 5 (Or.inr rfl))⟩
  have h := LocalODE.small_add one_small (negative_scale_small 504 w (4*(8*r))
    (by decide +kernel) (weightedLambertSum_bound q r 5 hr (local_guard r hr hg) hq (ratio_guard r hr hg 5 (Or.inr rfl))))
  apply h.mono
  grind only

/-- The linear weight-four Fourier polynomial has the same coordinate bound. -/
theorem nomeEisensteinFour_linear_polynomial_bound (q : Scalar) (r : Rat) (hr : 0≤r)
    (hq : Small q.val r) (hsmall : r≤(1:Rat)/65536) :
    Small (add one (scaleRat 240 q.val)) 2 := by
  have h := LocalODE.small_add one_small (LocalODE.small_scale (show (0:Rat)≤240 by decide +kernel) hq)
  apply h.mono
  grind only

/-- The linear weight-six Fourier polynomial has the same coordinate bound. -/
theorem nomeEisensteinSix_linear_polynomial_bound (q : Scalar) (r : Rat) (hr : 0≤r)
    (hq : Small q.val r) (hsmall : r≤(1:Rat)/65536) :
    Small (add one (scaleRat (-504) q.val)) 2 := by
  have h := LocalODE.small_add one_small (negative_scale_small 504 q r (by decide +kernel) hq)
  apply h.mono
  grind only

end ComputableAnalysis.ModularForms
