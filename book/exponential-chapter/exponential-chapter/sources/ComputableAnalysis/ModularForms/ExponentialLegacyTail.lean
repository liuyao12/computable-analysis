import ComputableAnalysis.ModularForms.ExponentialRationalPrefix

/-! Value-level prefix error for the older stabilized rational exponential. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert

theorem point_in_box_error (z : ComplexRaw) (hz : z.Valid) (p : QComplex)
    (stage : Nat) (E : Rat) (hp : (QBox.point p).NestedIn (z.compute stage))
    (hw : (z.compute stage).width ≤ E) (hh : (z.compute stage).height ≤ E) :
    Small (sub z (ofQComplex p)) E := by
  have overlap (i j : Nat) : (z.compute i).lo ≤ (z.compute j).hi ∧
      (z.compute j).lo ≤ (z.compute i).hi := by
    have hi := valid_ordered hz i
    have hj := valid_ordered hz j
    by_cases hij : i ≤ j
    · have hn := valid_nestedIn hz hij
      simp only [QBox.NestedIn, QBox.Ordered, QComplex.le_def] at *
      grind
    · have hn := valid_nestedIn hz (show j ≤ i by omega)
      simp only [QBox.NestedIn, QBox.Ordered, QComplex.le_def] at *
      grind
  have hpt : (z.compute stage).lo ≤ p ∧ p ≤ (z.compute stage).hi := hp
  simp only [QComplex.le_def] at hpt
  unfold QBox.width at hw
  unfold QBox.height at hh
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro n m
  · have hm := (overlap stage m)
    simp only [QComplex.le_def] at hm
    change -E ≤ (z.compute m).hi.re + -p.re
    grind
  · have hm := overlap n stage
    simp only [QComplex.le_def] at hm
    change (z.compute n).lo.re + -p.re ≤ E
    grind
  · have hm := overlap stage m
    simp only [QComplex.le_def] at hm
    change -E ≤ (z.compute m).hi.im + -p.im
    grind
  · have hm := overlap n stage
    simp only [QComplex.le_def] at hm
    change (z.compute n).lo.im + -p.im ≤ E
    grind

theorem legacy_exponential_prefix_error (z : QComplex) (C : Rat)
    (hC : 0 ≤ C) (hz : QComplex.normBound z ≤ C) (stage : Nat) :
    Small (sub (ComplexExponentialApproximation.exponentialRawAt z C)
      (ofQComplex (ComplexExponentialApproximation.expPrefix z
        (RationalMajorant.factorialTailStart C+stage))))
      (4*RationalMajorant.factorialTailTerm C (RationalMajorant.factorialTailStart C)*
        ((1 : Rat)/2)^stage) := by
  have hw := ComplexExponentialApproximation.exponentialRawAt_width_height_geometric (z := z) hC stage
  exact point_in_box_error _
    (ComplexExponentialApproximation.exponentialRawAt_valid hC hz) _ stage _
    (ComplexExponentialApproximation.exponentialRawAt_contains_prefix hC hz stage) hw.1 hw.2

end ComputableAnalysis.ModularForms
