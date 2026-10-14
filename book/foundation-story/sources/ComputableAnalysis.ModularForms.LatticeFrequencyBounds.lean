import ComputableAnalysis.ModularForms.LatticeFrequencyExponentialPeriod

/-! Rational bounds and reality of the actual positive lattice frequency. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert

theorem latticeFrequency_box_guard (n : Nat) :
    (1:Rat)/2≤(latticeFrequency.val.compute n).lo.re ∧
      (latticeFrequency.val.compute n).lo.im=0 ∧ (latticeFrequency.val.compute n).hi.im=0 := by
  have h := RepresentedPositiveSquareRoot.PositiveInput.awayRootRaw_nested_guard latticeFrequencyInput n
  simp only [QBox.NestedIn,QComplex.le_def] at h
  have ho := valid_ordered latticeFrequency.property n
  simp only [QBox.Ordered,QComplex.le_def] at ho
  rcases h with ⟨hl,hr⟩
  change (1:Rat)/2≤(latticeFrequency.val.compute n).lo.re ∧
    0≤(latticeFrequency.val.compute n).lo.im at hl
  change (latticeFrequency.val.compute n).hi.re≤32 ∧
    (latticeFrequency.val.compute n).hi.im≤0 at hr
  exact ⟨hl.1,Rat.le_antisymm (Rat.le_trans ho.2 hr.2) hl.2,
    Rat.le_antisymm hr.2 (Rat.le_trans hl.2 ho.2)⟩

theorem latticeFrequency_real_embedding :
    latticeFrequency.val.Equiv (ofRealRaw latticeFrequency.val.realPart) := by
  intro n
  apply (compareAt_overlap_iff _ _ n n).2
  have h := latticeFrequency_box_guard n
  have ho := valid_ordered latticeFrequency.property n
  simp only [QBox.Ordered,QComplex.le_def] at ho
  change ((latticeFrequency.val.compute n).lo.re≤(latticeFrequency.val.compute n).hi.re ∧
    (latticeFrequency.val.compute n).lo.im≤0) ∧
    ((latticeFrequency.val.compute n).lo.re≤(latticeFrequency.val.compute n).hi.re ∧
      0≤(latticeFrequency.val.compute n).hi.im)
  exact ⟨⟨ho.1,by rw [h.2.1]; exact Rat.le_refl⟩,
    ⟨ho.1,by rw [h.2.2]; exact Rat.le_refl⟩⟩

theorem latticeFrequency_le_six : latticeFrequency.val.realPart.Le (RealRaw.ofRat 6) := by
  intro n m
  let k := n+RepresentedPositiveSquareRoot.PositiveInput.guardShift 31 1
  have hs := RepresentedPositiveSquareRoot.PositiveInput.approximation_spec latticeFrequencyInput k
  have hc := RepresentedPositiveSquareRoot.PositiveInput.awayRootRaw_contains_shifted_approximation latticeFrequencyInput n
  have hb := latticeFrequencyInput.center_le_bound k
  have hl : (RepresentedPositiveSquareRoot.PositiveInput.approximation latticeFrequencyInput k).lo≤6 := by
    apply le_of_sq_le_sq_of_nonneg_right (by decide +kernel : (0:Rat)≤6)
    have hsq := Rat.le_trans hs.2.2.1 hb
    have h36 : (31:Rat)≤sq (6:Rat) := by decide +kernel
    exact Rat.le_trans hsq h36
  simp only [QBox.NestedIn,QComplex.le_def] at hc
  have h := hc.1.1
  change (latticeFrequency.val.compute n).lo.re≤
    (RepresentedPositiveSquareRoot.PositiveInput.approximation latticeFrequencyInput k).lo at h
  exact Rat.le_trans h hl

end ComputableAnalysis.ModularForms
