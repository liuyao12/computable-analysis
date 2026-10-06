import ComputableAnalysis.ModularForms.RealExponentialCore

/-! Strict separation of the actual positive-real exponential from one. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

theorem entireExponential_positive_gap (x : RealRaw) (hx : x.Valid) (hp : x.Pos) :
    ∃ r : Rat, 0<r ∧ (RealRaw.ofRat (1+r)).Le
      (entireExponentialValue ⟨ofRealRaw x,ofRealRaw_valid _ hx⟩).val.realPart := by
  have hpos := hp
  obtain ⟨N,hN⟩ := hp
  change 0<(x.compute N).lo at hN
  refine ⟨(x.compute N).lo,hN,?_⟩
  apply entireExponential_real_rational_lower x hx hpos
  intro i j
  exact RealRaw.le_refl x hx N j

theorem entireExponential_positive_ne_one (x : RealRaw) (hx : x.Valid) (hp : x.Pos) :
    ¬ (entireExponentialValue ⟨ofRealRaw x,ofRealRaw_valid _ hx⟩).val.Equiv (ofQComplex QComplex.one) := by
  intro he
  obtain ⟨r,hr,hgap⟩ := entireExponential_positive_gap x hx hp
  have hi : (entireExponentialValue ⟨ofRealRaw x,ofRealRaw_valid _ hx⟩).val.realPart.Equiv (RealRaw.ofRat 1) := realPart_equiv he
  have hv := realPart_valid (entireExponentialValue ⟨ofRealRaw x,ofRealRaw_valid _ hx⟩).property
  have ht := RealRaw.le_of_equiv (x := (entireExponentialValue ⟨ofRealRaw x,ofRealRaw_valid _ hx⟩).val.realPart)
    (y := RealRaw.ofRat 1) hv (RealRaw.ofRat_valid 1) hi
  have hl := RealRaw.le_trans (x := RealRaw.ofRat (1+r))
    (y := (entireExponentialValue ⟨ofRealRaw x,ofRealRaw_valid _ hx⟩).val.realPart)
    (z := RealRaw.ofRat 1) hv hgap ht
  have h := hl 0 0
  change 1+r≤(1:Rat) at h
  grind only

end ComputableAnalysis.ModularForms
