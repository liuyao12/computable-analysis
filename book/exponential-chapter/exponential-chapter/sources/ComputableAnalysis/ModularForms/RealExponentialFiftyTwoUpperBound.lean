import ComputableAnalysis.ModularForms.RealPowerUpperBound
import ComputableAnalysis.ModularForms.RealExponentialReality
import ComputableAnalysis.ModularForms.ExponentialPowers

/-! An actual exponential upper bound amplified by justified represented power laws. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

/-- The actual represented exponential at fifty-two is bounded by the twenty-sixth power of eight. -/
theorem entireExponential_rational_fiftyTwo_upper :
    (entireExponentialValue ⟨ofQComplex ⟨52,0⟩,ofQComplex_valid _⟩).val.realPart.Le
      (RealRaw.ofRat ((8:Rat)^26)) := by
  let z : Scalar := ⟨ofQComplex ⟨2,0⟩,ofQComplex_valid _⟩
  let e := (entireExponentialValue z).val.realPart
  have ve : e.Valid := realPart_valid (entireExponentialValue z).property
  have hnonneg : (RealRaw.ofRat 0).Le e := by
    have h := entireExponential_rational_real_quadratic_lower 2 (by decide +kernel)
    intro n m
    have hl := h 0 m
    change (0:Rat)≤(e.compute m).hi
    change (1:Rat)+2+2*2/2≤(e.compute m).hi at hl
    grind only
  have hb := realFinitePower_upper e ve 8 (by decide +kernel) hnonneg
    entireExponential_rational_two_upper_eight 26
  let s : Scalar := ⟨scaleRat ((26:Nat):Rat) z.val,scaleRat_valid z.property⟩
  have hs : s.val.Equiv (ofQComplex ⟨52,0⟩) := by
    intro n
    apply (compareAt_overlap_iff _ _ n n).mpr
    simp only [s,z,scaleRat,ofQComplex,QBox.scaleRat,QBox.point,
      if_pos (show (0:Rat)≤((26:Nat):Rat) by decide +kernel),QBox.Overlaps,QComplex.le_def]
    decide +kernel
  have hreal := equiv_real_embedding (entireExponentialValue z) (entireExponential_rational_real_imag_zero 2)
  have hp := LocalODE.power_congr _ _ (entireExponentialValue z).property (ofRealRaw_valid _ ve) hreal 26
  have he := equiv_trans
    (entireExponentialValue ⟨ofQComplex ⟨52,0⟩,ofQComplex_valid _⟩).property
    (entireExponentialValue s).property (ofRealRaw_valid _ (realFinitePower_valid e ve 26))
    (entireExponentialValue_congr _ s (equiv_symm hs))
    (equiv_trans (entireExponentialValue s).property
      (LocalODE.power_valid _ (entireExponentialValue z).property 26)
      (ofRealRaw_valid _ (realFinitePower_valid e ve 26)) (entireExponential_nat_multiple z 26)
      (equiv_trans (LocalODE.power_valid _ (entireExponentialValue z).property 26)
        (LocalODE.power_valid _ (ofRealRaw_valid _ ve) 26)
        (ofRealRaw_valid _ (realFinitePower_valid e ve 26)) hp (realFinitePower_complex e ve 26)))
  have hr := ComplexRaw.realPart_equiv he
  exact RealRaw.le_trans (realFinitePower_valid e ve 26)
    (RealRaw.le_of_equiv (realPart_valid (entireExponentialValue _).property) (realFinitePower_valid e ve 26) hr) hb

end ComputableAnalysis.ModularForms
