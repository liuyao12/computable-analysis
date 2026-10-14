import ComputableAnalysis.ModularForms.RepresentedPrefixFactors

/-! Exact multiplication by rational real constants on actual represented values. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

private theorem scale_one_compute (r : Rat) (N : Nat) :
    (scaleRat r one).compute N=(ofQComplex ⟨r,0⟩).compute N := by
  simp [scaleRat,one,ofQComplex,QBox.scaleRat,QComplex.one]

/-- Rational real multiplication is exactly rational scaling for every valid input. -/
theorem rationalReal_mul_scale (r : Rat) (z : Scalar) :
    (mul (ofQComplex ⟨r,0⟩) z.val).Equiv (scaleRat r z.val) := by
  have hc : ComplexRawQuotient.ofQComplex ⟨r,0⟩=ComplexRawQuotient.scaleRat r 1 := by
    have he : (ofQComplex ⟨r,0⟩).Equiv (scaleRat r one) := by
      intro N
      apply (compareAt_overlap_iff _ _ N N).mpr
      rw [scale_one_compute r N]
      exact (compareAt_overlap_iff _ _ N N).mp (equiv_refl (ofQComplex ⟨r,0⟩) (ofQComplex_valid _) N)
    exact ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := ofQComplex_valid _) (hright := scaleRat_valid (ofQComplex_valid _)) he
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := mul_valid (ofQComplex_valid _) z.property) (hright := scaleRat_valid z.property)
  change ComplexRawQuotient.ofQComplex ⟨r,0⟩*ComplexRawQuotient.ofRaw z.val z.property=
    ComplexRawQuotient.scaleRat r (ComplexRawQuotient.ofRaw z.val z.property)
  rw [hc,← ComplexRawQuotient.scaleRat_mul]
  congr 1
  grind only

end ComputableAnalysis.ModularForms
