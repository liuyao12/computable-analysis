import ComputableAnalysis.ModularForms.CMNormBounds163

/-! Algebraic conjugation agrees with complex conjugation at the CM embedding. -/
namespace ComputableAnalysis.ModularForms
open QuadraticOrder163

theorem cmPoint163_conjugate_compute (n : Nat) :
    (ComplexRaw.conj cmPoint163).compute n=(integerAffine (-1) 1 cmPoint163).compute n := by
  simp only [ComplexRaw.conj,cmPoint163,integerAffine,translate,
    ComplexRaw.scaleRat,ComplexRaw.add,ComplexRaw.one,ComplexRaw.ofQComplex,
    ComplexRaw.imaginaryAxis_compute,QBox.conj,QBox.scaleRat,QBox.add,QComplex.add,QComplex.one]
  simp only [if_pos (show (0:Rat)≤1/2 by decide +kernel),
    if_neg (show ¬(0:Rat)≤ -1 by decide +kernel)]
  congr 1 <;> congr 1 <;> grind

theorem cmPoint163_conjugate : (ComplexRaw.conj cmPoint163).Equiv (integerAffine (-1) 1 cmPoint163) := by
  intro n
  apply (ComplexRaw.compareAt_overlap_iff _ _ n n).mpr
  rw [cmPoint163_conjugate_compute]
  have h := ComplexRaw.valid_ordered (integerAffine_valid (-1) 1 cmPoint163_valid) n
  exact ⟨⟨h.1,h.2⟩,⟨h.1,h.2⟩⟩

end ComputableAnalysis.ModularForms
