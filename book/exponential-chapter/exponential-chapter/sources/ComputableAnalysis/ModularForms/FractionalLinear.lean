import ComputableAnalysis.ModularForms.UpperHalfPlane
import ComputableAnalysis.ModularForms.RationalAction
import ComputableAnalysis.RiemannHilbert.RepresentedReciprocal

/-! Executable fractional-linear evaluation on represented upper-half-plane
points. Denominator nonvanishing is proved, rather than supplied by the caller.
Domain preservation and the action composition law remain separate theorems. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw
open RiemannHilbert

/-- Integer affine expression on any represented complex input. -/
def integerAffine (a b : Int) (z : ComplexRaw) : ComplexRaw :=
  translate (b : Rat) (scaleRat (a : Rat) z)

theorem integerAffine_valid (a b : Int) {z : ComplexRaw} (hz : z.Valid) :
    (integerAffine a b z).Valid := translate_valid _ (scaleRat_valid hz)

theorem integerAffine_equiv (a b : Int) {z w : ComplexRaw} (hzw : z.Equiv w) :
    (integerAffine a b z).Equiv (integerAffine a b w) :=
  translate_equiv _ (scaleRat_equiv hzw)

/-- A determinant-one denominator cannot vanish in the represented upper half-plane. -/
theorem denominator_nonzero (g : SL2Z) (z : Scalar) (hz : InUpperHalfPlane z.val) :
    NonzeroBoxSearch.Nonzero ⟨integerAffine g.c g.d z.val, integerAffine_valid _ _ z.property⟩ := by
  intro hzero
  obtain ⟨N, hN⟩ := hz
  change 0 < (z.val.compute N).lo.im at hN
  have ho := (compareAt_overlap_iff _ _ N N).mp (hzero N)
  have hd := g.determinant_rat
  by_cases hc : 0 ≤ (g.c : Rat)
  · simp only [integerAffine, translate, add, scaleRat, ofQComplex,
      QBox.add, QComplex.add, QBox.scaleRat, if_pos hc, zero] at ho
    rcases ho with ⟨⟨hr₁, hi₁⟩, ⟨hr₂, hi₂⟩⟩
    dsimp [QComplex.zero] at hr₁ hi₁ hr₂ hi₂
    by_cases he : (g.c : Rat) = 0
    · simp only [he, Rat.zero_mul, Rat.zero_add, Rat.add_zero] at hr₁ hi₁ hr₂ hi₂
      have hdz : (g.d : Rat) = 0 := by grind only
      simp only [he, hdz, Rat.mul_zero] at hd
      grind only
    · have hp : 0 < (g.c : Rat) := Rat.lt_of_le_of_ne hc (Ne.symm he)
      have hh := Rat.mul_pos hp hN
      change 0 < (g.c : Rat)*(z.val.compute N).lo.im at hh
      grind only
  · simp only [integerAffine, translate, add, scaleRat, ofQComplex,
      QBox.add, QComplex.add, QBox.scaleRat, if_neg hc, zero] at ho
    rcases ho with ⟨⟨hr₁, hi₁⟩, ⟨hr₂, hi₂⟩⟩
    dsimp [QComplex.zero] at hr₁ hi₁ hr₂ hi₂
    have hn : (g.c : Rat) < 0 := (Rat.not_le).mp hc
    have hh : (g.c : Rat)*(z.val.compute N).lo.im < 0 := by
      have hp := Rat.mul_pos (show 0 < -(g.c : Rat) by grind only) hN
      rw [Rat.neg_mul] at hp
      grind only
    grind only

/-- A valid evaluator for `(az+b)/(cz+d)` on every represented upper-half-plane point. -/
def fractionalLinear (g : SL2Z) (z : Scalar) (hz : InUpperHalfPlane z.val) : Scalar :=
  let numerator : Scalar := ⟨integerAffine g.a g.b z.val, integerAffine_valid _ _ z.property⟩
  let denominator : Scalar := ⟨integerAffine g.c g.d z.val, integerAffine_valid _ _ z.property⟩
  let reciprocal := RepresentedReciprocal.inverse denominator (denominator_nonzero g z hz)
  ⟨mul numerator.val reciprocal.val, mul_valid numerator.property reciprocal.property⟩

theorem fractionalLinear_congr (g : SL2Z) (z w : Scalar)
    (hz : InUpperHalfPlane z.val) (hw : InUpperHalfPlane w.val) (hzw : z.val.Equiv w.val) :
    (fractionalLinear g z hz).val.Equiv (fractionalLinear g w hw).val := by
  apply mul_equiv
    (integerAffine_valid _ _ z.property) (integerAffine_valid _ _ w.property)
    (RepresentedReciprocal.inverse _ (denominator_nonzero g z hz)).property
    (RepresentedReciprocal.inverse _ (denominator_nonzero g w hw)).property
  · exact integerAffine_equiv _ _ hzw
  · exact RepresentedReciprocal.inverse_congr _ _ (denominator_nonzero g z hz)
      (denominator_nonzero g w hw) (integerAffine_equiv _ _ hzw)

/-- Exact quotient semantics for the evaluator, over arbitrary represented inputs. -/
theorem fractionalLinear_cancel (g : SL2Z) (z : Scalar) (hz : InUpperHalfPlane z.val) :
    (mul (integerAffine g.c g.d z.val) (fractionalLinear g z hz).val).Equiv
      (integerAffine g.a g.b z.val) := by
  let d : Scalar := ⟨integerAffine g.c g.d z.val, integerAffine_valid _ _ z.property⟩
  let n : Scalar := ⟨integerAffine g.a g.b z.val, integerAffine_valid _ _ z.property⟩
  let r := RepresentedReciprocal.inverse d (denominator_nonzero g z hz)
  have h := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid d.property r.property) (hright := ofQComplex_valid _)
    (RepresentedReciprocal.mul_inverse d (denominator_nonzero g z hz))
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := mul_valid d.property (fractionalLinear g z hz).property) (hright := n.property)
  let D := ComplexRawQuotient.ofRaw d.val d.property
  let N := ComplexRawQuotient.ofRaw n.val n.property
  let R := ComplexRawQuotient.ofRaw r.val r.property
  change D*R=1 at h
  change D*(N*R)=N
  grind

end ComputableAnalysis.ModularForms
