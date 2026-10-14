import ComputableAnalysis.ModularForms.ActionDomain

/-! Composition of the actual represented modular action. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert

theorem integer_constant (b : Int) :
    ComplexRawQuotient.ofQComplex ⟨(b : Rat),0⟩ = (b : ScalarAlgebra.Value) := by
  change ComplexRawQuotient.ofRaw (ofQComplex ⟨(b : Rat),0⟩) _ =
    ComplexRawQuotient.ofRaw (scaleRat (b : Rat) (ofQComplex QComplex.one)) _
  apply ComplexRawQuotient.ofRaw_eq_ofRaw
  intro k
  apply (compareAt_overlap_iff _ _ k k).mpr
  simp only [ofQComplex, scaleRat, QBox.scaleRat, QComplex.one]
  split <;> simp [QBox.Overlaps, QComplex.le_def, Rat.mul_one, Rat.mul_zero]

/-- Integer affine evaluation agrees with ordinary algebra on valid values. -/
theorem integerAffine_class (a b : Int) (z : Scalar) :
    ComplexRawQuotient.ofRaw (integerAffine a b z.val) (integerAffine_valid _ _ z.property) =
      (a : ScalarAlgebra.Value)*ComplexRawQuotient.ofRaw z.val z.property +
      (b : ScalarAlgebra.Value) := by
  change ComplexRawQuotient.scaleRat (a : Rat) (ComplexRawQuotient.ofRaw z.val z.property) +
    ComplexRawQuotient.ofQComplex ⟨(b : Rat),0⟩ = _
  rw [integer_constant]
  congr 1
  change ComplexRawQuotient.scaleRat (a : Rat) _ =
    ComplexRawQuotient.scaleRat (a : Rat) 1 * _
  rw [← ComplexRawQuotient.scaleRat_mul]
  congr 1
  grind

/-- Matrix multiplication agrees with composition on every represented upper-half-plane point. -/
theorem fractionalLinear_compose (g h : SL2Z) (z : Scalar) (hz : InUpperHalfPlane z.val) :
    (fractionalLinear g (fractionalLinear h z hz) (fractionalLinear_mem h z hz)).val.Equiv
      (fractionalLinear (SL2Z.multiply g h) z hz).val := by
  let y := fractionalLinear h z hz
  let w := fractionalLinear g y (fractionalLinear_mem h z hz)
  apply equiv_symm
  apply fractionalLinear_unique (SL2Z.multiply g h) z hz w
  have hy := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid (integerAffine_valid _ _ z.property) y.property)
    (hright := integerAffine_valid _ _ z.property) (fractionalLinear_cancel h z hz)
  have hw := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid (integerAffine_valid _ _ y.property) w.property)
    (hright := integerAffine_valid _ _ y.property)
    (fractionalLinear_cancel g y (fractionalLinear_mem h z hz))
  change ComplexRawQuotient.ofRaw (integerAffine h.c h.d z.val) (integerAffine_valid _ _ z.property) *
    ComplexRawQuotient.ofRaw y.val y.property =
    ComplexRawQuotient.ofRaw (integerAffine h.a h.b z.val) (integerAffine_valid _ _ z.property) at hy
  change ComplexRawQuotient.ofRaw (integerAffine g.c g.d y.val) (integerAffine_valid _ _ y.property) *
    ComplexRawQuotient.ofRaw w.val w.property =
    ComplexRawQuotient.ofRaw (integerAffine g.a g.b y.val) (integerAffine_valid _ _ y.property) at hw
  simp only [integerAffine_class] at hy hw
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := mul_valid (integerAffine_valid _ _ z.property) w.property)
    (hright := integerAffine_valid _ _ z.property)
  change ComplexRawQuotient.ofRaw (integerAffine (SL2Z.multiply g h).c (SL2Z.multiply g h).d z.val) (integerAffine_valid _ _ z.property) *
    ComplexRawQuotient.ofRaw w.val w.property =
    ComplexRawQuotient.ofRaw (integerAffine (SL2Z.multiply g h).a (SL2Z.multiply g h).b z.val) (integerAffine_valid _ _ z.property)
  simp only [integerAffine_class, SL2Z.multiply]
  grind

/-- Applying the inverse matrix undoes the transformation. -/
theorem fractionalLinear_inverse_left (g : SL2Z) (z : Scalar) (hz : InUpperHalfPlane z.val) :
    (fractionalLinear (SL2Z.inverse g) (fractionalLinear g z hz)
      (fractionalLinear_mem g z hz)).val.Equiv z.val := by
  have h := fractionalLinear_compose (SL2Z.inverse g) g z hz
  rw [SL2Z.inverse_multiply] at h
  exact equiv_trans
    (fractionalLinear _ _ _).property (fractionalLinear SL2Z.identity z hz).property
    z.property h (fractionalLinear_identity z hz)

/-- Applying a matrix after its inverse also returns the original value. -/
theorem fractionalLinear_inverse_right (g : SL2Z) (z : Scalar) (hz : InUpperHalfPlane z.val) :
    (fractionalLinear g (fractionalLinear (SL2Z.inverse g) z hz)
      (fractionalLinear_mem (SL2Z.inverse g) z hz)).val.Equiv z.val := by
  have h := fractionalLinear_compose g (SL2Z.inverse g) z hz
  rw [SL2Z.multiply_inverse] at h
  exact equiv_trans
    (fractionalLinear _ _ _).property (fractionalLinear SL2Z.identity z hz).property
    z.property h (fractionalLinear_identity z hz)

/-- Valid represented points with their upper-half-plane domain evidence. -/
abbrev UpperPoint := { z : Scalar // InUpperHalfPlane z.val }

/-- The integer matrix action includes its proved domain preservation. -/
def matrixAction (g : SL2Z) (z : UpperPoint) : UpperPoint :=
  ⟨fractionalLinear g z.val z.property, fractionalLinear_mem g z.val z.property⟩

theorem matrixAction_identity (z : UpperPoint) :
    (matrixAction SL2Z.identity z).val.val.Equiv z.val.val :=
  fractionalLinear_identity z.val z.property

theorem matrixAction_compose (g h : SL2Z) (z : UpperPoint) :
    (matrixAction g (matrixAction h z)).val.val.Equiv
      (matrixAction (SL2Z.multiply g h) z).val.val :=
  fractionalLinear_compose g h z.val z.property

end ComputableAnalysis.ModularForms
