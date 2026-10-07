import ComputableAnalysis.ModularForms.LatticeBasisIndices163
import ComputableAnalysis.ModularForms.ActionComposition

/-! Exact lattice-coordinate identity beneath the modular transformation law. -/
namespace ComputableAnalysis.ModularForms
open RiemannHilbert

/-- Coordinate change for a lattice vector written as x+y*z. -/
def latticeIndexMatrix (g : SL2Z) : SL2Z :=
  ⟨g.d,g.b,g.c,g.a,by have h := g.determinant; grind⟩

/-- Multiplying a lattice vector at the transformed point by c*z+d gives
the reindexed lattice vector at the original point. This holds at every valid
represented upper-half-plane input. -/
theorem latticeVector_action (g : SL2Z) (z : Scalar) (hz : InUpperHalfPlane z.val)
    (u : QuadraticOrder163) :
    (ComplexRaw.mul (integerAffine g.c g.d z.val)
      (integerAffine u.y u.x (fractionalLinear g z hz).val)).Equiv
      (integerAffine (QuadraticOrder163.basisIndex (latticeIndexMatrix g) u).y
        (QuadraticOrder163.basisIndex (latticeIndexMatrix g) u).x z.val) := by
  let w := fractionalLinear g z hz
  have hc := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := ComplexRaw.mul_valid (integerAffine_valid _ _ z.property) w.property)
    (hright := integerAffine_valid _ _ z.property) (fractionalLinear_cancel g z hz)
  change ComplexRawQuotient.ofRaw (integerAffine g.c g.d z.val)
    (integerAffine_valid _ _ z.property)*ComplexRawQuotient.ofRaw w.val w.property=
      ComplexRawQuotient.ofRaw (integerAffine g.a g.b z.val)
        (integerAffine_valid _ _ z.property) at hc
  rw [integerAffine_class,integerAffine_class] at hc
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := ComplexRaw.mul_valid (integerAffine_valid _ _ z.property)
      (integerAffine_valid _ _ w.property))
    (hright := integerAffine_valid _ _ z.property)
  rw [ComplexRawQuotient.ofRaw_mul _ _ (integerAffine_valid _ _ z.property)
    (integerAffine_valid _ _ w.property)]
  rw [integerAffine_class,integerAffine_class,integerAffine_class]
  simp only [QuadraticOrder163.basisIndex,latticeIndexMatrix]
  grind

end ComputableAnalysis.ModularForms
