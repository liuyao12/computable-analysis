import ComputableAnalysis.ModularForms.UpperLatticeReciprocal
import ComputableAnalysis.ModularForms.CMLatticeReciprocal163

/-! Representation invariance and CM agreement of general lattice reciprocals. -/
namespace ComputableAnalysis.ModularForms
open RiemannHilbert

theorem latticeVector_congr (z w : Scalar) (u : QuadraticOrder163)
    (he : z.val.Equiv w.val) : (latticeVector z u).val.Equiv (latticeVector w u).val :=
  integerAffine_equiv u.y u.x he

theorem latticeInverse_congr (z w : Scalar) (hz : InUpperHalfPlane z.val)
    (hw : InUpperHalfPlane w.val) (u : QuadraticOrder163) (hu : u≠QuadraticOrder163.zero)
    (he : z.val.Equiv w.val) :
    (latticeInverse z hz u hu).val.Equiv (latticeInverse w hw u hu).val :=
  RepresentedReciprocal.inverse_congr _ _ (latticeVector_nonzero z hz u hu)
    (latticeVector_nonzero w hw u hu) (latticeVector_congr z w u he)

/-- The general evaluator agrees with the original executable CM reciprocal. -/
theorem latticeInverse_cm_agreement (u : QuadraticOrder163) (hu : u≠QuadraticOrder163.zero) :
    (latticeInverse ⟨cmPoint163,cmPoint163_valid⟩ cmPoint163_upper u hu).val.Equiv
      (QuadraticOrder163.complexInverse u hu).val := by
  apply RepresentedReciprocal.inverse_unique _
    (latticeVector_nonzero ⟨cmPoint163,cmPoint163_valid⟩ cmPoint163_upper u hu)
    (QuadraticOrder163.complexInverse u hu)
  exact QuadraticOrder163.complexInverse_product u hu

end ComputableAnalysis.ModularForms
