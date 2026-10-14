import ComputableAnalysis.ModularForms.UpperLatticeTermHolomorphic

/-! Exact derivative formula for the actual holomorphic lattice reciprocal. -/
namespace ComputableAnalysis.ModularForms
open RiemannHilbert ComplexRaw

theorem latticeReciprocal_derivative_compute (u : QuadraticOrder163)
    (hu : u≠QuadraticOrder163.zero) (z : Scalar) (hz : InUpperHalfPlane z.val) :
    ((latticeReciprocalMap_holomorphic u hu).derivative z hz).val =
      mul (neg (mul (latticeInverse z hz u hu).val (latticeInverse z hz u hu).val))
        (ofQComplex ⟨(u.y:Rat),0⟩) := by
  rfl

theorem latticeReciprocal_derivative (u : QuadraticOrder163)
    (hu : u≠QuadraticOrder163.zero) (z : Scalar) (hz : InUpperHalfPlane z.val) :
    ((latticeReciprocalMap_holomorphic u hu).derivative z hz).val.Equiv
      (mul (neg (mul (latticeInverse z hz u hu).val (latticeInverse z hz u hu).val))
        (ofQComplex ⟨(u.y:Rat),0⟩)) := by
  rw [← latticeReciprocal_derivative_compute u hu z hz]
  exact equiv_refl _ ((latticeReciprocalMap_holomorphic u hu).derivative z hz).property

end ComputableAnalysis.ModularForms
