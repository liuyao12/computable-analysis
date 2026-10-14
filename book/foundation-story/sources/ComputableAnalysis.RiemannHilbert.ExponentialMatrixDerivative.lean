import ComputableAnalysis.RiemannHilbert.EntireExponentialODE
import ComputableAnalysis.RiemannHilbert.HolomorphicMatrixDifferentiation

/-! Exact matrix derivative of the entire exponential, for every genuine
entrywise holomorphic witness and every represented initial vector. -/
namespace ComputableAnalysis.RiemannHilbert.MatrixExponential
open ComplexRaw FunctionTheory LocalSystem
variable {n : Nat}

theorem field_derivative_ode (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A)
    (hM : LinearField.MatrixHolomorphic (field A hA) (fun _ _ _ => Iff.rfl) (field_congr A hA))
    (z : Scalar) :
    (LinearField.derivativeField hM z True.intro).Equiv ((value A hA z).followedBy A) := by
  apply (ValueMap.linear_equiv_iff_basis _ _ (LinearField.derivativeField_linear hM z True.intro)
    (IsLinear.followedBy (value_linear A hA z) hA)).2
  intro i
  exact Setoid.trans
    (LinearField.derivativeField_unique hM (field_holomorphic A hA) z True.intro (Fiber.basis i))
    (Setoid.trans (ValueMap.ofColumns_basis (LinearField.derivativeColumn (field_holomorphic A hA) z True.intro) i)
      (vector_derivative_ode A hA (Fiber.basis i) z))

theorem field_initial (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A) :
    (field A hA ⟨zero, ofQComplex_valid _⟩ True.intro).Equiv ValueMap.identity :=
  value_initial A hA

theorem field_derivative_congr (A B : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A) (hB : IsLinear B)
    (hAB : A.Equiv B) (z w : Scalar) (hzw : z.val.Equiv w.val)
    (hM : LinearField.MatrixHolomorphic (field A hA) (fun _ _ _ => Iff.rfl) (field_congr A hA))
    (hN : LinearField.MatrixHolomorphic (field B hB) (fun _ _ _ => Iff.rfl) (field_congr B hB)) :
    (LinearField.derivativeField hM z True.intro).Equiv (LinearField.derivativeField hN w True.intro) := by
  intro x
  exact Setoid.trans (field_derivative_ode A hA hM z x)
    (Setoid.trans (Setoid.trans (A.congr (value_congr A B hA hB hAB z w hzw x x (Setoid.refl _))) (hAB _))
      (Setoid.symm (field_derivative_ode B hB hN w x)))

end ComputableAnalysis.RiemannHilbert.MatrixExponential
