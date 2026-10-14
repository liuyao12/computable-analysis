import ComputableAnalysis.RiemannHilbert.JordanEigenvalueLogarithm
import ComputableAnalysis.RiemannHilbert.ComplexDiagonalBasis

/-! A represented logarithm of the usual Jordan block cI+J at every rank,
given a justified scalar logarithm branch. Complex diagonal rescaling and
its constructed reciprocal reduce the block to c(I+J). -/
namespace ComputableAnalysis.RiemannHilbert.StandardJordanLogarithm
open ComplexRaw FunctionTheory LocalSystem LocalODE
set_option maxHeartbeats 1000000

def monodromy (n : Nat) (c : Scalar) := ValueMap.sum (Fiber.scaleMap c) (JordanShift.shift n)
theorem monodromy_linear (n : Nat) (c : Scalar) : IsLinear (monodromy n c) :=
  ValueMap.sum_linear _ _ (Fiber.scaleMap_linear c) (JordanShift.shift_linear n)

theorem diagonal_intertwines (n : Nat) (c : Scalar) (x : Fiber n) :
    (ComplexDiagonalBasis.diagonal n c).eval ((JordanEigenvalueLogarithm.monodromy n c).eval x) ≈
      (monodromy n c).eval ((ComplexDiagonalBasis.diagonal n c).eval x) := by
  intro i
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := ((ComplexDiagonalBasis.diagonal n c).eval ((JordanEigenvalueLogarithm.monodromy n c).eval x)).property i)
    (hright := ((monodromy n c).eval ((ComplexDiagonalBasis.diagonal n c).eval x)).property i)
  by_cases h : i.val+1<n
  · let C := ComplexRawQuotient.ofRaw c.val c.property
    let P := ComplexRawQuotient.ofRaw (power c.val i.val) (power_valid c.val c.property i.val)
    let X := ComplexRawQuotient.ofRaw (x.val i) (x.property i)
    let Y := ComplexRawQuotient.ofRaw (x.val ⟨i.val+1,h⟩) (x.property _)
    dsimp [ComplexDiagonalBasis.diagonal,JordanEigenvalueLogarithm.monodromy,JordanEigenvalueLogarithm.scaledMonodromy,
      JordanLogarithm.monodromy,MatrixLogarithm.identityPlus,ValueMap.sum,ValueMap.identity,ValueMap.followedBy,
      Fiber.scaleMap,Fiber.scale,Fiber.add,JordanShift.shift,JordanShift.offset,monodromy]
    simp only [dif_pos h]
    change P*(C*(X+(1 : ScalarAlgebra.Value)*Y))=C*(P*X)+(P*C)*Y
    grind only
  · let C := ComplexRawQuotient.ofRaw c.val c.property
    let P := ComplexRawQuotient.ofRaw (power c.val i.val) (power_valid c.val c.property i.val)
    let X := ComplexRawQuotient.ofRaw (x.val i) (x.property i)
    dsimp [ComplexDiagonalBasis.diagonal,JordanEigenvalueLogarithm.monodromy,JordanEigenvalueLogarithm.scaledMonodromy,
      JordanLogarithm.monodromy,MatrixLogarithm.identityPlus,ValueMap.sum,ValueMap.identity,ValueMap.followedBy,
      Fiber.scaleMap,Fiber.scale,Fiber.add,JordanShift.shift,JordanShift.offset,monodromy]
    simp only [dif_neg h]
    change P*(C*(X+(1 : ScalarAlgebra.Value)*0))=C*(P*X)+0
    grind only

def branchBasis (n : Nat) (a c : Scalar) (hbranch : (MatrixExponential.scalarExponential a).val.Equiv c.val) :=
  ComplexDiagonalBasis.basis n c (MatrixExponential.scalarInverse a) (MatrixExponential.scalarBranch_inverse a c hbranch)

def logarithm (n : Nat) (a c : Scalar) (hbranch : (MatrixExponential.scalarExponential a).val.Equiv c.val) :=
  MatrixLogarithm.conjugated (branchBasis n a c hbranch) (JordanEigenvalueLogarithm.residue n a)

theorem logarithm_linear (n : Nat) (a c : Scalar) (hbranch : (MatrixExponential.scalarExponential a).val.Equiv c.val) :
    IsLinear (logarithm n a c hbranch) :=
  MatrixLogarithm.conjugated_linear _ _ (JordanEigenvalueLogarithm.residue_linear n a)

/-- The independent represented exponential recovers the standard Jordan
block. The scalar branch is supplied; the matrix identity is proved. -/
theorem exponential_logarithm (n : Nat) (a c : Scalar) (hbranch : (MatrixExponential.scalarExponential a).val.Equiv c.val) :
    (MatrixExponential.value (logarithm n a c hbranch) (logarithm_linear n a c hbranch) MatrixLogarithm.unit).Equiv (monodromy n c) := by
  intro x
  let q := branchBasis n a c hbranch
  exact Setoid.trans (JordanEigenvalueLogarithm.exponential_changed_basis q a c hbranch x)
    (Setoid.trans (diagonal_intertwines n c (q.toValueIso.backward.eval x))
      ((monodromy n c).congr (q.toValueIso.forward_backward x)))

theorem logarithm_congr (n : Nat) (a b c d : Scalar)
    (hac : (MatrixExponential.scalarExponential a).val.Equiv c.val)
    (hbd : (MatrixExponential.scalarExponential b).val.Equiv d.val)
    (hab : a.val.Equiv b.val) (hcd : c.val.Equiv d.val) :
    (logarithm n a c hac).Equiv (logarithm n b d hbd) :=
  MatrixLogarithm.conjugated_basis_congr _ _ _ _ (ComplexDiagonalBasis.diagonal_congr n c d hcd)
    (JordanEigenvalueLogarithm.residue_congr n a b hab)

def iso (n : Nat) (a c : Scalar) (hbranch : (MatrixExponential.scalarExponential a).val.Equiv c.val) : LinearIso n n := by
  let F := MatrixExponential.frame (logarithm n a c hbranch) (logarithm_linear n a c hbranch) MatrixLogarithm.unit
  have hFM : F.toValueIso.forward.Equiv (monodromy n c) := exponential_logarithm n a c hbranch
  exact {
    toValueIso := {
      forward := monodromy n c
      backward := F.toValueIso.backward
      backward_forward x := Setoid.trans (F.toValueIso.backward.congr (Setoid.symm (hFM x))) (F.toValueIso.backward_forward x)
      forward_backward x := Setoid.trans (Setoid.symm (hFM (F.toValueIso.backward.eval x))) (F.toValueIso.forward_backward x) }
    linear := monodromy_linear n c }

theorem iso_forward (n : Nat) (a c : Scalar) (hbranch : (MatrixExponential.scalarExponential a).val.Equiv c.val) :
    (iso n a c hbranch).toValueIso.forward=monodromy n c := rfl

theorem inverse_branch_independent (n : Nat) (a b c : Scalar)
    (hac : (MatrixExponential.scalarExponential a).val.Equiv c.val)
    (hbc : (MatrixExponential.scalarExponential b).val.Equiv c.val) :
    (iso n a c hac).toValueIso.backward.Equiv (iso n b c hbc).toValueIso.backward := by
  apply ValueIso.inverse_congr (iso n a c hac).toValueIso (iso n b c hbc).toValueIso
  rw [iso_forward n a c hac,iso_forward n b c hbc]
  exact ValueMap.equiv_refl (monodromy n c)

def vector (n : Nat) (a c : Scalar) (hbranch : (MatrixExponential.scalarExponential a).val.Equiv c.val) (x : Fiber n) :=
  MatrixExponential.vector (logarithm n a c hbranch) (logarithm_linear n a c hbranch) x

def vector_holomorphic (n : Nat) (a c : Scalar) (hbranch : (MatrixExponential.scalarExponential a).val.Equiv c.val) (x : Fiber n) :
    DomainVectorFunctions.Holomorphic (vector n a c hbranch x) :=
  MatrixExponential.vector_holomorphic _ (logarithm_linear n a c hbranch) x

theorem vector_derivative_at_unit (n : Nat) (a c : Scalar)
    (hbranch : (MatrixExponential.scalarExponential a).val.Equiv c.val) (x : Fiber n)
    (hF : DomainVectorFunctions.Holomorphic (vector n a c hbranch x)) :
    DomainVectorFunctions.derivative (vector n a c hbranch x) hF MatrixLogarithm.unit True.intro ≈
      (logarithm n a c hbranch).eval ((monodromy n c).eval x) :=
  Setoid.trans (MatrixExponential.vector_derivative_ode_of_holomorphic _ (logarithm_linear n a c hbranch) x hF MatrixLogarithm.unit)
    ((logarithm n a c hbranch).congr (exponential_logarithm n a c hbranch x))

end ComputableAnalysis.RiemannHilbert.StandardJordanLogarithm
