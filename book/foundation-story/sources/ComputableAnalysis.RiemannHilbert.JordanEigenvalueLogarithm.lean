import ComputableAnalysis.RiemannHilbert.JordanLogarithm
import ComputableAnalysis.RiemannHilbert.ExponentialScalarOperators
import ComputableAnalysis.RiemannHilbert.ExponentialCommutingSum

/-! Scalar shifts of proved matrix logarithms, instantiated for every
unipotent Jordan block. A scalar logarithm branch is genuine input evidence;
the matrix exponential identity and both matrix inverse laws are proved. -/
namespace ComputableAnalysis.RiemannHilbert.JordanEigenvalueLogarithm
open ComplexRaw FunctionTheory LocalSystem LocalODE
variable {n m : Nat}
set_option maxHeartbeats 1000000

def scalarShift (B : ValueMap (Fiber n) (Fiber n)) (a : Scalar) :=
  MatrixExponential.sumResidue (Fiber.scaleMap a) B

theorem scalarShift_linear (B : ValueMap (Fiber n) (Fiber n)) (hB : IsLinear B) (a : Scalar) :
    IsLinear (scalarShift B a) :=
  MatrixExponential.sumResidue_linear _ B (Fiber.scaleMap_linear a) hB

def scaledMonodromy (M : ValueMap (Fiber n) (Fiber n)) (c : Scalar) := M.followedBy (Fiber.scaleMap c)

theorem scaledMonodromy_linear (M : ValueMap (Fiber n) (Fiber n)) (hM : IsLinear M) (c : Scalar) :
    IsLinear (scaledMonodromy M c) := IsLinear.followedBy hM (Fiber.scaleMap_linear c)

/-- A scalar operator commutes with every complex-linear logarithm. The
independent exponential of their sum is the corresponding scalar multiple. -/
theorem exponential_scalarShift (B : ValueMap (Fiber n) (Fiber n)) (hB : IsLinear B) (a : Scalar) :
    (MatrixExponential.value (scalarShift B a) (scalarShift_linear B hB a) MatrixLogarithm.unit).Equiv
      (scaledMonodromy (MatrixExponential.value B hB MatrixLogarithm.unit) (MatrixExponential.scalarExponential a)) := by
  intro x
  exact Setoid.trans (MatrixExponential.value_commuting_sum (Fiber.scaleMap a) B (Fiber.scaleMap_linear a) hB
    (fun y => Setoid.symm (hB.2 a y)) MatrixLogarithm.unit x)
    (MatrixExponential.value_scalar_operator a _)

theorem exponential_scalarShift_of_branch (B : ValueMap (Fiber n) (Fiber n)) (hB : IsLinear B)
    (M : ValueMap (Fiber n) (Fiber n))
    (hBM : (MatrixExponential.value B hB MatrixLogarithm.unit).Equiv M)
    (a c : Scalar) (hbranch : (MatrixExponential.scalarExponential a).val.Equiv c.val) :
    (MatrixExponential.value (scalarShift B a) (scalarShift_linear B hB a) MatrixLogarithm.unit).Equiv (scaledMonodromy M c) :=
  ValueMap.equiv_trans (exponential_scalarShift B hB a)
    (ValueMap.followedBy_congr hBM (fun x => Fiber.scale_congr hbranch (Setoid.refl x)))

def residue (n : Nat) (a : Scalar) := scalarShift (JordanLogarithm.logarithm n) a
theorem residue_linear (n : Nat) (a : Scalar) : IsLinear (residue n a) :=
  scalarShift_linear _ (JordanLogarithm.logarithm_linear n) a

def monodromy (n : Nat) (c : Scalar) := scaledMonodromy (JordanLogarithm.monodromy n) c
theorem monodromy_linear (n : Nat) (c : Scalar) : IsLinear (monodromy n c) :=
  scaledMonodromy_linear _ (JordanLogarithm.monodromy_linear n) c

/-- A finite matrix logarithm for the block c(I+J), given a justified scalar
branch exp(a)=c. There is no matrix smallness restriction at any rank. -/
theorem exponential_residue (n : Nat) (a c : Scalar)
    (hbranch : (MatrixExponential.scalarExponential a).val.Equiv c.val) :
    (MatrixExponential.value (residue n a) (residue_linear n a) MatrixLogarithm.unit).Equiv (monodromy n c) :=
  exponential_scalarShift_of_branch _ (JordanLogarithm.logarithm_linear n) _ (JordanLogarithm.exponential_logarithm n) a c hbranch

theorem residue_congr (n : Nat) (a b : Scalar) (hab : a.val.Equiv b.val) : (residue n a).Equiv (residue n b) :=
  fun x => Fiber.add_congr (Fiber.scale_congr hab (Setoid.refl x)) (Setoid.refl _)

theorem monodromy_congr (n : Nat) (c d : Scalar) (hcd : c.val.Equiv d.val) : (monodromy n c).Equiv (monodromy n d) :=
  fun _ => Fiber.scale_congr hcd (Setoid.refl _)

def iso (n : Nat) (a c : Scalar) (hbranch : (MatrixExponential.scalarExponential a).val.Equiv c.val) : LinearIso n n := by
  let F := MatrixExponential.frame (residue n a) (residue_linear n a) MatrixLogarithm.unit
  have hFM : F.toValueIso.forward.Equiv (monodromy n c) := exponential_residue n a c hbranch
  exact {
    toValueIso := {
      forward := monodromy n c
      backward := F.toValueIso.backward
      backward_forward x := Setoid.trans (F.toValueIso.backward.congr (Setoid.symm (hFM x))) (F.toValueIso.backward_forward x)
      forward_backward x := Setoid.trans (Setoid.symm (hFM (F.toValueIso.backward.eval x))) (F.toValueIso.forward_backward x) }
    linear := monodromy_linear n c }

theorem inverse_congr (n : Nat) (a b c d : Scalar)
    (hac : (MatrixExponential.scalarExponential a).val.Equiv c.val)
    (hbd : (MatrixExponential.scalarExponential b).val.Equiv d.val) (hcd : c.val.Equiv d.val) :
    (iso n a c hac).toValueIso.backward.Equiv (iso n b d hbd).toValueIso.backward :=
  ValueIso.inverse_congr (iso n a c hac).toValueIso (iso n b d hbd).toValueIso (monodromy_congr n c d hcd)

def vector (n : Nat) (a : Scalar) (x : Fiber n) := MatrixExponential.vector (residue n a) (residue_linear n a) x
def vector_holomorphic (n : Nat) (a : Scalar) (x : Fiber n) : DomainVectorFunctions.Holomorphic (vector n a x) :=
  MatrixExponential.vector_holomorphic (residue n a) (residue_linear n a) x

theorem vector_derivative_at_unit (n : Nat) (a c : Scalar)
    (hbranch : (MatrixExponential.scalarExponential a).val.Equiv c.val) (x : Fiber n)
    (hF : DomainVectorFunctions.Holomorphic (vector n a x)) :
    DomainVectorFunctions.derivative (vector n a x) hF MatrixLogarithm.unit True.intro ≈
      (residue n a).eval ((monodromy n c).eval x) :=
  Setoid.trans (MatrixExponential.vector_derivative_ode_of_holomorphic (residue n a) (residue_linear n a) x hF MatrixLogarithm.unit)
    ((residue n a).congr (exponential_residue n a c hbranch x))

theorem exponential_changed_basis (q : LinearIso n m) (a c : Scalar)
    (hbranch : (MatrixExponential.scalarExponential a).val.Equiv c.val) :
    (MatrixExponential.value (MatrixLogarithm.conjugated q (residue n a))
      (MatrixLogarithm.conjugated_linear q _ (residue_linear n a)) MatrixLogarithm.unit).Equiv
      (MatrixLogarithm.conjugated q (monodromy n c)) :=
  ValueMap.equiv_trans (ValueMap.equiv_symm (MatrixLogarithm.exponential_conjugated q _ (residue_linear n a) MatrixLogarithm.unit))
    (MatrixLogarithm.conjugated_congr q _ _ (exponential_residue n a c hbranch))

end ComputableAnalysis.RiemannHilbert.JordanEigenvalueLogarithm
