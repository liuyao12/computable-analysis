import ComputableAnalysis.ModularForms.UpperFiniteHolomorphic
import ComputableAnalysis.ModularForms.UpperDerivativeShells

/-! Actual derivatives of finite lattice sums are sums of the certified point derivatives. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

def upperPointDerivative (z : Scalar) (hz : InUpperHalfPlane z.val)
    (k : Nat) (u : QuadraticOrder163) : ComplexRaw :=
  ((upperPointMap_holomorphic k u).derivative z hz).val

theorem upperPointDerivative_valid (z : Scalar) (hz : InUpperHalfPlane z.val)
    (k : Nat) (u : QuadraticOrder163) : (upperPointDerivative z hz k u).Valid :=
  ((upperPointMap_holomorphic k u).derivative z hz).property

theorem upperPointDerivative_nonzero (z : Scalar) (hz : InUpperHalfPlane z.val)
    (k : Nat) (u : QuadraticOrder163) (hu : u≠QuadraticOrder163.zero) :
    upperPointDerivative z hz k u = ((latticePowerMap_holomorphic u hu k).derivative z hz).val := by
  simp only [upperPointDerivative, upperPointMap_holomorphic, dif_pos hu,
    Holomorphic.transfer]

theorem upperPointDerivative_zero (z : Scalar) (hz : InUpperHalfPlane z.val)
    (k : Nat) : upperPointDerivative z hz k QuadraticOrder163.zero = ComplexRaw.zero := by
  simp only [upperPointDerivative, upperPointMap_holomorphic, ne_eq, not_true_eq_false,
    dif_neg, Holomorphic.transfer, constantOn_holomorphic]
  rfl

theorem derivativeShellTerm_point (z : Scalar) (hz : InUpperHalfPlane z.val)
    (r : Nat) (hr : 0<r) (k i : Nat) (hi : i<8*r) :
    derivativeShellTerm z hz r hr k i =
      upperPointDerivative z hz k (QuadraticOrder163.shellPoint r ⟨i,hi⟩) := by
  rw [upperPointDerivative_nonzero z hz k _
    (QuadraticOrder163.shellPoint_nonzero r hr ⟨i,hi⟩)]
  simp only [derivativeShellTerm, dif_pos hi]

theorem upperFiniteMap_derivative (z : Scalar) (hz : InUpperHalfPlane z.val)
    (k : Nat) (us : List QuadraticOrder163) :
    ((upperFiniteMap_holomorphic k us).derivative z hz).val =
      LocalODE.sum (us.map (upperPointDerivative z hz k)) := by
  induction us with
  | nil => rfl
  | cons u us ih =>
    change add (upperPointDerivative z hz k u)
      ((upperFiniteMap_holomorphic k us).derivative z hz).val = _
    rw [ih]
    rfl

end ComputableAnalysis.ModularForms
