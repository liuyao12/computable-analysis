import ComputableAnalysis.RiemannHilbert.RationalNonzeroLogarithmRoutes

/-! Constructed scalar logarithms and Jordan logarithms at every nonzero
valid represented complex value. The finite route is computed from rational
boxes, and each analytic edge is justified. Selection retains its route;
no global single-valued holomorphic logarithm is asserted. -/
namespace ComputableAnalysis.RiemannHilbert.NonzeroLogarithmConstruction
open ComplexRaw FunctionTheory LocalSystem LocalODE DomainFunctions NonzeroBoxSearch ReciprocalExamples LogarithmContinuation
open ContinuedJordanLogarithm
set_option maxHeartbeats 1000000

def route (z : Scalar) (hz : Nonzero z) : Chain oneScalar one_nonzero z hz :=
  append (RationalNonzeroLogarithmRoutes.route (RationalLogarithmAnchor.center z hz)
    (RationalLogarithmAnchor.center_normSq_ne_zero z hz))
    (.step (RationalLogarithmAnchor.endpoint_mem z hz) (.nil z hz))

def value (z : Scalar) (hz : Nonzero z) : Scalar := LogarithmContinuation.value (route z hz) zeroSeed

theorem exponential (z : Scalar) (hz : Nonzero z) :
    (MatrixExponential.scalarExponential (value z hz)).val.Equiv z.val :=
  value_exponential (route z hz) zeroSeed MatrixExponential.scalarExponential_zero

theorem exists_logarithm (z : Scalar) (hz : Nonzero z) :
    ∃ a : Scalar, (MatrixExponential.scalarExponential a).val.Equiv z.val := ⟨value z hz,exponential z hz⟩

def localFunction (z : Scalar) (hz : Nonzero z) := terminalFunction (route z hz) zeroSeed
def localHolomorphic (z : Scalar) (hz : Nonzero z) : DomainFunctions.Holomorphic (localFunction z hz) :=
  terminalHolomorphic (route z hz) zeroSeed

theorem local_initial (z : Scalar) (hz : Nonzero z) :
    ((localFunction z hz).eval z (RelativeLogarithm.center_mem z hz)).val.Equiv (value z hz).val :=
  terminal_initial (route z hz) zeroSeed

theorem local_exponential (z : Scalar) (hz : Nonzero z) (w : Scalar) (hw : (localFunction z hz).domain w) :
    (MatrixExponential.scalarExponential ((localFunction z hz).eval w hw)).val.Equiv w.val :=
  terminal_exponential (route z hz) zeroSeed MatrixExponential.scalarExponential_zero w hw

theorem local_derivative (z : Scalar) (hz : Nonzero z) (hF : DomainFunctions.Holomorphic (localFunction z hz))
    (w : Scalar) (hw : (localFunction z hz).domain w) :
    (hF.derivative w hw).val.Equiv (RepresentedReciprocal.inverse w (RelativeLogarithm.nonzero z hz w hw)).val :=
  terminal_derivative (route z hz) zeroSeed hF w hw

theorem route_nonzero (z : Scalar) (hz : Nonzero z) (t : UnitInterval.Point) :
    Nonzero ((path (route z hz)).eval t) := path_nonzero (route z hz) t

def logarithm (n : Nat) (z : Scalar) (hz : Nonzero z) := ContinuedJordanLogarithm.logarithm n z hz (route z hz)
theorem logarithm_linear (n : Nat) (z : Scalar) (hz : Nonzero z) : IsLinear (logarithm n z hz) :=
  ContinuedJordanLogarithm.logarithm_linear n z hz (route z hz)

theorem exponential_logarithm (n : Nat) (z : Scalar) (hz : Nonzero z) :
    (MatrixExponential.value (logarithm n z hz) (logarithm_linear n z hz) MatrixLogarithm.unit).Equiv
      (StandardJordanLogarithm.monodromy n z) := ContinuedJordanLogarithm.exponential_logarithm n z hz (route z hz)

def vector (n : Nat) (z : Scalar) (hz : Nonzero z) (x : Fiber n) := ContinuedJordanLogarithm.vector n z hz (route z hz) x
def vector_holomorphic (n : Nat) (z : Scalar) (hz : Nonzero z) (x : Fiber n) : DomainVectorFunctions.Holomorphic (vector n z hz x) :=
  ContinuedJordanLogarithm.vector_holomorphic n z hz (route z hz) x

theorem vector_derivative (n : Nat) (z : Scalar) (hz : Nonzero z) (x : Fiber n)
    (hF : DomainVectorFunctions.Holomorphic (vector n z hz x)) :
    DomainVectorFunctions.derivative (vector n z hz x) hF MatrixLogarithm.unit True.intro ≈
      (logarithm n z hz).eval ((StandardJordanLogarithm.monodromy n z).eval x) :=
  ContinuedJordanLogarithm.vector_derivative n z hz (route z hz) x hF

/-- A selected branch remains a branch under a change of endpoint name.
The route is retained; independently selected routes need not have equal
logarithm values. -/
theorem exponential_of_equiv (z w : Scalar) (hz : Nonzero z) (hzw : z.val.Equiv w.val) :
    (MatrixExponential.scalarExponential (value z hz)).val.Equiv w.val :=
  equiv_trans (MatrixExponential.scalarExponential (value z hz)).property z.property w.property (exponential z hz) hzw

def transportedLogarithm (n : Nat) (z w : Scalar) (hz : Nonzero z) (hzw : z.val.Equiv w.val) :=
  StandardJordanLogarithm.logarithm n (value z hz) w (exponential_of_equiv z w hz hzw)

theorem logarithm_name_transport (n : Nat) (z w : Scalar) (hz : Nonzero z) (hzw : z.val.Equiv w.val) :
    (logarithm n z hz).Equiv (transportedLogarithm n z w hz hzw) :=
  StandardJordanLogarithm.logarithm_congr n _ _ z w (exponential z hz) (exponential_of_equiv z w hz hzw)
    (equiv_refl _ (value z hz).property) hzw

theorem exists_logarithm_congr (z w : Scalar) (hzw : z.val.Equiv w.val) :
    (∃ a : Scalar, (MatrixExponential.scalarExponential a).val.Equiv z.val) ↔
      (∃ a : Scalar, (MatrixExponential.scalarExponential a).val.Equiv w.val) := by
  constructor
  · rintro ⟨a,ha⟩
    exact ⟨a,equiv_trans (MatrixExponential.scalarExponential a).property z.property w.property ha hzw⟩
  · rintro ⟨a,ha⟩
    exact ⟨a,equiv_trans (MatrixExponential.scalarExponential a).property w.property z.property ha (equiv_symm hzw)⟩

def iso (n : Nat) (z : Scalar) (hz : Nonzero z) : LinearIso n n :=
  StandardJordanLogarithm.iso n (value z hz) z (exponential z hz)

theorem iso_forward (n : Nat) (z : Scalar) (hz : Nonzero z) :
    (iso n z hz).toValueIso.forward=StandardJordanLogarithm.monodromy n z :=
  StandardJordanLogarithm.iso_forward n (value z hz) z (exponential z hz)

theorem monodromy_congr (n : Nat) (z w : Scalar) (hzw : z.val.Equiv w.val) :
    (StandardJordanLogarithm.monodromy n z).Equiv (StandardJordanLogarithm.monodromy n w) := by
  intro x i
  exact add_equiv (mul_equiv z.property w.property (x.property i) (x.property i) hzw
    (equiv_refl _ (x.property i))) (equiv_refl _ (((JordanShift.shift n).eval x).property i))

/-- The inverse Jordan frame is independent of both input names and the
branches selected by the two computed routes. -/
theorem inverse_name_independent (n : Nat) (z w : Scalar) (hz : Nonzero z) (hw : Nonzero w) (hzw : z.val.Equiv w.val) :
    (iso n z hz).toValueIso.backward.Equiv (iso n w hw).toValueIso.backward := by
  apply ValueIso.inverse_congr (iso n z hz).toValueIso (iso n w hw).toValueIso
  rw [iso_forward n z hz,iso_forward n w hw]
  exact monodromy_congr n z w hzw

def transportedLocalFunction (z w : Scalar) (hz : Nonzero z) (hw : Nonzero w) :=
  LogarithmBranchCharts.function w hw (value z hz)

theorem local_name_transport (z w : Scalar) (hz : Nonzero z) (hw : Nonzero w) (hzw : z.val.Equiv w.val)
    (p q : Scalar) (hp : (localFunction z hz).domain p) (hq : (transportedLocalFunction z w hz hw).domain q)
    (hpq : p.val.Equiv q.val) :
    ((localFunction z hz).eval p hp).val.Equiv ((transportedLocalFunction z w hz hw).eval q hq).val :=
  LogarithmBranchCharts.value_congr z w hz hw _ _ hzw (equiv_refl _ (value z hz).property) p q hp hq hpq

end ComputableAnalysis.RiemannHilbert.NonzeroLogarithmConstruction
