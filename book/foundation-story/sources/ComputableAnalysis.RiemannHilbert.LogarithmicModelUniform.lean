import ComputableAnalysis.RiemannHilbert.LogarithmicLocalModel
import ComputableAnalysis.RiemannHilbert.RelativeLogarithmUniform
import ComputableAnalysis.RiemannHilbert.MatrixCoordinateRemainders

/-! Constructed uniform bounds and operator remainder schedules for actual
logarithmic local frames. The forward and inverse estimates apply to every
represented vector with an independently supplied coordinate bound. -/
namespace ComputableAnalysis.RiemannHilbert.LogarithmicLocalModel
open ComplexRaw FunctionTheory LocalSystem LocalODE LinearField NonzeroBoxSearch
set_option maxHeartbeats 1000000
variable {n : Nat}

private def S : QPos := ⟨5, by decide⟩
private theorem image (c : Scalar) (hc : Nonzero c) (z : Scalar) (hz : RelativeLogarithm.domain c hc z) :
    interior S.val ((RelativeLogarithm.function c hc).eval z hz) :=
  ⟨4, by decide, by decide, RelativeLogarithm.value_bound c hc z hz⟩

def operator (A : ValueMap (Fiber n) (Fiber n)) (c : Scalar) (hc : Nonzero c) :
    UniformSegment.OperatorField (n := n) (RelativeLogarithm.domain c hc) :=
  fun z hz => LogarithmicConnection.coefficient A z (RelativeLogarithm.nonzero c hc z hz)

theorem operator_linear (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A) (c : Scalar) (hc : Nonzero c)
    (z : Scalar) (hz : RelativeLogarithm.domain c hc z) : IsLinear (operator A c hc z hz) :=
  LogarithmicConnection.coefficient_linear A hA _ _

def slope (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A) (c : Scalar) (hc : Nonzero c) :
    Field (n := n) (m := n) (RelativeLogarithm.domain c hc) :=
  coordinateSlope (MatrixExponential.discSlope A hA S) (RelativeLogarithm.function c hc).eval
    (RelativeLogarithm.holomorphic c hc).derivative (image c hc)

def inverseSlope (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A) (c : Scalar) (hc : Nonzero c) :=
  slope (MatrixExponential.negativeOperator A) (MatrixExponential.negativeOperator_linear A hA) c hc

theorem slope_ode (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A) (c : Scalar) (hc : Nonzero c)
    (z : Scalar) (hz : RelativeLogarithm.domain c hc z) :
    (slope A hA c hc z hz).Equiv
      ((forwardField (frame A hA c hc) z hz).followedBy (operator A c hc z hz)) :=
  fun x => coefficient_agreement A c hc (RelativeLogarithm.holomorphic c hc) z hz
    ((forwardField (frame A hA c hc) z hz).eval x)

theorem slope_matrix_derivative (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A) (c : Scalar) (hc : Nonzero c)
    (hM : MatrixHolomorphic (forwardField (frame A hA c hc))
      (RelativeLogarithm.function c hc).domain_congr (forward_congr A hA c hc))
    (z : Scalar) (hz : RelativeLogarithm.domain c hc z) :
    (derivativeField hM z hz).Equiv (slope A hA c hc z hz) :=
  MatrixExponential.pullback_matrix_derivative A hA (RelativeLogarithm.function c hc)
    (RelativeLogarithm.holomorphic c hc) hM z hz

theorem inverseSlope_matrix_derivative (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A) (c : Scalar) (hc : Nonzero c)
    (hN : MatrixHolomorphic (inverseField (frame A hA c hc))
      (RelativeLogarithm.function c hc).domain_congr (inverse_congr A hA c hc))
    (z : Scalar) (hz : RelativeLogarithm.domain c hc z) :
    (derivativeField hN z hz).Equiv (inverseSlope A hA c hc z hz) :=
  MatrixExponential.pullback_matrix_derivative (MatrixExponential.negativeOperator A)
    (MatrixExponential.negativeOperator_linear A hA) (RelativeLogarithm.function c hc)
    (RelativeLogarithm.holomorphic c hc) hN z hz

theorem inverseSlope_compatible (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A) (c : Scalar) (hc : Nonzero c) :
    Compatible (inverseField (frame A hA c hc)) (inverseSlope A hA c hc)
      (operator A c hc) (fun _ _ => ValueMap.zeroBetween n n) := by
  intro z hz x
  exact Setoid.trans (Fiber.add_congr
    (Setoid.symm (inverseSlope_matrix_derivative A hA c hc (inverse_holomorphic A hA c hc) z hz x))
    (Setoid.refl _)) (inverse_compatible A hA c hc (inverse_holomorphic A hA c hc) z hz x)

def valueBound (A : ValueMap (Fiber n) (Fiber n)) : Rat := MatrixExponential.discValueBound A S
def derivativeBound (A : ValueMap (Fiber n) (Fiber n)) (c : Scalar) (hc : Nonzero c) : Rat :=
  16*RelativeLogarithm.inverseBound c hc*MatrixExponential.discDerivativeBound A S
def operatorBound (A : ValueMap (Fiber n) (Fiber n)) (c : Scalar) (hc : Nonzero c) : Rat :=
  16*RelativeLogarithm.inverseBound c hc*ValueMap.linearBound A

theorem valueBound_nonneg (A : ValueMap (Fiber n) (Fiber n)) : 0 ≤ valueBound A := MatrixExponential.discValueBound_nonneg A S
theorem derivativeBound_nonneg (A : ValueMap (Fiber n) (Fiber n)) (c : Scalar) (hc : Nonzero c) : 0 ≤ derivativeBound A c hc :=
  Rat.mul_nonneg (Rat.mul_nonneg (by decide) (Rat.le_of_lt (RelativeLogarithm.inverseBound_pos c hc)))
    (MatrixExponential.discDerivativeBound_nonneg A S)
theorem operatorBound_nonneg (A : ValueMap (Fiber n) (Fiber n)) (c : Scalar) (hc : Nonzero c) : 0 ≤ operatorBound A c hc :=
  Rat.mul_nonneg (Rat.mul_nonneg (by decide) (Rat.le_of_lt (RelativeLogarithm.inverseBound_pos c hc))) (ValueMap.linearBound_nonneg A)

theorem forward_bound (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A) (c : Scalar) (hc : Nonzero c)
    (z : Scalar) (hz : RelativeLogarithm.domain c hc z) (E : Rat) (hE : 0 ≤ E) (x : Fiber n) (hx : CoordinateBound x E) :
    CoordinateBound ((forwardField (frame A hA c hc) z hz).eval x) (valueBound A*E) :=
  MatrixExponential.discField_bound A hA S _ (image c hc z hz) E hE x hx

theorem inverse_bound (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A) (c : Scalar) (hc : Nonzero c)
    (z : Scalar) (hz : RelativeLogarithm.domain c hc z) (E : Rat) (hE : 0 ≤ E) (x : Fiber n) (hx : CoordinateBound x E) :
    CoordinateBound ((inverseField (frame A hA c hc) z hz).eval x) (valueBound (MatrixExponential.negativeOperator A)*E) :=
  forward_bound (MatrixExponential.negativeOperator A) (MatrixExponential.negativeOperator_linear A hA) c hc z hz E hE x hx

theorem slope_bound (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A) (c : Scalar) (hc : Nonzero c)
    (z : Scalar) (hz : RelativeLogarithm.domain c hc z) (E : Rat) (hE : 0 ≤ E) (x : Fiber n) (hx : CoordinateBound x E) :
    CoordinateBound ((slope A hA c hc z hz).eval x) (derivativeBound A c hc*E) := by
  have h := coordinateSlope_bound (MatrixExponential.discSlope A hA S) (RelativeLogarithm.function c hc).eval
    (RelativeLogarithm.holomorphic c hc).derivative (image c hc)
    (MatrixExponential.discDerivativeBound A S) (8*RelativeLogarithm.inverseBound c hc)
    (MatrixExponential.discDerivativeBound_nonneg A S)
    (Rat.mul_nonneg (by decide) (Rat.le_of_lt (RelativeLogarithm.inverseBound_pos c hc)))
    (MatrixExponential.discSlope_bound A hA S) (RelativeLogarithm.derivative_bound c hc) z hz E hE x hx
  have he : (2*(8*RelativeLogarithm.inverseBound c hc)*MatrixExponential.discDerivativeBound A S)*E=
      derivativeBound A c hc*E := by dsimp [derivativeBound]; grind only
  rw [he] at h
  exact h

theorem inverseSlope_bound (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A) (c : Scalar) (hc : Nonzero c)
    (z : Scalar) (hz : RelativeLogarithm.domain c hc z) (E : Rat) (hE : 0 ≤ E) (x : Fiber n) (hx : CoordinateBound x E) :
    CoordinateBound ((inverseSlope A hA c hc z hz).eval x) (derivativeBound (MatrixExponential.negativeOperator A) c hc*E) :=
  slope_bound (MatrixExponential.negativeOperator A) (MatrixExponential.negativeOperator_linear A hA) c hc z hz E hE x hx

theorem operator_bound (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A) (c : Scalar) (hc : Nonzero c)
    (z : Scalar) (hz : RelativeLogarithm.domain c hc z) (E : Rat) (hE : 0 ≤ E) (x : Fiber n) (hx : CoordinateBound x E) :
    CoordinateBound ((operator A c hc z hz).eval x) (operatorBound A c hc*E) := by
  have h := bound_scale (c := RepresentedReciprocal.inverse z (RelativeLogarithm.nonzero c hc z hz))
    (x := A.eval x) (Rat.mul_nonneg (by decide : (0 : Rat) ≤ 8) (Rat.le_of_lt (RelativeLogarithm.inverseBound_pos c hc)))
    (Rat.mul_nonneg (ValueMap.linearBound_nonneg A) hE) (RelativeLogarithm.reciprocal_bound c hc z hz)
    (ValueMap.linear_bound A hA E hE x hx)
  have he : 2*(8*RelativeLogarithm.inverseBound c hc)*(ValueMap.linearBound A*E)=operatorBound A c hc*E := by
    dsimp [operatorBound]; grind only
  rw [he] at h
  exact h

def uniformDelta (A : ValueMap (Fiber n) (Fiber n)) (c : Scalar) (hc : Nonzero c) : QPos → QPos :=
  coordinateDelta (18*RelativeLogarithm.inverseBound c hc) (MatrixExponential.discDerivativeBound A S)
    (Rat.mul_nonneg (by decide) (Rat.le_of_lt (RelativeLogarithm.inverseBound_pos c hc)))
    (MatrixExponential.discDerivativeBound_nonneg A S) (MatrixExponential.discDelta A S) (RelativeLogarithm.uniformDelta c hc)

theorem forward_uniform_remainder (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A) (c : Scalar) (hc : Nonzero c)
    (eps H : QPos) (w z : Scalar) (hw : RelativeLogarithm.domain c hc w) (hz : RelativeLogarithm.domain c hc z)
    (hH : H.val ≤ (uniformDelta A c hc eps).val) (hzw : Small (sub z.val w.val) H.val)
    (E : Rat) (hE : 0 ≤ E) (x : Fiber n) (hx : CoordinateBound x E) :
    CoordinateBound (operatorRemainder (forwardField (frame A hA c hc)) (slope A hA c hc) w z hw hz x)
      ((eps.val*H.val)*E) :=
  coordinate_uniform_remainder (MatrixExponential.discField A hA S) (MatrixExponential.discSlope A hA S)
    (RelativeLogarithm.function c hc).eval (RelativeLogarithm.holomorphic c hc).derivative (image c hc)
    (18*RelativeLogarithm.inverseBound c hc) (MatrixExponential.discDerivativeBound A S)
    (Rat.mul_nonneg (by decide) (Rat.le_of_lt (RelativeLogarithm.inverseBound_pos c hc)))
    (MatrixExponential.discDerivativeBound_nonneg A S) (MatrixExponential.discSlope_bound A hA S)
    (RelativeLogarithm.lipschitz c hc) (MatrixExponential.discDelta A S) (RelativeLogarithm.uniformDelta c hc)
    (MatrixExponential.disc_uniform_remainder A hA S) (RelativeLogarithm.uniform_remainder c hc) eps H w z hw hz hH hzw E hE x hx

theorem inverse_uniform_remainder (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A) (c : Scalar) (hc : Nonzero c)
    (eps H : QPos) (w z : Scalar) (hw : RelativeLogarithm.domain c hc w) (hz : RelativeLogarithm.domain c hc z)
    (hH : H.val ≤ (uniformDelta (MatrixExponential.negativeOperator A) c hc eps).val)
    (hzw : Small (sub z.val w.val) H.val) (E : Rat) (hE : 0 ≤ E) (x : Fiber n) (hx : CoordinateBound x E) :
    CoordinateBound (operatorRemainder (inverseField (frame A hA c hc)) (inverseSlope A hA c hc) w z hw hz x)
      ((eps.val*H.val)*E) :=
  forward_uniform_remainder (MatrixExponential.negativeOperator A) (MatrixExponential.negativeOperator_linear A hA)
    c hc eps H w z hw hz hH hzw E hE x hx

end ComputableAnalysis.RiemannHilbert.LogarithmicLocalModel
