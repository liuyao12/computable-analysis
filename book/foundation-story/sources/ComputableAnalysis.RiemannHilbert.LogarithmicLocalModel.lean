import ComputableAnalysis.RiemannHilbert.LogarithmicConnection
import ComputableAnalysis.RiemannHilbert.RelativeLogarithm

/-! Constructed normalized fundamental frames for A dz/z at every nonzero
represented center. Both inverse evaluators, holomorphicity, actual derivative
equations and center normalization are proved for arbitrary finite ranks. -/
namespace ComputableAnalysis.RiemannHilbert.LogarithmicLocalModel
open ComplexRaw FunctionTheory NonzeroBoxSearch
variable {n : Nat}

def frame (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A) (c : Scalar) (hc : Nonzero c) :
    (z : Scalar) → RelativeLogarithm.domain c hc z → LinearIso n n :=
  MatrixExponential.pullbackFrame A hA (RelativeLogarithm.function c hc)

theorem forward_congr (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A) (c : Scalar) (hc : Nonzero c)
    (z w : Scalar) (hz : RelativeLogarithm.domain c hc z) (hw : RelativeLogarithm.domain c hc w) (hzw : z.val.Equiv w.val) :
    (LinearField.forwardField (frame A hA c hc) z hz).Equiv (LinearField.forwardField (frame A hA c hc) w hw) :=
  MatrixExponential.pullback_forward_congr A hA (RelativeLogarithm.function c hc) z w hz hw hzw

theorem inverse_congr (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A) (c : Scalar) (hc : Nonzero c)
    (z w : Scalar) (hz : RelativeLogarithm.domain c hc z) (hw : RelativeLogarithm.domain c hc w) (hzw : z.val.Equiv w.val) :
    (LinearField.inverseField (frame A hA c hc) z hz).Equiv (LinearField.inverseField (frame A hA c hc) w hw) :=
  MatrixExponential.pullback_inverse_congr A hA (RelativeLogarithm.function c hc) z w hz hw hzw

def forward_holomorphic (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A) (c : Scalar) (hc : Nonzero c) :
    LinearField.MatrixHolomorphic (LinearField.forwardField (frame A hA c hc))
      (RelativeLogarithm.function c hc).domain_congr (forward_congr A hA c hc) :=
  MatrixExponential.pullback_forward_holomorphic A hA (RelativeLogarithm.function c hc) (RelativeLogarithm.holomorphic c hc)

def inverse_holomorphic (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A) (c : Scalar) (hc : Nonzero c) :
    LinearField.MatrixHolomorphic (LinearField.inverseField (frame A hA c hc))
      (RelativeLogarithm.function c hc).domain_congr (inverse_congr A hA c hc) :=
  MatrixExponential.pullback_inverse_holomorphic A hA (RelativeLogarithm.function c hc) (RelativeLogarithm.holomorphic c hc)

theorem coefficient_agreement (A : ValueMap (Fiber n) (Fiber n)) (c : Scalar) (hc : Nonzero c)
    (hL : DomainFunctions.Holomorphic (RelativeLogarithm.function c hc))
    (z : Scalar) (hz : RelativeLogarithm.domain c hc z) :
    (MatrixExponential.pullbackCoefficient A (RelativeLogarithm.function c hc) hL z hz).Equiv
      (LogarithmicConnection.coefficient A z (RelativeLogarithm.nonzero c hc z hz)) :=
  fun _x => Fiber.scale_congr (RelativeLogarithm.derivative_reciprocal c hc hL z hz) (Setoid.refl _)

theorem matrix_derivative_ode (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A) (c : Scalar) (hc : Nonzero c)
    (hM : LinearField.MatrixHolomorphic (LinearField.forwardField (frame A hA c hc))
      (RelativeLogarithm.function c hc).domain_congr (forward_congr A hA c hc))
    (z : Scalar) (hz : RelativeLogarithm.domain c hc z) :
    (LinearField.derivativeField hM z hz).Equiv
      ((LinearField.forwardField (frame A hA c hc) z hz).followedBy
        (LogarithmicConnection.coefficient A z (RelativeLogarithm.nonzero c hc z hz))) := by
  intro x
  exact Setoid.trans (MatrixExponential.pullback_matrix_derivative A hA (RelativeLogarithm.function c hc)
      (RelativeLogarithm.holomorphic c hc) hM z hz x)
    (coefficient_agreement A c hc (RelativeLogarithm.holomorphic c hc) z hz _)

theorem forward_initial (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A) (c : Scalar) (hc : Nonzero c) :
    (LinearField.forwardField (frame A hA c hc) c (RelativeLogarithm.center_mem c hc)).Equiv ValueMap.identity :=
  MatrixExponential.pullback_initial A hA (RelativeLogarithm.function c hc) c (RelativeLogarithm.center_mem c hc)
    (RelativeLogarithm.initial c hc)

theorem inverse_initial (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A) (c : Scalar) (hc : Nonzero c) :
    (LinearField.inverseField (frame A hA c hc) c (RelativeLogarithm.center_mem c hc)).Equiv ValueMap.identity :=
  MatrixExponential.pullback_initial (MatrixExponential.negativeOperator A) (MatrixExponential.negativeOperator_linear A hA)
    (RelativeLogarithm.function c hc) c (RelativeLogarithm.center_mem c hc) (RelativeLogarithm.initial c hc)

theorem inverse_matrix_derivative_ode (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A) (c : Scalar) (hc : Nonzero c)
    (hN : LinearField.MatrixHolomorphic (LinearField.inverseField (frame A hA c hc))
      (RelativeLogarithm.function c hc).domain_congr (inverse_congr A hA c hc))
    (z : Scalar) (hz : RelativeLogarithm.domain c hc z) (x : Fiber n) :
    (LinearField.derivativeField hN z hz).eval x ≈
      Fiber.neg ((LogarithmicConnection.coefficient A z (RelativeLogarithm.nonzero c hc z hz)).eval
        ((LinearField.inverseField (frame A hA c hc) z hz).eval x)) :=
  Setoid.trans (MatrixExponential.pullback_inverse_derivative A hA (RelativeLogarithm.function c hc)
    (RelativeLogarithm.holomorphic c hc) hN z hz x)
    (fun i => neg_equiv (coefficient_agreement A c hc (RelativeLogarithm.holomorphic c hc) z hz _ i))

theorem forward_compatible (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A) (c : Scalar) (hc : Nonzero c)
    (hM : LinearField.MatrixHolomorphic (LinearField.forwardField (frame A hA c hc))
      (RelativeLogarithm.function c hc).domain_congr (forward_congr A hA c hc)) :
    LinearField.Compatible (LinearField.forwardField (frame A hA c hc)) (LinearField.derivativeField hM)
      (fun _ _ => ValueMap.zeroBetween n n)
      (fun z hz => LogarithmicConnection.coefficient A z (RelativeLogarithm.nonzero c hc z hz)) := by
  intro z hz x
  exact Setoid.trans (Fiber.add_congr (matrix_derivative_ode A hA c hc hM z hz x)
    ((frame A hA c hc z hz).linear.zero)) (Fiber.add_zero _)

theorem inverse_compatible (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A) (c : Scalar) (hc : Nonzero c)
    (hN : LinearField.MatrixHolomorphic (LinearField.inverseField (frame A hA c hc))
      (RelativeLogarithm.function c hc).domain_congr (inverse_congr A hA c hc)) :
    LinearField.Compatible (LinearField.inverseField (frame A hA c hc)) (LinearField.derivativeField hN)
      (fun z hz => LogarithmicConnection.coefficient A z (RelativeLogarithm.nonzero c hc z hz))
      (fun _ _ => ValueMap.zeroBetween n n) := by
  intro z hz x
  have h := MatrixExponential.pullback_inverse_compatible A hA (RelativeLogarithm.function c hc)
    (RelativeLogarithm.holomorphic c hc) hN z hz x
  exact Setoid.trans (Fiber.add_congr (Setoid.refl _)
    ((LinearField.inverseField (frame A hA c hc) z hz).congr
      (Setoid.symm (coefficient_agreement A c hc (RelativeLogarithm.holomorphic c hc) z hz x)))) h

def vector (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A) (c : Scalar) (hc : Nonzero c) (x : Fiber n) :
    DomainVectorFunctions.Map n := MatrixExponential.pullbackVector A hA x (RelativeLogarithm.function c hc)

def vector_holomorphic (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A) (c : Scalar) (hc : Nonzero c) (x : Fiber n) :
    DomainVectorFunctions.Holomorphic (vector A hA c hc x) :=
  MatrixExponential.pullbackVector_holomorphic A hA x (RelativeLogarithm.function c hc) (RelativeLogarithm.holomorphic c hc)

theorem vector_derivative_ode (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A) (c : Scalar) (hc : Nonzero c)
    (x : Fiber n) (hV : DomainVectorFunctions.Holomorphic (vector A hA c hc x))
    (z : Scalar) (hz : RelativeLogarithm.domain c hc z) :
    DomainVectorFunctions.derivative (vector A hA c hc x) hV z hz ≈
      (LogarithmicConnection.coefficient A z (RelativeLogarithm.nonzero c hc z hz)).eval ((vector A hA c hc x).eval z hz) := by
  have he : DomainVectorFunctions.derivative (vector A hA c hc x) hV z hz ≈
      DomainVectorFunctions.derivative (vector A hA c hc x) (vector_holomorphic A hA c hc x) z hz :=
    fun i => (hV.coordinates i).derivative_unique ((vector_holomorphic A hA c hc x).coordinates i) z hz
  exact Setoid.trans he (Setoid.trans (MatrixExponential.pullbackVector_derivative A hA x (RelativeLogarithm.function c hc)
      (RelativeLogarithm.holomorphic c hc) z hz)
      (coefficient_agreement A c hc (RelativeLogarithm.holomorphic c hc) z hz _))

theorem frame_names_congr (A B : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A) (hB : IsLinear B) (hAB : A.Equiv B)
    (c d : Scalar) (hc : Nonzero c) (hd : Nonzero d) (hcd : c.val.Equiv d.val)
    (z w : Scalar) (hz : RelativeLogarithm.domain c hc z) (hw : RelativeLogarithm.domain d hd w) (hzw : z.val.Equiv w.val) :
    ((frame A hA c hc z hz).toValueIso.forward).Equiv ((frame B hB d hd w hw).toValueIso.forward) :=
  MatrixExponential.frame_congr A B hA hB hAB _ _ (RelativeLogarithm.value_congr c d hc hd hcd z w hz hw hzw)

theorem inverse_names_congr (A B : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A) (hB : IsLinear B) (hAB : A.Equiv B)
    (c d : Scalar) (hc : Nonzero c) (hd : Nonzero d) (hcd : c.val.Equiv d.val)
    (z w : Scalar) (hz : RelativeLogarithm.domain c hc z) (hw : RelativeLogarithm.domain d hd w) (hzw : z.val.Equiv w.val) :
    ((frame A hA c hc z hz).toValueIso.backward).Equiv ((frame B hB d hd w hw).toValueIso.backward) :=
  MatrixExponential.frame_backward_congr A B hA hB hAB _ _ (RelativeLogarithm.value_congr c d hc hd hcd z w hz hw hzw)

end ComputableAnalysis.RiemannHilbert.LogarithmicLocalModel
