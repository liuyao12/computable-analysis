import ComputableAnalysis.RiemannHilbert.LogarithmContinuationIncrement
import ComputableAnalysis.RiemannHilbert.LogarithmicTransport
import ComputableAnalysis.RiemannHilbert.LogarithmContinuationPaths

/-! Actual connection transport along a finite logarithm chart chain.
Each edge is the constructed local ODE transport for A/z. Its product
is proved to be the independent exponential at the continued logarithm
increment, including inverse frames, admissible refinement and input names. -/
namespace ComputableAnalysis.RiemannHilbert.LogarithmicChainTransport
open ComplexRaw FunctionTheory LocalSystem LocalODE DomainFunctions NonzeroBoxSearch LogarithmContinuation
set_option maxHeartbeats 1000000
set_option autoImplicit false
variable {n : Nat}

def edge (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A)
    (c d : Scalar) (hc : Nonzero c) (hcd : RelativeLogarithm.domain c hc d) : LinearIso n n :=
  LogarithmicLocalModel.transport A hA c hc c d (RelativeLogarithm.center_mem c hc) hcd

theorem edge_forward (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A)
    (c d : Scalar) (hc : Nonzero c) (hcd : RelativeLogarithm.domain c hc d) :
    (edge A hA c d hc hcd).toValueIso.forward.Equiv
      (MatrixExponential.value A hA ((RelativeLogarithm.function c hc).eval d hcd)) :=
  fun x => (MatrixExponential.value A hA ((RelativeLogarithm.function c hc).eval d hcd)).congr
    (LogarithmicLocalModel.inverse_initial A hA c hc x)

def transport (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A)
    {c d : Scalar} {hc : Nonzero c} {hd : Nonzero d} : Chain c hc d hd → LinearIso n n
  | .nil _ _ => LinearIso.identity n
  | @Chain.step c d e hc _ _ hcd tail => (edge A hA c d hc hcd).followedBy (transport A hA tail)

theorem forward_exponential (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A)
    {c d : Scalar} {hc : Nonzero c} {hd : Nonzero d} (p : Chain c hc d hd) :
    (transport A hA p).toValueIso.forward.Equiv (MatrixExponential.value A hA (increment p)) := by
  induction p with
  | nil c hc => exact fun x => Setoid.symm (MatrixExponential.value_initial A hA x)
  | @step c d e hc hd he hcd tail ih =>
      let L := (RelativeLogarithm.function c hc).eval d hcd
      have hprod : ((edge A hA c d hc hcd).toValueIso.forward.followedBy
          (transport A hA tail).toValueIso.forward).Equiv
          ((MatrixExponential.value A hA L).followedBy (MatrixExponential.value A hA (increment tail))) :=
        ValueMap.followedBy_congr (edge_forward A hA c d hc hcd) ih
      exact ValueMap.equiv_trans hprod
        (fun x => Setoid.symm (MatrixExponential.value_add A hA (increment tail) L x))

theorem inverse_exponential (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A)
    {c d : Scalar} {hc : Nonzero c} {hd : Nonzero d} (p : Chain c hc d hd) :
    (transport A hA p).toValueIso.backward.Equiv
      (MatrixExponential.frame A hA (increment p)).toValueIso.backward :=
  ValueIso.inverse_congr (transport A hA p).toValueIso (MatrixExponential.frame A hA (increment p)).toValueIso
    (forward_exponential A hA p)

theorem forward_increment_congr (A B : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A) (hB : IsLinear B)
    (hAB : A.Equiv B) {c d e f : Scalar} {hc : Nonzero c} {hd : Nonzero d} {he : Nonzero e} {hf : Nonzero f}
    (p : Chain c hc d hd) (q : Chain e he f hf) (hpq : (increment p).val.Equiv (increment q).val) :
    (transport A hA p).toValueIso.forward.Equiv (transport B hB q).toValueIso.forward :=
  ValueMap.equiv_trans (forward_exponential A hA p)
    (ValueMap.equiv_trans
      (fun x => MatrixExponential.value_congr A B hA hB hAB (increment p) (increment q) hpq x x (Setoid.refl x))
      (ValueMap.equiv_symm (forward_exponential B hB q)))

theorem inverse_increment_congr (A B : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A) (hB : IsLinear B)
    (hAB : A.Equiv B) {c d e f : Scalar} {hc : Nonzero c} {hd : Nonzero d} {he : Nonzero e} {hf : Nonzero f}
    (p : Chain c hc d hd) (q : Chain e he f hf) (hpq : (increment p).val.Equiv (increment q).val) :
    (transport A hA p).toValueIso.backward.Equiv (transport B hB q).toValueIso.backward :=
  ValueIso.inverse_congr (transport A hA p).toValueIso (transport B hB q).toValueIso
    (forward_increment_congr A B hA hB hAB p q hpq)

theorem transport_append (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A)
    {c d e : Scalar} {hc : Nonzero c} {hd : Nonzero d} {he : Nonzero e}
    (p : Chain c hc d hd) (q : Chain d hd e he) :
    (transport A hA (append p q)).toValueIso.forward.Equiv
      ((transport A hA p).toValueIso.forward.followedBy (transport A hA q).toValueIso.forward) := by
  induction p with
  | nil => exact ValueMap.equiv_refl _
  | @step c d f hc hd hf hcd tail ih =>
      exact fun x => (ih q) ((edge A hA c d hc hcd).toValueIso.forward.eval x)

theorem forward_refines (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A)
    {c d : Scalar} {hc : Nonzero c} {hd : Nonzero d} {p q : Chain c hc d hd} (h : Refines p q) :
    (transport A hA p).toValueIso.forward.Equiv (transport A hA q).toValueIso.forward :=
  forward_increment_congr A A hA hA (ValueMap.equiv_refl A) p q (increment_refines h)

theorem inverse_refines (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A)
    {c d : Scalar} {hc : Nonzero c} {hd : Nonzero d} {p q : Chain c hc d hd} (h : Refines p q) :
    (transport A hA p).toValueIso.backward.Equiv (transport A hA q).toValueIso.backward :=
  inverse_increment_congr A A hA hA (ValueMap.equiv_refl A) p q (increment_refines h)

theorem forward_rename (A B : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A) (hB : IsLinear B) (hAB : A.Equiv B)
    (g : Scalar → Scalar) (hg : ∀ z, (g z).val.Equiv z.val)
    {c d : Scalar} {hc : Nonzero c} {hd : Nonzero d} (p : Chain c hc d hd) :
    (transport A hA p).toValueIso.forward.Equiv (transport B hB (rename g hg p)).toValueIso.forward :=
  forward_increment_congr A B hA hB hAB p (rename g hg p) (increment_rename g hg p)

theorem inverse_rename (A B : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A) (hB : IsLinear B) (hAB : A.Equiv B)
    (g : Scalar → Scalar) (hg : ∀ z, (g z).val.Equiv z.val)
    {c d : Scalar} {hc : Nonzero c} {hd : Nonzero d} (p : Chain c hc d hd) :
    (transport A hA p).toValueIso.backward.Equiv (transport B hB (rename g hg p)).toValueIso.backward :=
  inverse_increment_congr A B hA hB hAB p (rename g hg p) (increment_rename g hg p)

def edgeSolution (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A)
    (c : Scalar) (hc : Nonzero c) (x : Fiber n) : DomainVectorFunctions.Map n :=
  LogarithmicLocalModel.solution A hA c hc c (RelativeLogarithm.center_mem c hc) x

def edgeSolution_holomorphic (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A)
    (c : Scalar) (hc : Nonzero c) (x : Fiber n) : DomainVectorFunctions.Holomorphic (edgeSolution A hA c hc x) :=
  LogarithmicLocalModel.solution_holomorphic A hA c hc c (RelativeLogarithm.center_mem c hc) x

theorem edgeSolution_ode (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A)
    (c : Scalar) (hc : Nonzero c) (x : Fiber n) (hF : DomainVectorFunctions.Holomorphic (edgeSolution A hA c hc x))
    (z : Scalar) (hz : RelativeLogarithm.domain c hc z) :
    DomainVectorFunctions.derivative (edgeSolution A hA c hc x) hF z hz ≈
      (LogarithmicConnection.coefficient A z (RelativeLogarithm.nonzero c hc z hz)).eval
        ((edgeSolution A hA c hc x).eval z hz) :=
  LogarithmicLocalModel.solution_ode A hA c hc c (RelativeLogarithm.center_mem c hc) x hF z hz

theorem edgeSolution_endpoint (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A)
    (c d : Scalar) (hc : Nonzero c) (hcd : RelativeLogarithm.domain c hc d) (x : Fiber n) :
    (edgeSolution A hA c hc x).eval d hcd ≈ (edge A hA c d hc hcd).toValueIso.forward.eval x :=
  LogarithmicLocalModel.solution_transport A hA c hc c d (RelativeLogarithm.center_mem c hc) hcd x

theorem edgeSolution_initial (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A)
    (c : Scalar) (hc : Nonzero c) (x : Fiber n) :
    (edgeSolution A hA c hc x).eval c (RelativeLogarithm.center_mem c hc) ≈ x :=
  LogarithmicLocalModel.solution_initial A hA c hc c (RelativeLogarithm.center_mem c hc) x

end ComputableAnalysis.RiemannHilbert.LogarithmicChainTransport
