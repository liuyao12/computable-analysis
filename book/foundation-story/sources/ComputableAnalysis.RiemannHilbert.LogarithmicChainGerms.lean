import ComputableAnalysis.RiemannHilbert.LogarithmicChainTransport
import ComputableAnalysis.RiemannHilbert.LogarithmicOverlap

/-! Genuine germ continuation underlying finite A/z transport.
The actual local solutions agree on constructed open overlaps after a chart
step. Terminal germs have proved initial values, derivatives and refinement
agreement, rather than only a product of endpoint maps. -/
namespace ComputableAnalysis.RiemannHilbert.LogarithmicChainGerms
open ComplexRaw FunctionTheory LocalSystem LocalODE DomainFunctions NonzeroBoxSearch LogarithmContinuation
set_option maxHeartbeats 1000000
set_option autoImplicit false
variable {n : Nat}

theorem recenter_agreement (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A)
    (c d : Scalar) (hc : Nonzero c) (hd : Nonzero d) (hcd : RelativeLogarithm.domain c hc d)
    (x : Fiber n) (z : Scalar) (hz : LogarithmicLocalModel.overlap c d hc hd z) :
    (LogarithmicChainTransport.edgeSolution A hA c hc x).eval z hz.1 ≈
      (LogarithmicChainTransport.edgeSolution A hA d hd
        ((LogarithmicChainTransport.edge A hA c d hc hcd).toValueIso.forward.eval x)).eval z hz.2 := by
  let E := LogarithmicChainTransport.edge A hA c d hc hcd
  let U := LogarithmicLocalModel.transport A hA c hc d z hcd hz.1
  let V := LogarithmicLocalModel.transport A hA d hd d z (RelativeLogarithm.center_mem d hd) hz.2
  have hcomp : (E.toValueIso.forward.followedBy U.toValueIso.forward).eval x ≈
      (LogarithmicLocalModel.transport A hA c hc c z (RelativeLogarithm.center_mem c hc) hz.1).toValueIso.forward.eval x :=
    LogarithmicLocalModel.transport_comp A hA c hc c d z (RelativeLogarithm.center_mem c hc) hcd hz.1 x
  have hoverlap : U.toValueIso.forward.Equiv V.toValueIso.forward :=
    LogarithmicLocalModel.transport_overlap A hA c d hc hd d z ⟨hcd,RelativeLogarithm.center_mem d hd⟩ hz
  exact Setoid.trans (Setoid.symm hcomp) (hoverlap (E.toValueIso.forward.eval x))

def recenterRadius (c d : Scalar) (hc : Nonzero c) (hd : Nonzero d) (hcd : RelativeLogarithm.domain c hc d) : QPos :=
  LogarithmBranchCharts.overlapRadius c d hc hd hcd

theorem recenter_germ (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A)
    (c d : Scalar) (hc : Nonzero c) (hd : Nonzero d) (hcd : RelativeLogarithm.domain c hc d)
    (x : Fiber n) (z : Scalar) (hz : Small (sub z.val d.val) (recenterRadius c d hc hd hcd).val) :
    (LogarithmicChainTransport.edgeSolution A hA c hc x).eval z
      (LogarithmBranchCharts.overlapRadius_inside c d hc hd hcd z hz).1 ≈
    (LogarithmicChainTransport.edgeSolution A hA d hd
      ((LogarithmicChainTransport.edge A hA c d hc hcd).toValueIso.forward.eval x)).eval z
      (LogarithmBranchCharts.overlapRadius_inside c d hc hd hcd z hz).2 :=
  recenter_agreement A hA c d hc hd hcd x z (LogarithmBranchCharts.overlapRadius_inside c d hc hd hcd z hz)

def terminalGerm (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A)
    {c d : Scalar} {hc : Nonzero c} {hd : Nonzero d} (p : Chain c hc d hd) (x : Fiber n) :=
  LogarithmicLocalModel.vector A hA d hd ((LogarithmicChainTransport.transport A hA p).toValueIso.forward.eval x)

def terminalGerm_holomorphic (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A)
    {c d : Scalar} {hc : Nonzero c} {hd : Nonzero d} (p : Chain c hc d hd) (x : Fiber n) :
    DomainVectorFunctions.Holomorphic (terminalGerm A hA p x) := LogarithmicLocalModel.vector_holomorphic A hA d hd _

theorem terminalGerm_initial (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A)
    {c d : Scalar} {hc : Nonzero c} {hd : Nonzero d} (p : Chain c hc d hd) (x : Fiber n) :
    (terminalGerm A hA p x).eval d (RelativeLogarithm.center_mem d hd) ≈
      (LogarithmicChainTransport.transport A hA p).toValueIso.forward.eval x := LogarithmicLocalModel.forward_initial A hA d hd _

theorem terminalGerm_ode (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A)
    {c d : Scalar} {hc : Nonzero c} {hd : Nonzero d} (p : Chain c hc d hd) (x : Fiber n)
    (hF : DomainVectorFunctions.Holomorphic (terminalGerm A hA p x))
    (z : Scalar) (hz : RelativeLogarithm.domain d hd z) :
    DomainVectorFunctions.derivative (terminalGerm A hA p x) hF z hz ≈
      (LogarithmicConnection.coefficient A z (RelativeLogarithm.nonzero d hd z hz)).eval ((terminalGerm A hA p x).eval z hz) :=
  LogarithmicLocalModel.vector_derivative_ode A hA d hd _ hF z hz

theorem terminalGerm_append (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A)
    {c d e : Scalar} {hc : Nonzero c} {hd : Nonzero d} {he : Nonzero e}
    (p : Chain c hc d hd) (q : Chain d hd e he) (x : Fiber n)
    (z : Scalar) (hz : RelativeLogarithm.domain e he z) :
    (terminalGerm A hA (append p q) x).eval z hz ≈
      (terminalGerm A hA q ((LogarithmicChainTransport.transport A hA p).toValueIso.forward.eval x)).eval z hz :=
  (LogarithmicLocalModel.frame A hA e he z hz).toValueIso.forward.congr (LogarithmicChainTransport.transport_append A hA p q x)

theorem terminalGerm_refines (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A)
    {c d : Scalar} {hc : Nonzero c} {hd : Nonzero d} {p q : Chain c hc d hd} (h : Refines p q)
    (x : Fiber n) (z : Scalar) (hz : RelativeLogarithm.domain d hd z) :
    (terminalGerm A hA p x).eval z hz ≈ (terminalGerm A hA q x).eval z hz :=
  (LogarithmicLocalModel.frame A hA d hd z hz).toValueIso.forward.congr (LogarithmicChainTransport.forward_refines A hA h x)

theorem terminalGerm_vector_congr (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A)
    {c d : Scalar} {hc : Nonzero c} {hd : Nonzero d} (p : Chain c hc d hd)
    (x y : Fiber n) (hxy : x ≈ y) (z : Scalar) (hz : RelativeLogarithm.domain d hd z) :
    (terminalGerm A hA p x).eval z hz ≈ (terminalGerm A hA p y).eval z hz :=
  (LogarithmicLocalModel.frame A hA d hd z hz).toValueIso.forward.congr
    ((LogarithmicChainTransport.transport A hA p).toValueIso.forward.congr hxy)

theorem terminalGerm_names (A B : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A) (hB : IsLinear B) (hAB : A.Equiv B)
    (g : Scalar → Scalar) (hg : ∀ z, (g z).val.Equiv z.val)
    {c d : Scalar} {hc : Nonzero c} {hd : Nonzero d} (p : Chain c hc d hd) (x : Fiber n)
    (z w : Scalar) (hz : RelativeLogarithm.domain d hd z)
    (hw : RelativeLogarithm.domain (g d) (renamedNonzero g hg d hd) w) (hzw : z.val.Equiv w.val) :
    (terminalGerm A hA p x).eval z hz ≈ (terminalGerm B hB (rename g hg p) x).eval w hw := by
  let T := (LogarithmicChainTransport.transport A hA p).toValueIso.forward
  let U := (LogarithmicChainTransport.transport B hB (rename g hg p)).toValueIso.forward
  have hTU : T.Equiv U := LogarithmicChainTransport.forward_rename A B hA hB hAB g hg p
  have hframe : (LogarithmicLocalModel.frame A hA d hd z hz).toValueIso.forward.Equiv
      (LogarithmicLocalModel.frame B hB (g d) (renamedNonzero g hg d hd) w hw).toValueIso.forward :=
    LogarithmicLocalModel.frame_names_congr A B hA hB hAB d (g d) hd (renamedNonzero g hg d hd)
      (equiv_symm (hg d)) z w hz hw hzw
  exact Setoid.trans (hframe (T.eval x))
    ((LogarithmicLocalModel.frame B hB (g d) (renamedNonzero g hg d hd) w hw).toValueIso.forward.congr (hTU x))

end ComputableAnalysis.RiemannHilbert.LogarithmicChainGerms
