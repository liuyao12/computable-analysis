import ComputableAnalysis.RiemannHilbert.LogarithmBranchCharts

/-! Finite continuation of actual logarithm germs. A chain records only
local domain membership; its continued values, exponential identity and
open overlap agreement are proved from the constructed Taylor charts. -/
namespace ComputableAnalysis.RiemannHilbert.LogarithmContinuation
open ComplexRaw FunctionTheory LocalODE DomainFunctions NonzeroBoxSearch
set_option maxHeartbeats 1000000

inductive Chain : (c : Scalar) → Nonzero c → (d : Scalar) → Nonzero d → Type where
  | nil (c : Scalar) (hc : Nonzero c) : Chain c hc c hc
  | step {c d e : Scalar} {hc : Nonzero c} {hd : Nonzero d} {he : Nonzero e}
      (hcd : RelativeLogarithm.domain c hc d) (tail : Chain d hd e he) : Chain c hc e he

def value {c d : Scalar} {hc : Nonzero c} {hd : Nonzero d} : Chain c hc d hd → Scalar → Scalar
  | .nil _ _, a => a
  | .step hcd tail, a => value tail ((LogarithmBranchCharts.function _ _ a).eval _ hcd)

def terminalFunction {c d : Scalar} {hc : Nonzero c} {hd : Nonzero d}
    (p : Chain c hc d hd) (a : Scalar) : DomainFunctions.Map :=
  LogarithmBranchCharts.function d hd (value p a)

def terminalHolomorphic {c d : Scalar} {hc : Nonzero c} {hd : Nonzero d}
    (p : Chain c hc d hd) (a : Scalar) : DomainFunctions.Holomorphic (terminalFunction p a) :=
  LogarithmBranchCharts.holomorphic d hd (value p a)

theorem value_congr {c d : Scalar} {hc : Nonzero c} {hd : Nonzero d}
    (p : Chain c hc d hd) (a b : Scalar) (hab : a.val.Equiv b.val) :
    (value p a).val.Equiv (value p b).val := by
  induction p generalizing a b with
  | nil => exact hab
  | @step c d e hc hd he hcd tail ih =>
      exact ih _ _ (LogarithmBranchCharts.value_congr c c hc hc a b
        (equiv_refl _ c.property) hab d d hcd hcd (equiv_refl _ d.property))

theorem value_exponential {c d : Scalar} {hc : Nonzero c} {hd : Nonzero d}
    (p : Chain c hc d hd) (a : Scalar)
    (ha : (MatrixExponential.scalarExponential a).val.Equiv c.val) :
    (MatrixExponential.scalarExponential (value p a)).val.Equiv d.val := by
  induction p generalizing a with
  | nil => exact ha
  | step hcd tail ih => exact ih _ (LogarithmBranchCharts.exponential _ _ a ha _ hcd)

theorem terminal_exponential {c d : Scalar} {hc : Nonzero c} {hd : Nonzero d}
    (p : Chain c hc d hd) (a : Scalar)
    (ha : (MatrixExponential.scalarExponential a).val.Equiv c.val)
    (z : Scalar) (hz : (terminalFunction p a).domain z) :
    (MatrixExponential.scalarExponential ((terminalFunction p a).eval z hz)).val.Equiv z.val :=
  LogarithmBranchCharts.exponential d hd (value p a) (value_exponential p a ha) z hz

theorem terminal_initial {c d : Scalar} {hc : Nonzero c} {hd : Nonzero d}
    (p : Chain c hc d hd) (a : Scalar) :
    ((terminalFunction p a).eval d (RelativeLogarithm.center_mem d hd)).val.Equiv (value p a).val :=
  LogarithmBranchCharts.initial d hd (value p a)

theorem terminal_derivative {c d : Scalar} {hc : Nonzero c} {hd : Nonzero d}
    (p : Chain c hc d hd) (a : Scalar) (hF : DomainFunctions.Holomorphic (terminalFunction p a))
    (z : Scalar) (hz : (terminalFunction p a).domain z) :
    (hF.derivative z hz).val.Equiv (RepresentedReciprocal.inverse z (RelativeLogarithm.nonzero d hd z hz)).val :=
  LogarithmBranchCharts.derivative_reciprocal d hd (value p a) hF z hz

theorem edge_segment (c d : Scalar) (hc : Nonzero c) (hcd : RelativeLogarithm.domain c hc d)
    (t : Rat) (ht : UniformPath.unitInterval t) :
    RelativeLogarithm.domain c hc (AffineSegment.point c d t) :=
  RelativeLogarithm.affine_mem c hc c d (RelativeLogarithm.center_mem c hc) hcd t ht

theorem edge_germ (c d : Scalar) (hc : Nonzero c) (hd : Nonzero d)
    (hcd : RelativeLogarithm.domain c hc d) (a z : Scalar)
    (hz : Small (sub z.val d.val) (LogarithmBranchCharts.overlapRadius c d hc hd hcd).val) :
    ((LogarithmBranchCharts.function c hc a).eval z
      (LogarithmBranchCharts.overlapRadius_inside c d hc hd hcd z hz).1).val.Equiv
    ((LogarithmBranchCharts.function d hd ((LogarithmBranchCharts.function c hc a).eval d hcd)).eval z
      (LogarithmBranchCharts.overlapRadius_inside c d hc hd hcd z hz).2).val :=
  LogarithmBranchCharts.recenter_agreement c d hc hd a hcd z
    (LogarithmBranchCharts.overlapRadius_inside c d hc hd hcd z hz)

def append {c d e : Scalar} {hc : Nonzero c} {hd : Nonzero d} {he : Nonzero e}
    (p : Chain c hc d hd) (q : Chain d hd e he) : Chain c hc e he :=
  match p with
  | .nil _ _ => q
  | .step hcd tail => .step hcd (append tail q)

theorem value_append {c d e : Scalar} {hc : Nonzero c} {hd : Nonzero d} {he : Nonzero e}
    (p : Chain c hc d hd) (q : Chain d hd e he) (a : Scalar) :
    (value (append p q) a).val.Equiv (value q (value p a)).val := by
  induction p generalizing a with
  | nil => exact equiv_refl _ (value q a).property
  | step hcd tail ih => exact ih q _

/-- An admissible subdivision has the same continued value. All three
edge domain hypotheses are genuine local chart membership, not assumed
agreement of the continued logarithms. -/
theorem subdivision {c d e f : Scalar} {hc : Nonzero c} {hd : Nonzero d}
    {he : Nonzero e} {hf : Nonzero f} (hce : RelativeLogarithm.domain c hc e)
    (hcd : RelativeLogarithm.domain c hc d) (hde : RelativeLogarithm.domain d hd e)
    (tail : Chain e he f hf) (a : Scalar) :
    (value (.step hce tail) a).val.Equiv (value (.step hcd (.step hde tail)) a).val :=
  value_congr tail _ _ (LogarithmBranchCharts.recenter_agreement c d hc hd a hcd e ⟨hce,hde⟩)

theorem terminal_agreement {c d : Scalar} {hc : Nonzero c} {hd : Nonzero d}
    (p q : Chain c hc d hd) (a b : Scalar) (h : (value p a).val.Equiv (value q b).val)
    (z w : Scalar) (hz : (terminalFunction p a).domain z) (hw : (terminalFunction q b).domain w)
    (hzw : z.val.Equiv w.val) :
    ((terminalFunction p a).eval z hz).val.Equiv ((terminalFunction q b).eval w hw).val :=
  LogarithmBranchCharts.value_congr d d hd hd _ _ (equiv_refl _ d.property) h z w hz hw hzw

end ComputableAnalysis.RiemannHilbert.LogarithmContinuation
