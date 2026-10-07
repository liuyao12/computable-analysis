import ComputableAnalysis.ExponentialComputations.PositiveLogarithm
import ComputableAnalysis.ModularForms.RelativeLogarithmOverlapConstancy

/-! Public complex exponential and normalized logarithm germs. The branch
is an executable Taylor chart, not a record assuming its analytic laws.
Continuation carries its normalization through actual open overlaps. -/
namespace ComputableAnalysis.ExponentialComputations.Complex
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions NonzeroBoxSearch ModularForms
set_option maxHeartbeats 1000000
private def scalarClass (z : Scalar) := ComplexRawQuotient.ofRaw z.val z.property

def exp : Scalar → Scalar := entireExponentialValue
def expFunction : DomainFunctions.Map := entireExponential
def expHolomorphic : DomainFunctions.Holomorphic expFunction := entireExponential_holomorphic
theorem exp_congr (z w : Scalar) (h : z.val.Equiv w.val) :
    (exp z).val.Equiv (exp w).val := entireExponentialValue_congr z w h
theorem exp_derivative (z : Scalar) :
    (expHolomorphic.derivative z trivial).val.Equiv (exp z).val :=
  entireExponential_derivative_value z
theorem exp_add (z w : Scalar) :
    (mul (exp z).val (exp w).val).Equiv (exp (scalarSum z w)).val :=
  entireExponential_addition z w
theorem exp_nonzero (z : Scalar) : Nonzero (exp z) := entireExponential_ne_zero z
theorem exp_real (x : RealInput) :
    (exp (realAxis x)).val.Equiv (realAxis (ExponentialComputations.exp x)).val := exp_real_embedding x

/-- A normalization is a logarithm of the center. Analytic and overlap laws
are proved below from the actual series and are not fields of this record. -/
structure LogSeed where
  center : Scalar
  nonzero : Nonzero center
  value : Scalar
  exponential : (exp value).val.Equiv center.val

namespace LogSeed
def function (s : LogSeed) : DomainFunctions.Map :=
  LogarithmBranchCharts.function s.center s.nonzero s.value
def holomorphic (s : LogSeed) : DomainFunctions.Holomorphic s.function :=
  LogarithmBranchCharts.holomorphic s.center s.nonzero s.value
theorem exponential_eval (s : LogSeed) (z : Scalar) (hz : s.function.domain z) :
    (exp (s.function.eval z hz)).val.Equiv z.val := by
  have ha := equiv_trans (MatrixExponential.scalarExponential s.value).property
    (exp s.value).property s.center.property (scalarExponential_agreement s.value) s.exponential
  exact equiv_trans (exp (s.function.eval z hz)).property
    (MatrixExponential.scalarExponential (s.function.eval z hz)).property z.property
    (equiv_symm (scalarExponential_agreement _))
    (LogarithmBranchCharts.exponential _ _ _ ha z hz)
theorem initial (s : LogSeed) :
    (s.function.eval s.center (RelativeLogarithm.center_mem _ s.nonzero)).val.Equiv s.value.val :=
  LogarithmBranchCharts.initial _ _ _
theorem derivative (s : LogSeed) (z : Scalar) (hz : s.function.domain z) :
    (s.holomorphic.derivative z hz).val.Equiv
      (RepresentedReciprocal.inverse z (RelativeLogarithm.nonzero _ s.nonzero z hz)).val :=
  LogarithmBranchCharts.derivative_reciprocal _ _ _ s.holomorphic z hz
theorem congr (s t : LogSeed) (hc : s.center.val.Equiv t.center.val)
    (ha : s.value.val.Equiv t.value.val) (z w : Scalar)
    (hz : s.function.domain z) (hw : t.function.domain w) (h : z.val.Equiv w.val) :
    (s.function.eval z hz).val.Equiv (t.function.eval w hw).val :=
  LogarithmBranchCharts.value_congr _ _ _ _ _ _ hc ha z w hz hw h

def continueAlong (s : LogSeed) {d : Scalar} {hd : Nonzero d}
    (p : LogarithmContinuation.Chain s.center s.nonzero d hd) : LogSeed where
  center := d
  nonzero := hd
  value := LogarithmContinuation.value p s.value
  exponential := by
    have ha := equiv_trans (MatrixExponential.scalarExponential s.value).property
      (exp s.value).property s.center.property (scalarExponential_agreement s.value) s.exponential
    exact equiv_trans (exp _).property (MatrixExponential.scalarExponential _).property d.property
      (equiv_symm (scalarExponential_agreement _)) (LogarithmContinuation.value_exponential p s.value ha)

def recenter (s : LogSeed) (d : Scalar) (hd : Nonzero d) (h : s.function.domain d) : LogSeed :=
  ⟨d,hd,s.function.eval d h,s.exponential_eval d h⟩
theorem recenter_agrees (s : LogSeed) (d : Scalar) (hd : Nonzero d)
    (h : s.function.domain d) (z : Scalar)
    (hz : RelativeLogarithm.commonDomain s.center d s.nonzero hd z) :
    (s.function.eval z hz.1).val.Equiv ((s.recenter d hd h).function.eval z hz.2).val :=
  LogarithmBranchCharts.recenter_agreement _ _ _ _ _ h z hz

/-- Constancy on the entire actual chart intersection, proved by finite
telescoping with uniform remainders and convex segment coverage. -/
theorem overlap_difference (s t : LogSeed) (p z : Scalar)
    (hp : s.function.domain p ∧ t.function.domain p)
    (hz : s.function.domain z ∧ t.function.domain z) :
    (sub (s.function.eval z hz.1).val (t.function.eval z hz.2).val).Equiv
      (sub (s.function.eval p hp.1).val (t.function.eval p hp.2).val) := by
  have hr := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := sub_valid ((RelativeLogarithm.function s.center s.nonzero).eval z hz.1).property
      ((RelativeLogarithm.function t.center t.nonzero).eval z hz.2).property)
    (hright := sub_valid ((RelativeLogarithm.function s.center s.nonzero).eval p hp.1).property
      ((RelativeLogarithm.function t.center t.nonzero).eval p hp.2).property)
    (relativeLogarithm_overlap_difference_constant s.center t.center s.nonzero t.nonzero p z hp hz)
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := sub_valid (s.function.eval z hz.1).property (t.function.eval z hz.2).property)
    (hright := sub_valid (s.function.eval p hp.1).property (t.function.eval p hp.2).property)
  let A := scalarClass s.value
  let B := scalarClass t.value
  let CZ := scalarClass ((RelativeLogarithm.function s.center s.nonzero).eval z hz.1)
  let DZ := scalarClass ((RelativeLogarithm.function t.center t.nonzero).eval z hz.2)
  let CP := scalarClass ((RelativeLogarithm.function s.center s.nonzero).eval p hp.1)
  let DP := scalarClass ((RelativeLogarithm.function t.center t.nonzero).eval p hp.2)
  change CZ-DZ=CP-DP at hr
  change (A+CZ)-(B+DZ)=(A+CP)-(B+DP)
  grind only
theorem overlap_agrees (s t : LogSeed) (p z : Scalar)
    (hp : s.function.domain p ∧ t.function.domain p)
    (hz : s.function.domain z ∧ t.function.domain z)
    (h : (s.function.eval p hp.1).val.Equiv (t.function.eval p hp.2).val) :
    (s.function.eval z hz.1).val.Equiv (t.function.eval z hz.2).val := by
  have hd := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := sub_valid (s.function.eval z hz.1).property (t.function.eval z hz.2).property)
    (hright := sub_valid (s.function.eval p hp.1).property (t.function.eval p hp.2).property)
    (s.overlap_difference t p z hp hz)
  have he := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := (s.function.eval p hp.1).property) (hright := (t.function.eval p hp.2).property) h
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (s.function.eval z hz.1).property) (hright := (t.function.eval z hz.2).property)
  let SZ := scalarClass (s.function.eval z hz.1)
  let TZ := scalarClass (t.function.eval z hz.2)
  let SP := scalarClass (s.function.eval p hp.1)
  let TP := scalarClass (t.function.eval p hp.2)
  change SZ-TZ=SP-TP at hd
  change SP=TP at he
  change SZ=TZ
  grind only
end LogSeed

/-- Executable selection of a normalized germ at every nonzero input. The
selected pointwise values are not claimed to form a global analytic log. -/
def logarithmAt (z : Scalar) (hz : Nonzero z) : LogSeed where
  center := z
  nonzero := hz
  value := NonzeroLogarithmConstruction.value z hz
  exponential := equiv_trans (exp _).property (MatrixExponential.scalarExponential _).property z.property
    (equiv_symm (scalarExponential_agreement _)) (NonzeroLogarithmConstruction.exponential z hz)

/-- Choose the real normalization before extending into a complex chart. -/
def realLogarithmAt (x : PositiveInput) : LogSeed where
  center := realAxis x.val
  nonzero := positive_real_nonzero x.val x.property
  value := realAxis (log x)
  exponential := equiv_trans (exp _).property (realAxis (ExponentialComputations.exp (log x))).property
    (realAxis x.val).property (exp_real (log x))
    (real_embedding_congr (ExponentialComputations.exp (log x)).property x.val.property (exp_log x))

theorem realLogarithmAt_initial (x : PositiveInput) :
    ((realLogarithmAt x).function.eval (realAxis x.val)
      (RelativeLogarithm.center_mem _ (positive_real_nonzero x.val x.property))).val.Equiv
      (realAxis (log x)).val := (realLogarithmAt x).initial

end ComputableAnalysis.ExponentialComputations.Complex
