import ComputableAnalysis.ModularForms.LambertSharperSlopeBound
import ComputableAnalysis.ModularForms.TauWeightedLambertSlopeSeries
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert

def wideLambertFirstSlopeTerm (q : Scalar) (hq : Small q.val ((1:Rat)/64)) (n : Nat) : Scalar :=
  weightedLambertSlope q (1/64) 1 (by decide +kernel) (by decide +kernel) hq n
private theorem wideLambertFirstSlopeTerm_bound (q : Scalar) (hq : Small q.val ((1:Rat)/64)) (n : Nat) :
    Small (wideLambertFirstSlopeTerm q hq n).val (2*32*((1:Rat)/8)^n) := by
  have h := weightedLambertSlope_geometric_bound q (1/64) 1 (by decide +kernel) (by decide +kernel) hq n
  have hr : (2^(1+1):Rat)*(2*(1/64))=1/8 := by decide +kernel
  simpa only [wideLambertFirstSlopeTerm,hr,show (2:Rat)*32=64 by decide +kernel] using h

/-- Executable wider-disk slope sum; identifying it as the derivative is a separate theorem. -/
def wideLambertFirstSlopeValue (q : Scalar) (hq : Small q.val ((1:Rat)/64)) : Scalar :=
  ⟨ScalarSeries.value (fun n => (wideLambertFirstSlopeTerm q hq n).val)
      (fun n => (wideLambertFirstSlopeTerm q hq n).property) 32 (1/8),
    ScalarSeries.value_valid _ _ _ _ (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (wideLambertFirstSlopeTerm_bound q hq)⟩

theorem wideLambertFirstSlopeValue_close_prefix (q : Scalar) (hq : Small q.val ((1:Rat)/64)) (N : Nat) :
    Small (sub (wideLambertFirstSlopeValue q hq).val
      (ScalarSeries.block (fun n => (wideLambertFirstSlopeTerm q hq n).val) 0 N)) (128*((1:Rat)/8)^N) := by
  have h := ScalarSeries.value_close (fun n => (wideLambertFirstSlopeTerm q hq n).val)
    (fun n => (wideLambertFirstSlopeTerm q hq n).property) 32 (1/8)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (wideLambertFirstSlopeTerm_bound q hq) N
  simpa only [wideLambertFirstSlopeValue,show (4:Rat)*32=128 by decide +kernel] using h

theorem wideLambertFirstSlopeValue_tail_shrinks : ShrinksToZero (fun N => 128*((1:Rat)/8)^N) := by
  simpa only [show (4:Rat)*32=128 by decide +kernel] using
    LocalODE.tail_bound_shrinks 32 (1/8) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem wideLambertFirstSlopeValue_congr (q w : Scalar)
    (hq : Small q.val ((1:Rat)/64)) (hw : Small w.val ((1:Rat)/64)) (he : q.val.Equiv w.val) :
    (wideLambertFirstSlopeValue q hq).val.Equiv (wideLambertFirstSlopeValue w hw).val :=
  ScalarSeries.value_congr (fun n => (wideLambertFirstSlopeTerm q hq n).val) (fun n => (wideLambertFirstSlopeTerm w hw n).val)
    (fun n => (wideLambertFirstSlopeTerm q hq n).property) (fun n => (wideLambertFirstSlopeTerm w hw n).property)
    32 (1/8) 32 (1/8) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (wideLambertFirstSlopeTerm_bound q hq) (wideLambertFirstSlopeTerm_bound w hw)
    (weightedLambertSlope_congr q w (1/64) (1/64) 1 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) hq hw he)

/-- Exact overlap agreement with the existing constructed actual derivative value. -/
theorem wideLambertFirstSlopeValue_tau_agreement (q : Scalar) (hq : tauEulerNomeDomain q)
    (hw : Small q.val ((1:Rat)/64)) :
    (wideLambertFirstSlopeValue q hw).val.Equiv
      (tauWeightedLambertSlopeValue q hq 1 (by decide +kernel)).val := by
  let oldTerm (n : Nat) := weightedLambertSlope q (1/1024) 1 (by decide +kernel) (by decide +kernel)
    (LocalODE.interior_bound _ q hq) n
  have oldBound (n : Nat) : Small (oldTerm n).val (2*32*(weightedSlopeRatio 1)^n) := by
    have h := weightedLambertSlope_geometric_bound q (1/1024) 1
      (by decide +kernel) (by decide +kernel) (LocalODE.interior_bound _ q hq) n
    simpa only [oldTerm,weightedSlopeRatio,show (2:Rat)*32=64 by decide +kernel] using h
  exact ScalarSeries.value_congr (fun n => (wideLambertFirstSlopeTerm q hw n).val) (fun n => (oldTerm n).val)
    (fun n => (wideLambertFirstSlopeTerm q hw n).property) (fun n => (oldTerm n).property)
    32 (1/8) 32 (weightedSlopeRatio 1)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (wideLambertFirstSlopeTerm_bound q hw) oldBound
    (weightedLambertSlope_congr q q (1/64) (1/1024) 1 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) hw (LocalODE.interior_bound _ q hq) (equiv_refl _ q.property))
end ComputableAnalysis.ModularForms
