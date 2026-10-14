import ComputableAnalysis.ModularForms.LambertSharperSlopeBound
import ComputableAnalysis.ModularForms.TauWeightedLambertSlopeSeries
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert

def wideLambertFifthSlopeTerm (q : Scalar) (hq : Small q.val ((1:Rat)/64)) (n : Nat) : Scalar :=
  weightedLambertSlope q (1/64) 5 (by decide +kernel) (by decide +kernel) hq n
private theorem wideLambertFifthSlopeTerm_bound (q : Scalar) (hq : Small q.val ((1:Rat)/64)) (n : Nat) :
    Small (wideLambertFifthSlopeTerm q hq n).val (2*512*((1:Rat)/4)^n) := by
  have h := weightedLambertFifthSlope_sharp_bound q (1/64) (by decide +kernel) (by decide +kernel) hq n
  have hr : (16:Rat)*(1/64)=1/4 := by decide +kernel
  simpa only [wideLambertFifthSlopeTerm,hr,show (2:Rat)*512=1024 by decide +kernel] using h

/-- Executable wider-disk slope sum; identifying it as the derivative is a separate theorem. -/
def wideLambertFifthSlopeValue (q : Scalar) (hq : Small q.val ((1:Rat)/64)) : Scalar :=
  ⟨ScalarSeries.value (fun n => (wideLambertFifthSlopeTerm q hq n).val)
      (fun n => (wideLambertFifthSlopeTerm q hq n).property) 512 (1/4),
    ScalarSeries.value_valid _ _ _ _ (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (wideLambertFifthSlopeTerm_bound q hq)⟩

theorem wideLambertFifthSlopeValue_close_prefix (q : Scalar) (hq : Small q.val ((1:Rat)/64)) (N : Nat) :
    Small (sub (wideLambertFifthSlopeValue q hq).val
      (ScalarSeries.block (fun n => (wideLambertFifthSlopeTerm q hq n).val) 0 N)) (2048*((1:Rat)/4)^N) := by
  have h := ScalarSeries.value_close (fun n => (wideLambertFifthSlopeTerm q hq n).val)
    (fun n => (wideLambertFifthSlopeTerm q hq n).property) 512 (1/4)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (wideLambertFifthSlopeTerm_bound q hq) N
  simpa only [wideLambertFifthSlopeValue,show (4:Rat)*512=2048 by decide +kernel] using h

theorem wideLambertFifthSlopeValue_tail_shrinks : ShrinksToZero (fun N => 2048*((1:Rat)/4)^N) := by
  simpa only [show (4:Rat)*512=2048 by decide +kernel] using
    LocalODE.tail_bound_shrinks 512 (1/4) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem wideLambertFifthSlopeValue_congr (q w : Scalar)
    (hq : Small q.val ((1:Rat)/64)) (hw : Small w.val ((1:Rat)/64)) (he : q.val.Equiv w.val) :
    (wideLambertFifthSlopeValue q hq).val.Equiv (wideLambertFifthSlopeValue w hw).val :=
  ScalarSeries.value_congr (fun n => (wideLambertFifthSlopeTerm q hq n).val) (fun n => (wideLambertFifthSlopeTerm w hw n).val)
    (fun n => (wideLambertFifthSlopeTerm q hq n).property) (fun n => (wideLambertFifthSlopeTerm w hw n).property)
    512 (1/4) 512 (1/4) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (wideLambertFifthSlopeTerm_bound q hq) (wideLambertFifthSlopeTerm_bound w hw)
    (weightedLambertSlope_congr q w (1/64) (1/64) 5 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) hq hw he)

/-- Exact overlap agreement with the existing constructed actual derivative value. -/
theorem wideLambertFifthSlopeValue_tau_agreement (q : Scalar) (hq : tauEulerNomeDomain q)
    (hw : Small q.val ((1:Rat)/64)) :
    (wideLambertFifthSlopeValue q hw).val.Equiv
      (tauWeightedLambertSlopeValue q hq 5 (by decide +kernel)).val := by
  let oldTerm (n : Nat) := weightedLambertSlope q (1/1024) 5 (by decide +kernel) (by decide +kernel)
    (LocalODE.interior_bound _ q hq) n
  have oldBound (n : Nat) : Small (oldTerm n).val (2*32*(weightedSlopeRatio 5)^n) := by
    have h := weightedLambertSlope_geometric_bound q (1/1024) 5
      (by decide +kernel) (by decide +kernel) (LocalODE.interior_bound _ q hq) n
    simpa only [oldTerm,weightedSlopeRatio,show (2:Rat)*32=64 by decide +kernel] using h
  exact ScalarSeries.value_congr (fun n => (wideLambertFifthSlopeTerm q hw n).val) (fun n => (oldTerm n).val)
    (fun n => (wideLambertFifthSlopeTerm q hw n).property) (fun n => (oldTerm n).property)
    512 (1/4) 32 (weightedSlopeRatio 5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (wideLambertFifthSlopeTerm_bound q hw) oldBound
    (weightedLambertSlope_congr q q (1/64) (1/1024) 5 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) hw (LocalODE.interior_bound _ q hq) (equiv_refl _ q.property))
end ComputableAnalysis.ModularForms
