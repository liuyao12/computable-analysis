import ComputableAnalysis.ModularForms.WideLambertFifthDerivative
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

/-- Executable degree-three Lambert sum on the larger disk. -/
def wideLambertThirdValue (q : Scalar) (hq : Small q.val ((1:Rat)/64)) : Scalar :=
  ⟨weightedLambertSum q (1/64) 3 (by decide +kernel) (by decide +kernel) hq,
    weightedLambertSum_valid q (1/64) 3 (by decide +kernel) (by decide +kernel) hq (by decide +kernel)⟩

theorem wideLambertThirdValue_congr (q w : Scalar)
    (hq : Small q.val ((1:Rat)/64)) (hw : Small w.val ((1:Rat)/64)) (he : q.val.Equiv w.val) :
    (wideLambertThirdValue q hq).val.Equiv (wideLambertThirdValue w hw).val :=
  weightedLambertSum_congr q w (1/64) (1/64) 3
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    hq hw (by decide +kernel) (by decide +kernel) he

theorem wideLambertThirdValue_close_prefix (q : Scalar) (hq : Small q.val ((1:Rat)/64)) (N : Nat) :
    Small (sub (wideLambertThirdValue q hq).val
      (ScalarSeries.block (weightedLambertTerm q (1/64) 3) 0 N)) (((1:Rat)/2)*((1:Rat)/4)^N) := by
  have h := weightedLambertSum_close q (1/64) 3 (by decide +kernel) (by decide +kernel) hq (by decide +kernel) N
  have hc : (4:Rat)*(8*(1/64))=1/2 := by decide +kernel
  have hr : weightedLambertRatio (1/64) 3=1/4 := by decide +kernel
  rw [hc,hr] at h
  exact h

theorem wideLambertThirdValue_tail_shrinks : ShrinksToZero (fun N => ((1:Rat)/2)*((1:Rat)/4)^N) := by
  have h := weightedLambertSum_tail_shrinks (1/64) 3 (by decide +kernel) (by decide +kernel)
  have hc : (4:Rat)*(8*(1/64))=1/2 := by decide +kernel
  have hr : weightedLambertRatio (1/64) 3=1/4 := by decide +kernel
  simpa only [hc,hr] using h

theorem wideLambertThirdValue_tau_agreement (q : Scalar) (hq : tauEulerNomeDomain q)
    (hw : Small q.val ((1:Rat)/64)) :
    (wideLambertThirdValue q hw).val.Equiv (tauHigherLambertValue q hq 3 (by decide +kernel)).val :=
  weightedLambertSum_congr q q (1/64) (1/1024) 3
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    hw (LocalODE.interior_bound _ q hq) (by decide +kernel) (by decide +kernel) (equiv_refl _ q.property)
end ComputableAnalysis.ModularForms
