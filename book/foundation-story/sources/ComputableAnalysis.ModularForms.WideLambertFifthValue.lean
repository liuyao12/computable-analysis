import ComputableAnalysis.ModularForms.SharperLambertFifthSeries
import ComputableAnalysis.ModularForms.TauHigherLambertHolomorphic
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

/-- Executable actual Lambert value on the larger closed rational disk. -/
def wideLambertFifthValue (q : Scalar) (hq : Small q.val ((1:Rat)/64)) : Scalar :=
  ⟨sharperLambertFifthSum q (1/64) (by decide +kernel) (by decide +kernel) hq,
    sharperLambertFifthSum_valid q (1/64) (by decide +kernel) (by decide +kernel) hq (by decide +kernel)⟩

theorem wideLambertFifthValue_congr (q w : Scalar)
    (hq : Small q.val ((1:Rat)/64)) (hw : Small w.val ((1:Rat)/64)) (he : q.val.Equiv w.val) :
    (wideLambertFifthValue q hq).val.Equiv (wideLambertFifthValue w hw).val :=
  sharperLambertFifthSum_congr q w (1/64) (1/64)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    hq hw (by decide +kernel) (by decide +kernel) he

/-- The new sum has a concrete certified approximation schedule. -/
theorem wideLambertFifthValue_close_prefix (q : Scalar) (hq : Small q.val ((1:Rat)/64)) (N : Nat) :
    Small (sub (wideLambertFifthValue q hq).val
      (ScalarSeries.block (weightedLambertTerm q (1/64) 5) 0 N)) (8*((1:Rat)/8)^N) := by
  have h := sharperLambertFifthSum_close q (1/64) (by decide +kernel) (by decide +kernel) hq (by decide +kernel) N
  have hc : (4:Rat)*(128*(1/64))=8 := by decide +kernel
  have hr : (8:Rat)*(1/64)=1/8 := by decide +kernel
  rw [hc,hr] at h
  exact h

theorem wideLambertFifthValue_tail_shrinks : ShrinksToZero (fun N => 8*((1:Rat)/8)^N) := by
  have h := sharperLambertFifthSum_tail_shrinks (1/64) (by decide +kernel) (by decide +kernel)
  have hc : (4:Rat)*(128*(1/64))=8 := by decide +kernel
  have hr : (8:Rat)*(1/64)=1/8 := by decide +kernel
  simpa only [hc,hr] using h

/-- Exact agreement with the original actual holomorphic evaluator on the original nome chart. -/
theorem wideLambertFifthValue_tau_agreement (q : Scalar) (hq : tauEulerNomeDomain q)
    (hw : Small q.val ((1:Rat)/64)) :
    (wideLambertFifthValue q hw).val.Equiv (tauHigherLambertValue q hq 5 (by decide +kernel)).val :=
  sharperLambertFifthSum_agreement q q (1/64) (1/1024)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    hw (LocalODE.interior_bound _ q hq) (by decide +kernel) (by decide +kernel)
    (equiv_refl _ q.property)

/-- Membership in the original chart automatically supplies the larger disk bound. -/
theorem tauEulerNomeDomain_wide_fifth_bound (q : Scalar) (hq : tauEulerNomeDomain q) :
    Small q.val ((1:Rat)/64) :=
  (LocalODE.interior_bound _ q hq).mono (by decide +kernel)
end ComputableAnalysis.ModularForms
