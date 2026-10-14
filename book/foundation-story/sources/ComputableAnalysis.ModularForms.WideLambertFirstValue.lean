import ComputableAnalysis.ModularForms.WideFiniteEulerLambert
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

/-- Actual degree-one Lambert sum on the wider represented nome disk. -/
def wideLambertFirstValue (q : Scalar) (hq : Small q.val ((1:Rat)/64)) : Scalar :=
  ⟨weightedLambertSum q (1/64) 1 (by decide +kernel) (by decide +kernel) hq,
    weightedLambertSum_valid q (1/64) 1 (by decide +kernel) (by decide +kernel) hq (by decide +kernel)⟩

theorem wideLambertFirstValue_close_prefix (q : Scalar) (hq : Small q.val ((1:Rat)/64)) (N : Nat) :
    Small (sub (wideLambertFirstValue q hq).val (ScalarSeries.block (weightedLambertTerm q (1/64) 1) 0 N))
      ((1/2:Rat)*((1:Rat)/16)^N) := by
  have h := weightedLambertSum_close q (1/64) 1 (by decide +kernel) (by decide +kernel) hq (by decide +kernel) N
  rw [show (4:Rat)*(8*(1/64))=1/2 by decide +kernel,
    show weightedLambertRatio (1/64) 1=(1/16:Rat) by decide +kernel] at h
  exact h

theorem wideLambertFirstValue_tail_shrinks : ShrinksToZero (fun N => (1/2:Rat)*((1:Rat)/16)^N) := by
  have h := LocalODE.tail_bound_shrinks (1/8) (1/16) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simpa only [show (4:Rat)*(1/8)=1/2 by decide +kernel] using h

theorem wideLambertFirstValue_congr (q w : Scalar) (hq : Small q.val ((1:Rat)/64))
    (hw : Small w.val ((1:Rat)/64)) (he : q.val.Equiv w.val) :
    (wideLambertFirstValue q hq).val.Equiv (wideLambertFirstValue w hw).val :=
  weightedLambertSum_congr q w (1/64) (1/64) 1 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) hq hw (by decide +kernel) (by decide +kernel) he

/-- Exact agreement with any supplied valid original degree-one Lambert schedule. -/
theorem wideLambertFirstValue_agreement (q : Scalar) (hq : Small q.val ((1:Rat)/64))
    (r : Rat) (hr : 0≤r) (hl : 4*r≤(1:Rat)/2) (hqr : Small q.val r)
    (hg : weightedLambertRatio r 1≤(1:Rat)/2) :
    (wideLambertFirstValue q hq).val.Equiv (weightedLambertSum q r 1 hr hl hqr) :=
  weightedLambertSum_congr q q (1/64) r 1 (by decide +kernel) hr (by decide +kernel) hl
    hq hqr (by decide +kernel) hg (equiv_refl _ q.property)

theorem wideLambertFirstValue_tau_agreement (q : Scalar) (hq : tauEulerNomeDomain q)
    (hw : Small q.val ((1:Rat)/64)) :
    (wideLambertFirstValue q hw).val.Equiv (tauHigherLambertValue q hq 1 (by omega)).val :=
  wideLambertFirstValue_agreement q hw (1/1024) (by decide +kernel) (by decide +kernel)
    (LocalODE.interior_bound _ q hq) (by decide +kernel)

end ComputableAnalysis.ModularForms
