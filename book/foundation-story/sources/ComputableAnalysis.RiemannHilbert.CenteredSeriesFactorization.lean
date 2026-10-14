import ComputableAnalysis.RiemannHilbert.SeriesSuccessorFactorization
import ComputableAnalysis.RiemannHilbert.CenteredSeriesEstimates
import ComputableAnalysis.RiemannHilbert.GeneralSeriesDerivativeInitial

/-! Removing the constant term of an actual centered series constructs a
holomorphic quotient, including the center. The division identity is proved
from shrinking series tails, and never divides by a possibly zero input. -/
namespace ComputableAnalysis.RiemannHilbert.CenteredSeries
open ComplexRaw FunctionTheory LocalODE DomainFunctions
set_option autoImplicit false
variable (p : Scalar) (c : Nat → ComplexRaw) (hc : ∀ k, (c k).Valid)
    (C K R : Rat) (hC : 0≤C) (hK : 0≤K) (hR : 0≤R)
    (hb : ∀ k, Small (c k) (C*K^k)) (hl : 8*K*R≤(1:Rat)/2)

def successor : DomainFunctions.Map :=
  function p (fun k => c (k+1)) (fun k => hc (k+1)) (C*K) K R
    (Rat.mul_nonneg hC hK) hK hR (BoundedSeries.successor_majorant c C K hb) hl

def successor_holomorphic : Holomorphic (successor p c hc C K R hC hK hR hb hl) :=
  holomorphic p (fun k => c (k+1)) (fun k => hc (k+1)) (C*K) K R
    (Rat.mul_nonneg hC hK) hK hR (BoundedSeries.successor_majorant c C K hb) hl

theorem initial (hp : Centered.domain p R p) :
    ((function p c hc C K R hC hK hR hb hl).eval p hp).val.Equiv (c 0) := by
  have hlocal : 2*K*R≤(1:Rat)/2 := by have := Rat.mul_nonneg hK hR; grind only
  exact equiv_trans ((function p c hc C K R hC hK hR hb hl).eval p hp).property
    (BoundedSeries.sumValue_valid c zero hc (ofQComplex_valid _) C K R hC hK hR hb (Small.zero hR) hlocal)
    (hc 0)
    (coefficientSum_congr c c (Centered.offset p p).val zero hc hc (Centered.offset p p).property
      (ofQComplex_valid _) (fun k => equiv_refl _ (hc k)) (Centered.offset_self p) C K R
      hC hK hR hb (interior_bound R _ hp) hlocal)
    (coefficientSum_zero c hc C K R hC hK hR hb hlocal)

theorem factorization (z : Scalar) (hz : Centered.domain p R z) :
    ((function p c hc C K R hC hK hR hb hl).eval z hz).val.Equiv
      (add (c 0) (mul (Centered.offset p z).val
        ((successor p c hc C K R hC hK hR hb hl).eval z hz).val)) :=
  BoundedSeries.sumValue_successor c (Centered.offset p z).val hc (Centered.offset p z).property C K R
    hC hK hR hb (interior_bound R _ hz) (by have := Rat.mul_nonneg hK hR; grind only)

theorem successor_initial (hp : Centered.domain p R p) :
    ((successor p c hc C K R hC hK hR hb hl).eval p hp).val.Equiv (c 1) :=
  initial p (fun k => c (k+1)) (fun k => hc (k+1)) (C*K) K R (Rat.mul_nonneg hC hK) hK hR
    (BoundedSeries.successor_majorant c C K hb) hl hp

theorem derivative_initial (hp : Centered.domain p R p) :
    ((holomorphic p c hc C K R hC hK hR hb hl).derivative p hp).val.Equiv (c 1) := by
  have hlocal : 4*K*R≤(1:Rat)/2 := by have := Rat.mul_nonneg hK hR; grind only
  exact equiv_trans ((holomorphic p c hc C K R hC hK hR hb hl).derivative p hp).property
    (BoundedSeries.sumDerivative_valid c zero hc (ofQComplex_valid _) C K R hC hK hR hb (Small.zero hR) hlocal)
    (hc 1)
    (BoundedSeries.sumDerivative_congr c (Centered.offset p p).val zero hc (Centered.offset p p).property
      (ofQComplex_valid _) (Centered.offset_self p) C K R hC hK hR hb (interior_bound R _ hp) hlocal)
    (BoundedSeries.sumDerivative_zero c hc C K R hC hK hR hb hlocal)

end ComputableAnalysis.RiemannHilbert.CenteredSeries
