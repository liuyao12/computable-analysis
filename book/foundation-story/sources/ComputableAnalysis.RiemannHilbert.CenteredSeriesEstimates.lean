import ComputableAnalysis.RiemannHilbert.GeneralSeriesHolomorphic
import ComputableAnalysis.RiemannHilbert.DomainFunctions
import ComputableAnalysis.RiemannHilbert.TranslatedHolomorphic
import ComputableAnalysis.RiemannHilbert.ScalarTopology

/-! Actual centered scalar series retain uniform first-order error radii.
The center and coefficients may be arbitrary valid represented complex
values. Bounds are consequences of coefficient majorants and finite tails. -/
namespace ComputableAnalysis.RiemannHilbert.CenteredSeries
open ComplexRaw FunctionTheory LocalODE DomainFunctions
set_option autoImplicit false
variable (p : Scalar) (c : Nat → ComplexRaw) (hc : ∀ k, (c k).Valid)
    (C K R : Rat) (hC : 0 ≤ C) (hK : 0 ≤ K) (hR : 0 ≤ R)
    (hb : ∀ k, Small (c k) (C*K^k)) (hl : 8*K*R ≤ (1 : Rat)/2)

def function : DomainFunctions.Map := ofCertified
  (CertifiedFunctions.translateInput p (BoundedSeries.seriesMap c hc C K R hC hK hR hb hl))

def holomorphic : Holomorphic (function p c hc C K R hC hK hR hb hl) :=
  ofCertifiedHolomorphic (CertifiedFunctions.translateDerivative p
    (BoundedSeries.seriesMap_holomorphic c hc C K R hC hK hR hb hl))

def openData : ScalarTopology.OpenData (Centered.domain p R) :=
  ⟨(function p c hc C K R hC hK hR hb hl).domain_congr,
    (holomorphic p c hc C K R hC hK hR hb hl).openDomain.radius,
    (holomorphic p c hc C K R hC hK hR hb hl).openDomain.inside⟩

theorem value_bound (z : Scalar) (hz : Centered.domain p R z) :
    Small ((function p c hc C K R hC hK hR hb hl).eval z hz).val (4*C) :=
  coefficientSum_bound c (Centered.offset p z).val hc (Centered.offset p z).property C K R
    hC hK hR hb (interior_bound R _ hz) (by have := Rat.mul_nonneg hK hR; grind only)

theorem derivative_bound (z : Scalar) (hz : Centered.domain p R z) :
    Small ((holomorphic p c hc C K R hC hK hR hb hl).derivative z hz).val (4*(C*K)) := by
  change Small (BoundedSeries.sumDerivative c (Centered.offset p z).val hc (Centered.offset p z).property C K R) (4*(C*K))
  apply ScalarSeries.value_bound _ _ (C*K) (4*K*R) (Rat.mul_nonneg hC hK)
    (Rat.mul_nonneg (Rat.mul_nonneg (by decide) hK) hR)
    (by have := Rat.mul_nonneg hK hR; grind only)
  intro k
  simpa only [Rat.mul_assoc] using BoundedSeries.derivativeTerm_majorant c (Centered.offset p z).val
    hc (Centered.offset p z).property C K R hC hK hR hb (interior_bound R _ hz) k

theorem uniform_remainder (eps H : QPos) (w z : Scalar)
    (hw : Centered.domain p R w) (hz : Centered.domain p R z)
    (hH : H.val ≤ (derivativeDelta C K hC hK eps).val) (hzw : Small (sub z.val w.val) H.val) :
    Small (remainder (function p c hc C K R hC hK hR hb hl) w hw
      ((holomorphic p c hc C K R hC hK hR hb hl).derivative w hw) z hz) (eps.val*H.val) :=
  ((holomorphic p c hc C K R hC hK hR hb hl).atPoint w hw).estimate eps H z hz hH hzw

theorem value_agrees (q : Scalar) (d : Nat → ComplexRaw) (hd : ∀ k, (d k).Valid)
    (D L S : Rat) (hD : 0 ≤ D) (hL : 0 ≤ L) (hS : 0 ≤ S)
    (hdb : ∀ k, Small (d k) (D*L^k)) (hls : 8*L*S ≤ (1 : Rat)/2)
    (hpq : p≈q) (hcd : ∀ k, (c k).Equiv (d k)) (z w : Scalar)
    (hz : Centered.domain p R z) (hw : Centered.domain q S w) (hzw : z≈w) :
    (function p c hc C K R hC hK hR hb hl).eval z hz ≈
      (function q d hd D L S hD hL hS hdb hls).eval w hw :=
  BoundedSeries.seriesMap_congr c d hc hd hcd C K R D L S hC hK hR hD hL hS hb hdb hl hls
    (Centered.offset p z) (Centered.offset q w) hz hw (Centered.offset_congr p q z w hpq hzw)

theorem derivative_agrees (q : Scalar) (d : Nat → ComplexRaw) (hd : ∀ k, (d k).Valid)
    (D L S : Rat) (hD : 0 ≤ D) (hL : 0 ≤ L) (hS : 0 ≤ S)
    (hdb : ∀ k, Small (d k) (D*L^k)) (hls : 8*L*S ≤ (1 : Rat)/2)
    (hpq : p≈q) (hcd : ∀ k, (c k).Equiv (d k)) (z w : Scalar)
    (hz : Centered.domain p R z) (hw : Centered.domain q S w) (hzw : z≈w) :
    (holomorphic p c hc C K R hC hK hR hb hl).derivative z hz ≈
      (holomorphic q d hd D L S hD hL hS hdb hls).derivative w hw :=
  BoundedSeries.sumDerivative_congr_of_bounds c d (Centered.offset p z).val (Centered.offset q w).val
    hc hd (Centered.offset p z).property (Centered.offset q w).property hcd
    (Centered.offset_congr p q z w hpq hzw) C K R D L S hC hK hR hD hL hS hb hdb
    (interior_bound R _ hz) (interior_bound S _ hw)
    (by have := Rat.mul_nonneg hK hR; grind only) (by have := Rat.mul_nonneg hL hS; grind only)

end ComputableAnalysis.RiemannHilbert.CenteredSeries
