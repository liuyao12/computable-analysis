import ComputableAnalysis.RiemannHilbert.BoundaryCauchySequenceLimits
import ComputableAnalysis.RiemannHilbert.CoefficientSeriesComparison
import ComputableAnalysis.RiemannHilbert.ContourFixedRectangleNormalized

/-! The constructed coefficient-limit series agrees with the actual
boundary projections, quantitatively. Genuine interior Cauchy reconstruction
then identifies it with any justified shrinking limit of the actual sources. -/
namespace ComputableAnalysis.RiemannHilbert.BoundaryCauchySequenceAgreement
open ComplexRaw FunctionTheory DomainFunctions RectangularContour BoundaryCauchyPowers
open BoundaryCauchySequenceLimits
set_option autoImplicit false

variable (d : Nat → Data) (hJ : ∀ k, (d k).rectangle=(d 0).rectangle)
    (hc : ∀ k, (d k).center≈(d 0).center)
    (hU : ∀ k, (d k).reciprocalBound=(d 0).reciprocalBound)
    (hV : ∀ k, (d k).valueBound=(d 0).valueBound)
    (r : Nat → Rat) (hr : ShrinksToZero r) (hr0 : ∀ k, 0≤r k)
    (hsource : ∀ K L, K≤L → ∀ q, rationalRectangleBoundaryContains (d 0).rectangle q →
      ∀ hL hK, Small (sub ((d L).source.eval (rationalRectangleScalar q) hL).val
        ((d K).source.eval (rationalRectangleScalar q) hK).val) (r K))

def prefixSeries (K : Nat) : DomainFunctions.Map :=
  CenteredSeries.function (d 0).center (fun j => (moment (d K) j).val) (fun j => (moment (d K) j).property)
    (constant d*(d 0).valueBound.val) (rate (d 0)).val (BoundaryCauchyNear.radius (d 0)).val
    (Rat.mul_nonneg (constant_nonneg d) (Rat.le_of_lt (d 0).valueBound.property))
    (Rat.le_of_lt (rate (d 0)).property) (Rat.le_of_lt (BoundaryCauchyNear.radius (d 0)).property)
    (moments_bound d hJ hU hV · K) (BoundaryCauchySeries.budget (d 0))

include hU hc in
theorem prefix_domain (K : Nat) (z : Scalar)
    (hz : Centered.domain (d 0).center (BoundaryCauchyNear.radius (d 0)).val z) :
    (BoundaryCauchySeries.function (d K)).domain z := by
  change Centered.domain (d K).center (BoundaryCauchyNear.radius (d K)).val z
  have he : BoundaryCauchyNear.radius (d K)=BoundaryCauchyNear.radius (d 0) := by
    have hrate : rate (d K)=rate (d 0) := Subtype.ext (by
      change 2*(d K).reciprocalBound.val=2*(d 0).reciprocalBound.val
      rw [hU K])
    exact congrArg (fun R : QPos => divideRadius unitError
      ⟨16*R.val,Rat.mul_pos (by decide +kernel) R.property⟩) hrate
  rw [he]
  exact (Centered.domain_congr (d 0).center (d K).center z z _ (Setoid.symm (hc K)) (Setoid.refl z)).1 hz

theorem prefix_agreement (K : Nat) (z : Scalar)
    (hz : Centered.domain (d 0).center (BoundaryCauchyNear.radius (d 0)).val z) :
    (prefixSeries d hJ hU hV K).eval z hz≈(BoundaryCauchySeries.function (d K)).eval z (prefix_domain d hc hU K z hz) :=
  CenteredSeries.value_agrees (d 0).center _ _ _ _ _ _ _ _ _ _
    (d K).center (BoundaryCauchySeries.coefficients (d K)) (BoundaryCauchySeries.coefficients_valid (d K))
    (bound (d K)).val (rate (d K)).val (BoundaryCauchyNear.radius (d K)).val
    (Rat.le_of_lt (bound (d K)).property) (Rat.le_of_lt (rate (d K)).property)
    (Rat.le_of_lt (BoundaryCauchyNear.radius (d K)).property) (moment_bound (d K)) (BoundaryCauchySeries.budget (d K))
    (Setoid.symm (hc K)) (fun j => equiv_refl _ (moment (d K) j).property) z z hz
    (prefix_domain d hc hU K z hz) (Setoid.refl z)

theorem prefix_close (K : Nat) (z : Scalar)
    (hz : Centered.domain (d 0).center (BoundaryCauchyNear.radius (d 0)).val z) :
    Small (sub ((function d hJ hc hU hV r hr hr0 hsource).eval z hz).val
      ((prefixSeries d hJ hU hV K).eval z hz).val) (4*constant d*r K) := by
  have he : ∀ j, Small (sub (coefficient d r j) (moment (d K) j).val)
      ((constant d*r K)*(rate (d 0)).val^j) := by
    intro j
    have h := coefficient_close d hJ hc hU r hr0 hsource j K
    have eq : tail d r j K=(constant d*r K)*(rate (d 0)).val^j := by unfold tail BoundaryCauchyPowers.rate; grind only
    rw [eq] at h
    exact h
  have hlocal : 2*(rate (d 0)).val*(BoundaryCauchyNear.radius (d 0)).val≤(1:Rat)/2 := by
    have hb := BoundaryCauchySeries.budget (d 0)
    have hn := Rat.mul_nonneg (Rat.le_of_lt (rate (d 0)).property) (Rat.le_of_lt (BoundaryCauchyNear.radius (d 0)).property)
    grind only
  have hs := CoefficientSeriesComparison.value_difference (coefficient d r) (fun j => (moment (d K) j).val)
    (coefficient_valid d hJ hc hU r hr hr0 hsource) (fun j => (moment (d K) j).property)
    (Centered.offset (d 0).center z).val (Centered.offset (d 0).center z).property
    (constant d*(d 0).valueBound.val) (constant d*(d 0).valueBound.val)
    (rate (d 0)).val (BoundaryCauchyNear.radius (d 0)).val (constant d*r K)
    (Rat.mul_nonneg (constant_nonneg d) (Rat.le_of_lt (d 0).valueBound.property))
    (Rat.mul_nonneg (constant_nonneg d) (Rat.le_of_lt (d 0).valueBound.property))
    (Rat.le_of_lt (rate (d 0)).property) (Rat.le_of_lt (BoundaryCauchyNear.radius (d 0)).property)
    (Rat.mul_nonneg (constant_nonneg d) (hr0 K))
    (coefficient_bound d hJ hc hU hV r hr hr0 hsource) (moments_bound d hJ hU hV · K)
    he (LocalODE.interior_bound _ _ hz) hlocal
  have eq : 4*(constant d*r K)=4*constant d*r K := by grind only
  rw [eq] at hs
  exact hs

theorem projection_close (K : Nat) (z : Scalar)
    (hz : Centered.domain (d 0).center (BoundaryCauchyNear.radius (d 0)).val z) :
    Small (sub ((function d hJ hc hU hV r hr hr0 hsource).eval z hz).val
      ((BoundaryCauchySeries.function (d K)).eval z (prefix_domain d hc hU K z hz)).val)
      (4*constant d*r K) :=
  Small.congr
    (sub_valid ((function d hJ hc hU hV r hr hr0 hsource).eval z hz).property
      ((prefixSeries d hJ hU hV K).eval z hz).property)
    (sub_valid ((function d hJ hc hU hV r hr hr0 hsource).eval z hz).property
      ((BoundaryCauchySeries.function (d K)).eval z (prefix_domain d hc hU K z hz)).property)
    (FunctionTheory.sub_congr (equiv_refl _ ((function d hJ hc hU hV r hr hr0 hsource).eval z hz).property) (prefix_agreement d hJ hc hU hV K z hz))
    (prefix_close d hJ hc hU hV r hr hr0 hsource K z hz)

end ComputableAnalysis.RiemannHilbert.BoundaryCauchySequenceAgreement
