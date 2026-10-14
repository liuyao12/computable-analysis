import ComputableAnalysis.RiemannHilbert.BoundaryCauchySourceComparison
import ComputableAnalysis.RiemannHilbert.BoundaryCauchyAgreement

/-! Constructed Cauchy coefficients of a genuine boundary Cauchy sequence.
Literal moment evaluators and quantitative source comparisons construct
valid represented coefficients and their holomorphic local series. -/
namespace ComputableAnalysis.RiemannHilbert.BoundaryCauchySequenceLimits
open ComplexRaw FunctionTheory DomainFunctions RectangularContour BoundaryCauchyPowers
set_option autoImplicit false
variable (d : Nat → Data)
    (hJ : ∀ k, (d k).rectangle=(d 0).rectangle)
    (hc : ∀ k, (d k).center≈(d 0).center)
    (hU : ∀ k, (d k).reciprocalBound=(d 0).reciprocalBound)
    (hV : ∀ k, (d k).valueBound=(d 0).valueBound)
    (r : Nat → Rat) (hr : ShrinksToZero r) (hr0 : ∀ k, 0≤r k)
    (hsource : ∀ K L, K≤L → ∀ q, rationalRectangleBoundaryContains (d 0).rectangle q →
      ∀ hL hK, Small (sub ((d L).source.eval (rationalRectangleScalar q) hL).val
        ((d K).source.eval (rationalRectangleScalar q) hK).val) (r K))

def constant : Rat := BoundaryCauchyHomogeneousEstimates.constant (d 0).rectangle (d 0).reciprocalBound.val

theorem constant_nonneg : 0≤constant d := BoundaryCauchyHomogeneousEstimates.constant_nonneg
  (d 0).rectangle (d 0).xOrder (d 0).yOrder _ (Rat.le_of_lt (d 0).reciprocalBound.property)

def tail (j K : Nat) : Rat := constant d*(2*(d 0).reciprocalBound.val)^j*r K

include hr0 in
theorem tail_nonneg (j K : Nat) : 0≤tail d r j K := Rat.mul_nonneg
  (Rat.mul_nonneg (constant_nonneg d) (Rat.pow_nonneg (Rat.mul_nonneg (by decide +kernel)
    (Rat.le_of_lt (d 0).reciprocalBound.property)))) (hr0 K)

include hr in
theorem tail_shrinks (j : Nat) : ShrinksToZero (tail d r j) :=
  SeriesLimitLaws.shrinks_scale r hr (constant d*(2*(d 0).reciprocalBound.val)^j)
    (Rat.mul_nonneg (constant_nonneg d) (Rat.pow_nonneg (Rat.mul_nonneg (by decide +kernel)
      (Rat.le_of_lt (d 0).reciprocalBound.property))))

include hJ hc hU hr0 hsource in
theorem moments_future (j K L : Nat) (hKL : K≤L) :
    Small (sub (moment (d L) j).val (moment (d K) j).val) (tail d r j K) := by
  have h := BoundaryCauchySourceComparison.moment_difference (d L) (d K)
    ((hJ L).trans (hJ K).symm) (Setoid.trans (hc L) (Setoid.symm (hc K)))
    (r K) (hr0 K) (fun q hq => hsource K L hKL q ((hJ L) ▸ hq)) j
  rw [hJ L,hU L] at h
  change Small _ (constant d*r K*(2*(d 0).reciprocalBound.val)^j) at h
  have he : constant d*r K*(2*(d 0).reciprocalBound.val)^j=tail d r j K := by unfold tail; grind only
  rw [he] at h
  exact h

def coefficient (j : Nat) : ComplexRaw := RepresentedCauchySum.value
  (fun K => (moment (d K) j).val) (fun K => (moment (d K) j).property) (tail d r j)

include hJ hc hU hr hr0 hsource in
theorem coefficient_valid (j : Nat) : (coefficient d r j).Valid :=
  RepresentedCauchySum.value_valid _ _ _ (tail_shrinks d r hr j) (moments_future d hJ hc hU r hr0 hsource j)

include hJ hc hU hr0 hsource in
theorem coefficient_close (j K : Nat) :
    Small (sub (coefficient d r j) (moment (d K) j).val) (tail d r j K) :=
  RepresentedCauchySum.value_close_prefix _ _ _ (moments_future d hJ hc hU r hr0 hsource j) K

include hJ hU hV in
theorem moments_bound (j K : Nat) :
    Small (moment (d K) j).val ((constant d*(d 0).valueBound.val)*(2*(d 0).reciprocalBound.val)^j) := by
  have h := BoundaryCauchyHomogeneousEstimates.moment_bound (d K) j
  rw [hJ K,hU K,hV K] at h
  exact h

include hJ hc hU hV hr hr0 hsource in
theorem coefficient_bound (j : Nat) :
    Small (coefficient d r j) ((constant d*(d 0).valueBound.val)*(2*(d 0).reciprocalBound.val)^j) :=
  SeriesLimitLaws.small_of_prefix_bound _ (coefficient_valid d hJ hc hU r hr hr0 hsource j)
    (fun K => (moment (d K) j).val) (fun K => (moment (d K) j).property)
    _ (tail d r j) (tail_shrinks d r hr j)
    (coefficient_close d hJ hc hU r hr0 hsource j) (moments_bound d hJ hU hV j)

include hJ hc hU hr hr0 hsource in
/-- The actual coefficient limits agree under changed derivative bounds,
value bounds, reciprocal bounds and shrinking schedules, provided the actual
boundary sources, rectangles and represented centers agree. -/
theorem coefficient_congr (t : Nat → Data)
    (htJ : ∀ K, (t K).rectangle=(t 0).rectangle)
    (htc : ∀ K, (t K).center≈(t 0).center)
    (htU : ∀ K, (t K).reciprocalBound=(t 0).reciprocalBound)
    (s : Nat → Rat) (hs : ShrinksToZero s) (hs0 : ∀ K, 0≤s K)
    (htsource : ∀ K L, K≤L → ∀ q, rationalRectangleBoundaryContains (t 0).rectangle q →
      ∀ hL hK, Small (sub ((t L).source.eval (rationalRectangleScalar q) hL).val
        ((t K).source.eval (rationalRectangleScalar q) hK).val) (s K))
    (rectangles : ∀ K, (d K).rectangle=(t K).rectangle)
    (centers : ∀ K, (d K).center≈(t K).center)
    (sources : ∀ K z hd ht, (d K).source.eval z hd≈(t K).source.eval z ht)
    (j : Nat) : (coefficient d r j).Equiv (coefficient t s j) :=
  RepresentedCauchySum.value_congr _ _ (fun K => (moment (d K) j).property)
    (fun K => (moment (t K) j).property) (tail d r j) (tail t s j)
    (tail_shrinks d r hr j) (tail_shrinks t s hs j)
    (tail_nonneg d r hr0 j) (tail_nonneg t s hs0 j)
    (moments_future d hJ hc hU r hr0 hsource j)
    (moments_future t htJ htc htU s hs0 htsource j)
    (fun K => BoundaryCauchyAgreement.moment_agreement (d K) (t K) (rectangles K) (centers K) (sources K) j)

def function : DomainFunctions.Map := CenteredSeries.function (d 0).center
  (coefficient d r) (coefficient_valid d hJ hc hU r hr hr0 hsource)
  (constant d*(d 0).valueBound.val) (rate (d 0)).val (BoundaryCauchyNear.radius (d 0)).val
  (Rat.mul_nonneg (constant_nonneg d) (Rat.le_of_lt (d 0).valueBound.property))
  (Rat.le_of_lt (rate (d 0)).property) (Rat.le_of_lt (BoundaryCauchyNear.radius (d 0)).property)
  (coefficient_bound d hJ hc hU hV r hr hr0 hsource)
  (BoundaryCauchySeries.budget (d 0))

def holomorphic : Holomorphic (function d hJ hc hU hV r hr hr0 hsource) :=
  CenteredSeries.holomorphic (d 0).center (coefficient d r)
    (coefficient_valid d hJ hc hU r hr hr0 hsource)
    (constant d*(d 0).valueBound.val) (rate (d 0)).val (BoundaryCauchyNear.radius (d 0)).val
    (Rat.mul_nonneg (constant_nonneg d) (Rat.le_of_lt (d 0).valueBound.property))
    (Rat.le_of_lt (rate (d 0)).property) (Rat.le_of_lt (BoundaryCauchyNear.radius (d 0)).property)
    (coefficient_bound d hJ hc hU hV r hr hr0 hsource) (BoundaryCauchySeries.budget (d 0))

theorem center_value : (function d hJ hc hU hV r hr hr0 hsource).eval (d 0).center
    (Centered.center_mem _ _) ≈ ⟨coefficient d r 0,coefficient_valid d hJ hc hU r hr hr0 hsource 0⟩ :=
  CenteredSeries.initial _ _ _ _ _ _ _ _ _ _ _ _

theorem center_derivative : (holomorphic d hJ hc hU hV r hr hr0 hsource).derivative (d 0).center
    (Centered.center_mem _ _) ≈ ⟨coefficient d r 1,coefficient_valid d hJ hc hU r hr hr0 hsource 1⟩ :=
  CenteredSeries.derivative_initial _ _ _ _ _ _ _ _ _ _ _ _

end ComputableAnalysis.RiemannHilbert.BoundaryCauchySequenceLimits
