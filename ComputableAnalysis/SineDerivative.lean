import ComputableAnalysis.FixedScheduleSine
import ComputableAnalysis.RotationDerivative

/-!
# Sine differentiation, with a constructed derivative and literal endpoints

The factorial sine and cosine in this file use the rational radian coordinate.
No geometric normalized-angle identification is assumed.  In particular this
file does not silently rename the public geometric `sin (pi*x)` evaluator.

`HasEndpointDerivativeOn` quantifies over EVERY sufficiently small nonzero
rational increment, EVERY sufficiently late evaluation stage, and EVERY
rational selection from the three output intervals.  Its positive `QPos`
radius prevents a vacuous zero-neighborhood certificate.

The fixed-schedule derivative algorithm reads sine only.  We prove that it
satisfies this all-increment relation and is equivalent to the independently
specified factorial cosine.  There is no precision search in that algorithm.
-/

namespace ComputableAnalysis
namespace FixedSchedule

/-- Every sufficiently late residual interval is within `eps*|h|` of zero.
This definition mentions only rational numbers and finite interval outputs. -/
def HasEndpointDerivativeOn (f df : Rat -> RealRaw) (R : Rat) : Prop :=
  ∀ eps : QPos, ∃ delta : QPos, ∀ x h : Rat,
    qabs x <= R -> qabs (x+h) <= R -> h ≠ 0 -> qabs h <= delta.val ->
    ∃ N : Nat, ∀ n : Nat, N <= n -> ∀ a b c : Rat,
      ((f (x+h)).compute n).lo <= a ->
      a <= ((f (x+h)).compute n).hi ->
      ((f x).compute n).lo <= b -> b <= ((f x).compute n).hi ->
      ((df x).compute n).lo <= c -> c <= ((df x).compute n).hi ->
      qabs (a-b-h*c) <= eps.val * qabs h

private theorem around_point_error {a d r : Rat}
    (hl : d-r <= a) (hu : a <= d+r) : qabs (a-d) <= r := by
  apply qabs_le_of_neg_le_le <;> grind

/-- Passing from a finite center secant to arbitrary rational output points.
All cancellation takes place in the rational field, not between interval
objects or between unspecified completed real values. -/
private theorem residual_bound (a b c s1 s0 d r w h : Rat)
    (hh : h ≠ 0)
    (ha : qabs (a-s1) <= r) (hb : qabs (b-s0) <= r)
    (hc : qabs (c-d) <= w)
    (hs : qabs ((s1-s0)/h-d) <= qabs h * 34) :
    qabs (a-b-h*c) <= r+r+qabs h*(qabs h*34)+qabs h*w := by
  have hcancel : h * ((s1-s0)/h) = s1-s0 := by
    rw [Rat.div_def, Rat.mul_comm h ((s1-s0)*h⁻¹), Rat.mul_assoc,
      Rat.inv_mul_cancel h hh, Rat.mul_one]
  have hid : a-b-h*c =
      ((a-s1)-(b-s0)) + h*((s1-s0)/h-d) - h*(c-d) := by
    grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.mul_neg]
  have h1 := qabs_sub_le (a-s1) (b-s0)
  have h2 := qabs_add_le ((a-s1)-(b-s0)) (h*((s1-s0)/h-d))
  have h3 := qabs_sub_le
    (((a-s1)-(b-s0)) + h*((s1-s0)/h-d)) (h*(c-d))
  have h4 := Rat.mul_le_mul_of_nonneg_left hs (qabs_nonneg h)
  have h5 := Rat.mul_le_mul_of_nonneg_left hc (qabs_nonneg h)
  rw [qabs_mul] at h2
  rw [qabs_mul] at h3
  rw [hid]
  grind

private theorem radius_shrinks :
    ShrinksToZero RotationSeries.uniformRotationTailRadius := by
  apply shrinksToZero_of_natOverSuccBound (C := 1)
  intro n
  have hr := radius_le_step_sq n
  have hp := Rat.le_of_lt (step_pos n)
  have hm := Rat.mul_le_mul_of_nonneg_left (step_le_one n) hp
  have hcast : ((1 : Nat) : Rat) = (1 : Rat) := by decide +kernel
  simpa only [Rat.mul_one, step, hcast] using Rat.le_trans hr hm

private theorem residual_budget {eps H r w : Rat}
    (heps : 0 < eps) (hH : 0 <= H)
    (hsmall : H <= eps/68) (hr : r <= eps*H/16) (hw : w <= eps/4) :
    r+r+H*(H*34)+H*w <= eps*H := by
  have hstep : H*34 <= eps/2 := by
    have hm := Rat.mul_le_mul_of_nonneg_right hsmall
      (by decide : (0 : Rat) <= 34)
    have heq : eps/68*34 = eps/2 := by
      simp only [Rat.div_def]
      grind
    rw [heq] at hm
    exact hm
  have hquad := Rat.mul_le_mul_of_nonneg_left hstep hH
  have hwidth := Rat.mul_le_mul_of_nonneg_left hw hH
  have hnonneg := Rat.mul_nonneg (Rat.le_of_lt heps) hH
  simp only [Rat.div_def] at *
  grind

/-- General finite-center argument, instantiated below with fully checked
cosine and computed-derivative enclosures.  `w` is proof-side information:
it does not change the source evaluator or its fixed stage rule. -/
private theorem sine_endpoint_derivative_of_center_enclosure
    (df : Rat -> RealRaw) (R : Rat) (hR : R <= 2)
    (w : Nat -> Rat) (hw : ShrinksToZero w)
    (hencl : ∀ x : Rat, qabs x <= R -> ∀ (n : Nat) (c : Rat),
      ((df x).compute n).lo <= c -> c <= ((df x).compute n).hi ->
      qabs (c-(RotationSeries.uniformRotationCenter x n).re) <= w n) :
    HasEndpointDerivativeOn sine df R := by
  intro eps
  let delta : QPos :=
    { val := eps.val/68
      property := by
        rw [Rat.div_def]
        exact Rat.mul_pos eps.property ((Rat.inv_pos).2 (by decide)) }
  refine ⟨delta, ?_⟩
  intro x h hx hxh hh hsmall
  let eta : QPos :=
    { val := eps.val*qabs h/16
      property := by
        rw [Rat.div_def]
        exact Rat.mul_pos (Rat.mul_pos eps.property (qabs_pos_of_ne hh))
          ((Rat.inv_pos).2 (by decide)) }
  let theta : QPos :=
    { val := eps.val/4
      property := by
        rw [Rat.div_def]
        exact Rat.mul_pos eps.property ((Rat.inv_pos).2 (by decide)) }
  obtain ⟨Nr, hr⟩ := radius_shrinks eta
  obtain ⟨Nw, hw'⟩ := hw theta
  refine ⟨max Nr Nw, ?_⟩
  intro n hn a b c hal hau hbl hbu hcl hcu
  have hnr : Nr <= n := by omega
  have hnw : Nw <= n := by omega
  have ha : qabs (a-(RotationSeries.uniformRotationCenter (x+h) n).im) <=
      RotationSeries.uniformRotationTailRadius n := by
    exact around_point_error hal hau
  have hb : qabs (b-(RotationSeries.uniformRotationCenter x n).im) <=
      RotationSeries.uniformRotationTailRadius n := by
    exact around_point_error hbl hbu
  have hc := hencl x hx n c hcl hcu
  have hs := RotationSeries.uniformRotationSinCenter_secant_error_le_thirty_four
    hh (Rat.le_trans hx hR) (Rat.le_trans hxh hR) n
  have hbnd := residual_bound a b c
    (RotationSeries.uniformRotationCenter (x+h) n).im
    (RotationSeries.uniformRotationCenter x n).im
    (RotationSeries.uniformRotationCenter x n).re
    (RotationSeries.uniformRotationTailRadius n) (w n) h hh ha hb hc hs
  exact Rat.le_trans hbnd
    (residual_budget eps.property (qabs_nonneg h) hsmall (hr n hnr) (hw' n hnw))

/-- The factorial sine is differentiated by the independent factorial cosine
on the entire bounded chart, for all sufficiently small rational increments. -/
theorem sine_derivative_cosine : HasEndpointDerivativeOn sine cosine 2 := by
  apply sine_endpoint_derivative_of_center_enclosure cosine 2 (Rat.le_refl)
    RotationSeries.uniformRotationTailRadius radius_shrinks
  intro x _hx n c hl hu
  exact around_point_error hl hu

private theorem derivative_contains_cosine_center
    {x : Rat} (hx : qabs x <= 1) (n : Nat) :
    ((sineDerivative x).compute n).lo <=
      (RotationSeries.uniformRotationCenter x n).re ∧
    (RotationSeries.uniformRotationCenter x n).re <=
      ((sineDerivative x).compute n).hi := by
  have hc := prefix_contains (sineBracket x) (cosine x)
    (cosine_valid x (by grind)) (sineBracket_contains_cosine hx) n
  have hr : 0 <= RotationSeries.uniformRotationTailRadius n := by
    unfold RotationSeries.uniformRotationTailRadius
      RotationSeries.uniformRotationTailMagnitude
    exact Rat.mul_nonneg (by decide)
      (RationalMajorant.factorialTailTerm_nonneg (by decide) _)
  change (intersectPrefix (sineBracket x) n).lo <=
      (RotationSeries.uniformRotationCenter x n).re -
        RotationSeries.uniformRotationTailRadius n ∧
    (RotationSeries.uniformRotationCenter x n).re +
      RotationSeries.uniformRotationTailRadius n <=
        (intersectPrefix (sineBracket x) n).hi at hc
  change (intersectPrefix (sineBracket x) n).lo <= _ ∧
    _ <= (intersectPrefix (sineBracket x) n).hi
  constructor <;> grind

/-- The program constructed from fixed sine secants is a genuine derivative,
not merely a sequence of approximations having a familiar candidate limit. -/
theorem sine_derivative_computed :
    HasEndpointDerivativeOn sine sineDerivative 1 := by
  let w : Nat -> Rat := fun n => 204/((n+1 : Nat) : Rat)
  apply sine_endpoint_derivative_of_center_enclosure sineDerivative 1 (by decide) w
  · exact shrinksToZero_of_natOverSuccBound (C := 204) (fun _ => Rat.le_refl)
  · intro x hx n c hl hu
    have hm := derivative_contains_cosine_center hx n
    have hw := sineDerivative_width_le hx n
    unfold QInterval.width at hw
    apply qabs_le_of_neg_le_le <;> dsimp [w] <;> grind

/-- Constructive `sin' = cos`: the derivative is computed from sine alone,
valid, and cross-stage equivalent to the independently defined cosine. -/
theorem sin'_eq_cos :
    HasEndpointDerivativeOn sine sineDerivative 1 ∧
    (∀ x : Rat, qabs x <= 1 ->
      (sineDerivative x).Valid ∧ (sineDerivative x).Equiv (cosine x)) := by
  exact ⟨sine_derivative_computed,
    fun _ hx => ⟨sineDerivative_valid hx, sineDerivative_equiv_cosine hx⟩⟩

end FixedSchedule
end ComputableAnalysis
