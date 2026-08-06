import ComputableAnalysis.Calculus
import ComputableAnalysis.RotationSeries

/-!
# Epsilon--delta continuity for the factorial rotation evaluator

The rotation series is evaluated at a common finite factorial prefix on the
bounded rational chart `[-2,2]`.  This module turns its already checked
finite input-Lipschitz estimate into the project's literal rational
epsilon--delta continuity predicate.  It deliberately stops short of a
derivative claim: proving `sin' = cos` still needs a finite *secant* estimate
which identifies the linear term of two nearby prefixes.  Those derivative
certificates now live in `ComputableAnalysis.RotationDerivative`, leaving
this module as the continuity layer they depend on.
-/

namespace ComputableAnalysis

namespace RotationSeries

/-- The real coordinate of the common-prefix factorial rotation evaluator,
restricted to the bounded rational chart `[-2,2]`. -/
def uniformRotationCosOnTwo : FunctionOnInterval where
  raw :=
    { definedAt := fun x => (-2 : Rat) <= x /\ x <= 2
      compute := fun x _ n =>
        (ComplexRaw.realPart (uniformRotationExpRaw x)).compute n }
  lower := -2
  upper := 2
  defined_on := fun _ hx => hx
  valid_on := by
    intro x hx
    have hx' : (-2 : Rat) <= x /\ x <= 2 := by
      simpa [inDomainInterval] using hx
    exact ComplexRaw.realPart_valid
      (uniformRotationExpRaw_valid x (qabs_le_of_neg_le_le hx'.1 hx'.2))

/-- The imaginary coordinate of the common-prefix factorial rotation
evaluator, restricted to the bounded rational chart `[-2,2]`. -/
def uniformRotationSinOnTwo : FunctionOnInterval where
  raw :=
    { definedAt := fun x => (-2 : Rat) <= x /\ x <= 2
      compute := fun x _ n =>
        (ComplexRaw.imagPart (uniformRotationExpRaw x)).compute n }
  lower := -2
  upper := 2
  defined_on := fun _ hx => hx
  valid_on := by
    intro x hx
    have hx' : (-2 : Rat) <= x /\ x <= 2 := by
      simpa [inDomainInterval] using hx
    exact ComplexRaw.imagPart_valid
      (uniformRotationExpRaw_valid x (qabs_le_of_neg_le_le hx'.1 hx'.2))

/-- The negative of the common-prefix sine coordinate on the same bounded
chart.  This is kept as an interval evaluator (rather than a notation for a
completed real) so it can be the derivative target in `cos' = -sin`. -/
def uniformRotationNegSinOnTwo : FunctionOnInterval where
  raw :=
    { definedAt := fun x => (-2 : Rat) <= x /\ x <= 2
      compute := fun x _ n =>
        (RealRaw.neg (ComplexRaw.imagPart (uniformRotationExpRaw x))).compute n }
  lower := -2
  upper := 2
  defined_on := fun _ hx => hx
  valid_on := by
    intro x hx
    have hx' : (-2 : Rat) <= x /\ x <= 2 := by
      simpa [inDomainInterval] using hx
    exact RealRaw.neg_valid (ComplexRaw.imagPart_valid
      (uniformRotationExpRaw_valid x (qabs_le_of_neg_le_le hx'.1 hx'.2)))

private theorem qabs_sub_comm (x y : Rat) : qabs (x - y) = qabs (y - x) := by
  have hneg : x - y = -(y - x) := by
    grind [Rat.sub_eq_add_neg]
  rw [hneg, qabs_neg]

private theorem coordinate_near_of_box_near
    {x y : Rat} {eps : QPos} {n : Nat}
    (hxy : QBox.NestedIn (uniformRotationBox x n)
      (QBox.expand (uniformRotationBox y n) eps.val))
    (hyx : QBox.NestedIn (uniformRotationBox y n)
      (QBox.expand (uniformRotationBox x n) eps.val))
    (hwidthX : (uniformRotationBox x n).width <= eps.val)
    (hwidthY : (uniformRotationBox y n).width <= eps.val) :
    QInterval.NearAt
      ((ComplexRaw.realPart (uniformRotationExpRaw x)).compute n)
      ((ComplexRaw.realPart (uniformRotationExpRaw y)).compute n) eps := by
  change
    (uniformRotationBox x n).lo.re <= (uniformRotationBox y n).hi.re + eps.val /\
      (uniformRotationBox y n).lo.re <= (uniformRotationBox x n).hi.re + eps.val /\
      (uniformRotationBox x n).width <= eps.val /\
      (uniformRotationBox y n).width <= eps.val
  unfold QBox.NestedIn QBox.expand at hxy hyx
  simp only [QComplex.le_def] at hxy hyx
  have horderedX : (uniformRotationBox x n).lo.re <=
      (uniformRotationBox x n).hi.re := by
    have hnonneg := uniformRotationBox_width_nonneg x n
    unfold QBox.width at hnonneg
    grind [Rat.sub_eq_add_neg]
  have horderedY : (uniformRotationBox y n).lo.re <=
      (uniformRotationBox y n).hi.re := by
    have hnonneg := uniformRotationBox_width_nonneg y n
    unfold QBox.width at hnonneg
    grind [Rat.sub_eq_add_neg]
  exact ⟨Rat.le_trans horderedX hxy.2.1, Rat.le_trans horderedY hyx.2.1,
    hwidthX, hwidthY⟩

private theorem coordinate_near_of_box_near_imaginary
    {x y : Rat} {eps : QPos} {n : Nat}
    (hxy : QBox.NestedIn (uniformRotationBox x n)
      (QBox.expand (uniformRotationBox y n) eps.val))
    (hyx : QBox.NestedIn (uniformRotationBox y n)
      (QBox.expand (uniformRotationBox x n) eps.val))
    (hheightX : (uniformRotationBox x n).height <= eps.val)
    (hheightY : (uniformRotationBox y n).height <= eps.val) :
    QInterval.NearAt
      ((ComplexRaw.imagPart (uniformRotationExpRaw x)).compute n)
      ((ComplexRaw.imagPart (uniformRotationExpRaw y)).compute n) eps := by
  change
    (uniformRotationBox x n).lo.im <= (uniformRotationBox y n).hi.im + eps.val /\
      (uniformRotationBox y n).lo.im <= (uniformRotationBox x n).hi.im + eps.val /\
      (uniformRotationBox x n).height <= eps.val /\
      (uniformRotationBox y n).height <= eps.val
  unfold QBox.NestedIn QBox.expand at hxy hyx
  simp only [QComplex.le_def] at hxy hyx
  have horderedX : (uniformRotationBox x n).lo.im <=
      (uniformRotationBox x n).hi.im := by
    have hnonneg := uniformRotationBox_height_nonneg x n
    unfold QBox.height at hnonneg
    grind [Rat.sub_eq_add_neg]
  have horderedY : (uniformRotationBox y n).lo.im <=
      (uniformRotationBox y n).hi.im := by
    have hnonneg := uniformRotationBox_height_nonneg y n
    unfold QBox.height at hnonneg
    grind [Rat.sub_eq_add_neg]
  exact ⟨Rat.le_trans horderedX hxy.2.2, Rat.le_trans horderedY hyx.2.2,
    hheightX, hheightY⟩

/-- The common-prefix cosine coordinate is continuous on `[-2,2]` in the
project's rational epsilon--delta sense.  For output tolerance `eps`, the
input tolerance is `eps / 16`; a common factorial stage makes both output
boxes at most `eps` wide.  No topology or real-number completeness is used. -/
theorem uniformRotationCosOnTwo_epsilonDeltaContinuous :
    EpsilonDeltaContinuousOn uniformRotationCosOnTwo := by
  intro eps
  let delta : QPos :=
    { val := eps.val / 16
      property := by
        rw [Rat.div_def]
        exact Rat.mul_pos eps.property ((Rat.inv_pos).2 (by native_decide)) }
  obtain ⟨n, hn⟩ := uniformRotationBoxes_widths_shrink_uniform eps
  refine ⟨delta, n, ?_⟩
  intro x y hx hy hclose
  have hx' : (-2 : Rat) <= x /\ x <= 2 := by
    simpa [uniformRotationCosOnTwo, inDomainInterval] using hx
  have hy' : (-2 : Rat) <= y /\ y <= 2 := by
    simpa [uniformRotationCosOnTwo, inDomainInterval] using hy
  have hqabsX : qabs x <= 2 := qabs_le_of_neg_le_le hx'.1 hx'.2
  have hqabsY : qabs y <= 2 := qabs_le_of_neg_le_le hy'.1 hy'.2
  have hxyInput : qabs (x - y) <= delta.val := by
    rw [qabs_sub_comm]
    exact hclose
  have hyxInput : qabs (y - x) <= delta.val := hclose
  have hscale : 16 * delta.val = eps.val := by
    dsimp [delta]
    rw [Rat.div_def]
    have hcancel : (16 : Rat) * (16 : Rat)⁻¹ = 1 := by native_decide
    grind [Rat.mul_assoc, Rat.mul_comm]
  have hxy := uniformRotationBox_contained_expand_of_input_near
    x y delta.val hqabsX hqabsY n hxyInput
  have hyx := uniformRotationBox_contained_expand_of_input_near
    y x delta.val hqabsY hqabsX n hyxInput
  rw [hscale] at hxy hyx
  have hwidthX := (hn x n (Nat.le_refl n)).1
  have hwidthY := (hn y n (Nat.le_refl n)).1
  simpa [uniformRotationCosOnTwo] using
    coordinate_near_of_box_near hxy hyx hwidthX hwidthY

/-- The common-prefix sine coordinate is continuous on `[-2,2]` in the same
rational epsilon--delta sense.  Its modulus is shared with cosine because
the factorial rotation evaluator encloses both coordinates in one box. -/
theorem uniformRotationSinOnTwo_epsilonDeltaContinuous :
    EpsilonDeltaContinuousOn uniformRotationSinOnTwo := by
  intro eps
  let delta : QPos :=
    { val := eps.val / 16
      property := by
        rw [Rat.div_def]
        exact Rat.mul_pos eps.property ((Rat.inv_pos).2 (by native_decide)) }
  obtain ⟨n, hn⟩ := uniformRotationBoxes_widths_shrink_uniform eps
  refine ⟨delta, n, ?_⟩
  intro x y hx hy hclose
  have hx' : (-2 : Rat) <= x /\ x <= 2 := by
    simpa [uniformRotationSinOnTwo, inDomainInterval] using hx
  have hy' : (-2 : Rat) <= y /\ y <= 2 := by
    simpa [uniformRotationSinOnTwo, inDomainInterval] using hy
  have hqabsX : qabs x <= 2 := qabs_le_of_neg_le_le hx'.1 hx'.2
  have hqabsY : qabs y <= 2 := qabs_le_of_neg_le_le hy'.1 hy'.2
  have hxyInput : qabs (x - y) <= delta.val := by
    rw [qabs_sub_comm]
    exact hclose
  have hyxInput : qabs (y - x) <= delta.val := hclose
  have hscale : 16 * delta.val = eps.val := by
    dsimp [delta]
    rw [Rat.div_def]
    have hcancel : (16 : Rat) * (16 : Rat)⁻¹ = 1 := by native_decide
    grind [Rat.mul_assoc, Rat.mul_comm]
  have hxy := uniformRotationBox_contained_expand_of_input_near
    x y delta.val hqabsX hqabsY n hxyInput
  have hyx := uniformRotationBox_contained_expand_of_input_near
    y x delta.val hqabsY hqabsX n hyxInput
  rw [hscale] at hxy hyx
  have hheightX := (hn x n (Nat.le_refl n)).2
  have hheightY := (hn y n (Nat.le_refl n)).2
  simpa [uniformRotationSinOnTwo] using
    coordinate_near_of_box_near_imaginary hxy hyx hheightX hheightY

end RotationSeries

end ComputableAnalysis
