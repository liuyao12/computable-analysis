import ComputableAnalysis.ArctanGeometry
import ComputableAnalysis.GeometricRotationODE

/-!
# Finite clock estimates for geometric sine differentiation

All inputs and all selected interval endpoints are rational. The clock is
computed by the existing rectangle arctangent; no derivative theorem about
sine or inverse functions is assumed. Its tangent-increment identity reduces
the estimates to rational algebra and elementary rectangle bounds.
-/

namespace ComputableAnalysis
namespace GeometricSineSecant

open ArctanGeometry

private theorem inverse_bounds {d : Rat} (hd : 1 <= d) (hd2 : d <= 2) :
    (1 : Rat)/2 <= d⁻¹ ∧ d⁻¹ <= 1 := by
  have hp : 0 < d := by grind
  have hi : 0 <= d⁻¹ := Rat.le_of_lt ((Rat.inv_pos).2 hp)
  have hc := Rat.mul_inv_cancel d (Rat.ne_of_gt hp)
  have h1 := Rat.mul_le_mul_of_nonneg_right hd hi
  have h2 := Rat.mul_le_mul_of_nonneg_right hd2 hi
  simp only [Rat.one_mul, hc] at h1 h2
  constructor
  · simp only [Rat.div_def]
    grind
  · exact h1

theorem kernel_bounds {u : Rat} (hu0 : 0 <= u) (hu1 : u <= 1) :
    (1 : Rat)/2 <= integralKernel u ∧ integralKernel u <= 1 := by
  have hsq0 := Rat.mul_nonneg hu0 hu0
  have hsq1 := Rat.mul_le_mul_of_nonneg_left hu1 hu0
  simp only [Rat.mul_one] at hsq1
  have hi := inverse_bounds (d := 1+u*u) (by grind) (by grind)
  simpa only [integralKernel, Rat.div_def, Rat.one_mul] using hi

/-- The rational tangent increment differs from its linear term by at most
one squared input increment. -/
private theorem tangent_increment_bounds
    {u v : Rat} (hu0 : 0 <= u) (huv : u <= v) (hv1 : v <= 1) :
    let d := v-u
    let t := tangentChartIncrement u d
    0 <= t ∧ t <= d ∧ d/2 <= t ∧
      qabs (t - d*integralKernel u) <= d*d := by
  have hu1 : u <= 1 := Rat.le_trans huv hv1
  have hv0 : 0 <= v := Rat.le_trans hu0 huv
  have hd0 : 0 <= v-u := by grind
  have huv0 := Rat.mul_nonneg hu0 hv0
  have huv1 := Rat.mul_le_mul_of_nonneg_left hv1 hu0
  simp only [Rat.mul_one] at huv1
  have huu0 := Rat.mul_nonneg hu0 hu0
  have huu1 := Rat.mul_le_mul_of_nonneg_left hu1 hu0
  simp only [Rat.mul_one] at huu1
  have hiD := inverse_bounds (d := 1+u*v) (by grind) (by grind)
  have hiE := inverse_bounds (d := 1+u*u) (by grind) (by grind)
  have hpD : 0 < 1+u*v := by grind
  have hpE : 0 < 1+u*u := by grind
  have hcD := Rat.mul_inv_cancel (1+u*v) (Rat.ne_of_gt hpD)
  have hcE := Rat.mul_inv_cancel (1+u*u) (Rat.ne_of_gt hpE)
  have hD0 : 0 <= (1+u*v)⁻¹ := by grind
  have hE0 : 0 <= (1+u*u)⁻¹ := by grind
  have htEq : tangentChartIncrement u (v-u) = (v-u)*(1+u*v)⁻¹ := by
    unfold tangentChartIncrement
    simp only [Rat.div_def]
    congr 2
    grind
  have ht0 := Rat.mul_nonneg hd0 hD0
  have ht1 := Rat.mul_le_mul_of_nonneg_left hiD.2 hd0
  have ht2 := Rat.mul_le_mul_of_nonneg_left hiD.1 hd0
  have hfactor0 : 0 <= u*(1+u*v)⁻¹*(1+u*u)⁻¹ :=
    Rat.mul_nonneg (Rat.mul_nonneg hu0 hD0) hE0
  have hfactor1 : u*(1+u*v)⁻¹*(1+u*u)⁻¹ <= 1 := by
    have hfirst := Rat.mul_le_mul_of_nonneg_left hiD.2 hu0
    have hsecond := Rat.mul_le_mul_of_nonneg_right hfirst hE0
    have hthird := Rat.mul_le_mul_of_nonneg_left hiE.2 hu0
    simp only [Rat.mul_one] at hfirst hsecond hthird
    grind
  have herrEq : (v-u)*(1+u*v)⁻¹-(v-u)*integralKernel u =
      -((v-u)*(v-u)*(u*(1+u*v)⁻¹*(1+u*u)⁻¹)) := by
    unfold integralKernel
    simp only [Rat.div_def, Rat.one_mul]
    grind
  have hsquare0 := Rat.mul_nonneg hd0 hd0
  have herr0 := Rat.mul_nonneg hsquare0 hfactor0
  have herr1 := Rat.mul_le_mul_of_nonneg_left hfactor1 hsquare0
  dsimp only
  rw [htEq]
  refine ⟨ht0, ?_, ?_, ?_⟩
  · simpa only [Rat.mul_one] using ht1
  · simpa only [Rat.div_def, Rat.one_mul] using ht2
  · rw [herrEq, qabs_neg, qabs_eq_self_of_nonneg herr0]
    simpa only [Rat.mul_one] using herr1

theorem kernel_lipschitz {u v : Rat}
    (hu0 : 0 <= u) (hu1 : u <= 1) (hv0 : 0 <= v) (hv1 : v <= 1) :
    qabs (integralKernel v-integralKernel u) <= 2*qabs (v-u) := by
  have hu := kernel_bounds hu0 hu1
  have hv := kernel_bounds hv0 hv1
  have hku0 : 0 <= integralKernel u := by grind
  have hkv0 : 0 <= integralKernel v := by grind
  have hsum0 : 0 <= u+v := by grind
  have hsum2 : u+v <= 2 := by grind
  have hfactor0 : 0 <= (u+v)*integralKernel u*integralKernel v :=
    Rat.mul_nonneg (Rat.mul_nonneg hsum0 hku0) hkv0
  have hfactor2 : (u+v)*integralKernel u*integralKernel v <= 2 := by
    have h1 := Rat.mul_le_mul_of_nonneg_left hu.2 hsum0
    have h2 := Rat.mul_le_mul_of_nonneg_right h1 hkv0
    have h3 := Rat.mul_le_mul_of_nonneg_left hv.2 hsum0
    simp only [Rat.mul_one] at h1 h2 h3
    grind
  have hcu := Rat.mul_inv_cancel (1+u*u)
    (Rat.ne_of_gt (by have h := Rat.mul_nonneg hu0 hu0; grind : 0 < 1+u*u))
  have hcv := Rat.mul_inv_cancel (1+v*v)
    (Rat.ne_of_gt (by have h := Rat.mul_nonneg hv0 hv0; grind : 0 < 1+v*v))
  have heq : integralKernel v-integralKernel u =
      -(v-u)*((u+v)*integralKernel u*integralKernel v) := by
    unfold integralKernel
    simp only [Rat.div_def, Rat.one_mul]
    grind
  rw [heq, qabs_mul, qabs_neg, qabs_eq_self_of_nonneg hfactor0]
  have hm := Rat.mul_le_mul_of_nonneg_left hfactor2 (qabs_nonneg (v-u))
  simpa only [Rat.mul_comm] using hm

private theorem clock_forward_bounds
    {u v a b : Rat} (hu0 : 0 <= u) (huv : u < v) (hv1 : v <= 1)
    (n : Nat)
    (ha0 : (arctanIntegralRectangleCompute v n).lo <= a)
    (ha1 : a <= (arctanIntegralRectangleCompute v n).hi)
    (hb0 : (arctanIntegralRectangleCompute u n).lo <= b)
    (hb1 : b <= (arctanIntegralRectangleCompute u n).hi) :
    let d := v-u
    let w := (arctanIntegralRectangleCompute u n).width +
      (arctanIntegralRectangleCompute v n).width
    qabs (a-b-d*integralKernel u) <= 2*d*d+w ∧
      d <= 4*(qabs (a-b)+w) := by
  have hu1 : u <= 1 := by grind
  have hv0 : 0 <= v := by grind
  have hd0 : 0 <= v-u := by grind
  have hd1 : v-u <= 1 := by grind
  have hp : 0 < v-u := by grind
  have hcancel : u+(v-u) = v := by grind
  let d := v-u
  let t := tangentChartIncrement u d
  have ht := tangent_increment_bounds hu0 (Rat.le_of_lt huv) hv1
  change 0 <= t ∧ t <= d ∧ d/2 <= t ∧
    qabs (t-d*integralKernel u) <= d*d at ht
  have heq := arctanIntegralRectangleRaw_forward_difference_equiv_tangentChartIncrement
    hu0 hu1 hp (by simpa only [hcancel] using hv1)
  rw [hcancel] at heq
  have hover := (RealRaw.compareAt_overlap_iff _ _ n n).1 (heq n)
  change (arctanIntegralRectangleCompute v n).lo -
      (arctanIntegralRectangleCompute u n).hi <=
        (arctanIntegralRectangleCompute t n).hi ∧
    (arctanIntegralRectangleCompute t n).lo <=
      (arctanIntegralRectangleCompute v n).hi -
        (arctanIntegralRectangleCompute u n).lo at hover
  have htan := arctanIntegralRectangleCompute_tangent_box_contains ht.1 n
  unfold QInterval.ContainsInterval at htan
  have ht1 : t <= 1 := by grind
  have hk := kernel_bounds ht.1 ht1
  have hlower := arctanIntegralRectangleCompute_input_mul_kernel_le_lower ht.1 n
  have hh := Rat.mul_le_mul_of_nonneg_left hk.1 ht.1
  have hsq : t*t <= d*d := by
    exact Rat.le_trans (Rat.mul_le_mul_of_nonneg_right ht.2.1 ht.1)
      (Rat.mul_le_mul_of_nonneg_left ht.2.1 hd0)
  have hcube : t*t*t <= d*d := by
    have hm := Rat.mul_le_mul_of_nonneg_left ht1 (Rat.mul_nonneg ht.1 ht.1)
    simp only [Rat.mul_one] at hm
    exact Rat.le_trans hm hsq
  let w := (arctanIntegralRectangleCompute u n).width +
    (arctanIntegralRectangleCompute v n).width
  have habs : qabs (a-b-t) <= d*d+w := by
    apply qabs_le_of_neg_le_le
    all_goals
      dsimp [w]
      unfold QInterval.width
      grind
  have htriangle := qabs_add_le (a-b-t) (t-d*integralKernel u)
  have hid : a-b-d*integralKernel u = (a-b-t)+(t-d*integralKernel u) := by grind
  have hstretch : d <= 4*(qabs (a-b)+w) := by
    have hq := self_le_qabs (a-b)
    dsimp [w]
    unfold QInterval.width
    simp only [Rat.div_def] at ht hh
    grind
  change qabs (a-b-d*integralKernel u) <= 2*d*d+w ∧
    d <= 4*(qabs (a-b)+w)
  constructor
  · rw [hid]
    grind
  · exact hstretch

/-- Every selected finite clock difference has a quadratic residual.
There are no differentiability hypotheses in this theorem. -/
theorem clock_bounds
    {u v a b : Rat}
    (hu0 : 0 <= u) (hu1 : u <= 1) (hv0 : 0 <= v) (hv1 : v <= 1)
    (n : Nat)
    (ha0 : (arctanIntegralRectangleCompute v n).lo <= a)
    (ha1 : a <= (arctanIntegralRectangleCompute v n).hi)
    (hb0 : (arctanIntegralRectangleCompute u n).lo <= b)
    (hb1 : b <= (arctanIntegralRectangleCompute u n).hi) :
    let d := qabs (v-u)
    let w := (arctanIntegralRectangleCompute u n).width +
      (arctanIntegralRectangleCompute v n).width
    qabs (a-b-(v-u)*integralKernel u) <= 4*d*d+w ∧
      d <= 4*(qabs (a-b)+w) := by
  have hcases : u < v ∨ u = v ∨ v < u := by grind
  rcases hcases with huv | heq | hvu
  · have h := clock_forward_bounds hu0 huv hv1 n ha0 ha1 hb0 hb1
    have hd0 : 0 <= v-u := by grind
    have hsq0 := Rat.mul_nonneg hd0 hd0
    dsimp only
    rw [qabs_eq_self_of_nonneg hd0]
    constructor
    · have hh := h.1
      grind
    · exact h.2
  · subst v
    have ho := (arctanIntegralRectangleRaw_valid hu0 hu1).1 n
    change 0 <= (arctanIntegralRectangleCompute u n).width at ho
    have hab : qabs (a-b) <= (arctanIntegralRectangleCompute u n).width := by
      apply qabs_le_of_neg_le_le <;> unfold QInterval.width <;> grind
    simp only [Rat.sub_self, qabs_zero, Rat.zero_mul, Rat.sub_zero, Rat.zero_add]
    constructor
    · grind
    · have hnonneg := qabs_nonneg (a-b)
      grind
  · have h := clock_forward_bounds hv0 hvu hu1 n hb0 hb1 ha0 ha1
    have hk := kernel_lipschitz hu0 hu1 hv0 hv1
    have hd0 : 0 <= u-v := by grind
    have hflip : v-u = -(u-v) := by grind
    have hba : b-a = -(a-b) := by grind
    have habsflip : qabs (v-u) = u-v := by
      rw [hflip, qabs_neg, qabs_eq_self_of_nonneg hd0]
    rw [habsflip] at hk
    have hid : a-b-(v-u)*integralKernel u =
        -(b-a-(u-v)*integralKernel v) +
        (u-v)*(integralKernel u-integralKernel v) := by grind
    have hkflip : integralKernel u-integralKernel v =
        -(integralKernel v-integralKernel u) := by grind
    have htri := qabs_add_le (-(b-a-(u-v)*integralKernel v))
      ((u-v)*(integralKernel u-integralKernel v))
    rw [qabs_neg, qabs_mul, qabs_eq_self_of_nonneg hd0,
      hkflip, qabs_neg] at htri
    have hmul := Rat.mul_le_mul_of_nonneg_left hk hd0
    dsimp only
    rw [habsflip]
    constructor
    · rw [hid]
      have hh := h.1
      grind
    · have hs := h.2
      rw [hba, qabs_neg] at hs
      dsimp only at hs
      grind

end GeometricSineSecant
end ComputableAnalysis
