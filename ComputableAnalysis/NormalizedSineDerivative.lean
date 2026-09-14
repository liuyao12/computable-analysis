import ComputableAnalysis.GeometricSineDerivative

/-!
# The normalized geometric sine derivative

This statement uses the existing `sinPiRawOfArctan`, `cosPiRawOfArctan`, and
`piCircleArea` computations verbatim. The inverse data B is exactly the data
required by those definitions, not a differentiability assumption.
-/

namespace ComputableAnalysis
namespace GeometricSineDerivative

open ArctanGeometry IntegralIdentities SinPiIntegral
open GeometricRotationODE GeometricSineSecant

private theorem pi_initial_box :
    piCircleArea.compute 0 = ({lo := 2, hi := 4} : QInterval) := by
  decide +kernel

private theorem pi_output_bounds (n : Nat) {p : Rat}
    (hp0 : (piCircleArea.compute n).lo <= p)
    (hp1 : p <= (piCircleArea.compute n).hi) : 0 <= p ∧ p <= 4 := by
  have hn := CauchyPi.piCircleArea_valid.2.1 0 n (Nat.zero_le n)
  rw [pi_initial_box] at hn
  dsimp only at hn
  constructor <;> grind

private theorem sine_output_error
    (B : ArctanInverseBisection) (x : Rat) (hx : OnHalf x) (n : Nat)
    {a : Rat} (ha0 : ((sinPiRawOfArctan B x hx).compute n).lo <= a)
    (ha1 : a <= ((sinPiRawOfArctan B x hx).compute n).hi) :
    qabs (a-pointIm ((slope B x hx).compute n).lo) <=
      2*((slope B x hx).compute n).width := by
  have hw := (rationalCircleSinInterval_width_le (slope_unit B x hx n)).2
  change pointIm ((slope B x hx).compute n).lo <= a at ha0
  change a <= pointIm ((slope B x hx).compute n).hi at ha1
  change pointIm ((slope B x hx).compute n).hi -
    pointIm ((slope B x hx).compute n).lo <= _ at hw
  apply qabs_le_of_neg_le_le <;> grind

private theorem cosine_output_error
    (B : ArctanInverseBisection) (x : Rat) (hx : OnHalf x) (n : Nat)
    {c : Rat} (hc0 : ((cosPiRawOfArctan B x hx).compute n).lo <= c)
    (hc1 : c <= ((cosPiRawOfArctan B x hx).compute n).hi) :
    qabs (c-pointRe ((slope B x hx).compute n).lo) <=
      4*((slope B x hx).compute n).width := by
  have hw := (rationalCircleCosInterval_width_le (slope_unit B x hx n)).2
  change pointRe ((slope B x hx).compute n).hi <= c at hc0
  change c <= pointRe ((slope B x hx).compute n).lo at hc1
  change pointRe ((slope B x hx).compute n).lo -
    pointRe ((slope B x hx).compute n).hi <= _ at hw
  apply qabs_le_of_neg_le_le <;> grind

private theorem scaled_step_bound {p h : Rat} (hp0 : 0 <= p) (hp1 : p <= 4) :
    qabs ((h/2)*p) <= 2*qabs h := by
  have hi : qabs ((2 : Rat)⁻¹) = (1 : Rat)/2 := by decide +kernel
  have hm := Rat.mul_le_mul_of_nonneg_left hp1 (qabs_nonneg h)
  simp only [Rat.div_def, qabs_mul, hi, qabs_eq_self_of_nonneg hp0]
  simp only [Rat.div_def] at *
  grind

private theorem finite_normalized_residual
    {u v a b c p alpha beta h x e w : Rat}
    (hu0 : 0 <= u) (hu1 : u <= 1)
    (hp0 : 0 <= p) (hp1 : p <= 4)
    (hH : qabs h <= 1) (he : 0 <= e) (hesmall : e <= qabs h/16)
    (hw : w <= 2*e)
    (has : qabs (a-pointIm v) <= e)
    (hbs : qabs (b-pointIm u) <= e)
    (hcs : qabs (c-pointRe u) <= e)
    (ha : qabs (alpha-((x+h)/2)*p) <= e)
    (hb : qabs (beta-(x/2)*p) <= e)
    (hclock : qabs (v-u) <= 4*(qabs (alpha-beta)+w))
    (hsine : qabs (pointIm v-pointIm u-2*pointRe u*(alpha-beta)) <=
      20*qabs (v-u)*qabs (v-u)+2*w) :
    qabs (a-b-h*(p*c)) <= 1620*qabs h*qabs h+14*e := by
  have hangle : qabs ((alpha-beta)-(h/2)*p) <= 2*e := by
    have hid : (alpha-beta)-(h/2)*p =
        (alpha-((x+h)/2)*p)-(beta-(x/2)*p) := by
      simp only [Rat.div_def]
      grind
    have ht := qabs_sub_le (alpha-((x+h)/2)*p) (beta-(x/2)*p)
    rw [hid]
    grind
  have hanglesize : qabs (alpha-beta) <= 2*qabs h+2*e := by
    have ht := qabs_add_le ((alpha-beta)-(h/2)*p) ((h/2)*p)
    have hid : (alpha-beta)-(h/2)*p+(h/2)*p = alpha-beta := by grind
    rw [hid] at ht
    have hbnd := scaled_step_bound hp0 hp1 (h := h)
    grind
  have hd : qabs (v-u) <= 9*qabs h := by
    simp only [Rat.div_def] at hesmall
    grind
  have hd2 : qabs (v-u)*qabs (v-u) <= 81*qabs h*qabs h := by
    have hm1 := Rat.mul_le_mul_of_nonneg_right hd (qabs_nonneg (v-u))
    have hm2 := Rat.mul_le_mul_of_nonneg_left hd
      (Rat.mul_nonneg (by decide : (0 : Rat) <= 9) (qabs_nonneg h))
    grind
  have hco := cosine_coordinate_bounds hu0 hu1
  have hcabs : qabs (2*pointRe u) <= 2 := by
    rw [qabs_mul, qabs_eq_self_of_nonneg (by decide : (0 : Rat) <= 2),
      qabs_eq_self_of_nonneg hco.1]
    have hm := Rat.mul_le_mul_of_nonneg_left hco.2 (by decide : (0 : Rat) <= 2)
    simpa only [Rat.mul_one] using hm
  have hangleterm : qabs ((2*pointRe u)*((alpha-beta)-(h/2)*p)) <= 4*e := by
    rw [qabs_mul]
    have hm1 := Rat.mul_le_mul_of_nonneg_right hcabs
      (qabs_nonneg ((alpha-beta)-(h/2)*p))
    have hm2 := Rat.mul_le_mul_of_nonneg_left hangle (by decide : (0 : Rat) <= 2)
    grind
  have hcosineTerm : qabs (h*p*(c-pointRe u)) <= 4*e := by
    rw [qabs_mul, qabs_mul, qabs_eq_self_of_nonneg hp0]
    have hpH := Rat.mul_le_mul_of_nonneg_left hp1 (qabs_nonneg h)
    have hp4 : qabs h*p <= 4 := by grind
    have hm1 := Rat.mul_le_mul_of_nonneg_right hp4 (qabs_nonneg (c-pointRe u))
    have hm2 := Rat.mul_le_mul_of_nonneg_left hcs (by decide : (0 : Rat) <= 4)
    grind
  have hsource := qabs_sub_le (a-pointIm v) (b-pointIm u)
  have h12 := qabs_add_le ((a-pointIm v)-(b-pointIm u))
    (pointIm v-pointIm u-2*pointRe u*(alpha-beta))
  have h123 := qabs_add_le
    (((a-pointIm v)-(b-pointIm u)) +
      (pointIm v-pointIm u-2*pointRe u*(alpha-beta)))
    ((2*pointRe u)*((alpha-beta)-(h/2)*p))
  have h1234 := qabs_sub_le
    ((((a-pointIm v)-(b-pointIm u)) +
      (pointIm v-pointIm u-2*pointRe u*(alpha-beta))) +
      (2*pointRe u)*((alpha-beta)-(h/2)*p))
    (h*p*(c-pointRe u))
  have hid : a-b-h*(p*c) =
    ((((a-pointIm v)-(b-pointIm u)) +
      (pointIm v-pointIm u-2*pointRe u*(alpha-beta))) +
      (2*pointRe u)*((alpha-beta)-(h/2)*p)) - h*p*(c-pointRe u) := by
    simp only [Rat.div_def]
    grind
  rw [hid]
  grind

/-- The literal normalized derivative relation. Every rational selection
from every sufficiently late sine, cosine, and pi output obeys the residual
bound. In particular this covers all four corners of the pi-times-cosine
product interval, not just one chosen approximation. -/
def HasPiScaledDerivativeOnHalf (B : ArctanInverseBisection) : Prop :=
  ∀ eps : QPos, ∃ delta : QPos, ∀ x h : Rat,
    ∀ (hx : OnHalf x) (hxh : OnHalf (x+h)),
    h ≠ 0 -> qabs h <= delta.val ->
    ∃ N : Nat, ∀ n : Nat, N <= n -> ∀ a b c p : Rat,
      ((sinPiRawOfArctan B (x+h) hxh).compute n).lo <= a ->
      a <= ((sinPiRawOfArctan B (x+h) hxh).compute n).hi ->
      ((sinPiRawOfArctan B x hx).compute n).lo <= b ->
      b <= ((sinPiRawOfArctan B x hx).compute n).hi ->
      ((cosPiRawOfArctan B x hx).compute n).lo <= c ->
      c <= ((cosPiRawOfArctan B x hx).compute n).hi ->
      (piCircleArea.compute n).lo <= p -> p <= (piCircleArea.compute n).hi ->
      qabs (a-b-h*(p*c)) <= eps.val*qabs h

/-- The existing geometric sine has derivative pi times the existing
geometric cosine, throughout its first-quadrant rational chart. -/
theorem sinPi'_eq_pi_cosPi (B : ArctanInverseBisection) :
    HasPiScaledDerivativeOnHalf B := by
  intro eps
  let delta : QPos :=
    { val := eps.val/4000
      property := by
        rw [Rat.div_def]
        exact Rat.mul_pos eps.property ((Rat.inv_pos).2 (by decide)) }
  refine ⟨delta, ?_⟩
  intro x h hx hxh hh hsmall
  have hHpos : 0 < qabs h := qabs_pos_of_ne hh
  have hH0 := Rat.le_of_lt hHpos
  have hH1 : qabs h <= 1 := by
    apply qabs_le_of_neg_le_le
    all_goals
      have hx0 := hx.1
      have hx1 := hx.2
      have hy0 := hxh.1
      have hy1 := hxh.2
      simp only [Rat.div_def] at hx1 hy1
      grind
  let eta : QPos :=
    { val := min (qabs h/16) (eps.val*qabs h/64)
      property := by
        have h1 : 0 < qabs h/16 := by
          rw [Rat.div_def]
          exact Rat.mul_pos hHpos ((Rat.inv_pos).2 (by decide))
        have h2 : 0 < eps.val*qabs h/64 := by
          rw [Rat.div_def]
          exact Rat.mul_pos (Rat.mul_pos eps.property hHpos)
            ((Rat.inv_pos).2 (by decide))
        grind }
  have hetaH : eta.val <= qabs h/16 := by dsimp [eta]; grind
  have hetaE : eta.val <= eps.val*qabs h/64 := by dsimp [eta]; grind
  let etaSlope : QPos :=
    { val := eta.val/4
      property := by
        rw [Rat.div_def]
        exact Rat.mul_pos eta.property ((Rat.inv_pos).2 (by decide)) }
  obtain ⟨N0, hN0⟩ := slope_clock_close B x hx eta
  obtain ⟨N1, hN1⟩ := slope_clock_close B (x+h) hxh eta
  obtain ⟨M0, hM0⟩ := (slope_valid B x hx).2.2 etaSlope
  obtain ⟨M1, hM1⟩ := (slope_valid B (x+h) hxh).2.2 etaSlope
  let NA := 4*(eta.val.den+1)
  refine ⟨max NA (max N0 (max N1 (max M0 M1))), ?_⟩
  intro n hn a b c p ha0 ha1 hb0 hb1 hc0 hc1 hp0 hp1
  let U := (slope B x hx).compute n
  let V := (slope B (x+h) hxh).compute n
  let u := U.lo
  let v := V.lo
  have hU := slope_unit B x hx n
  have hV := slope_unit B (x+h) hxh n
  have hu : 0 <= u ∧ u <= 1 := ⟨hU.1, Rat.le_trans hU.2.1 hU.2.2⟩
  have hv : 0 <= v ∧ v <= 1 := ⟨hV.1, Rat.le_trans hV.2.1 hV.2.2⟩
  let A := arctanIntegralRectangleCompute v n
  let D := arctanIntegralRectangleCompute u n
  have hAo : A.lo <= A.hi :=
    RealRaw.interval_order_of_valid (arctanIntegralRectangleRaw v)
      (arctanIntegralRectangleRaw_valid hv.1 hv.2) n
  have hDo : D.lo <= D.hi :=
    RealRaw.interval_order_of_valid (arctanIntegralRectangleRaw u)
      (arctanIntegralRectangleRaw_valid hu.1 hu.2) n
  have hangle0 := hN0 n (by omega) u D.lo p (Rat.le_refl) hU.2.1
    (Rat.le_refl) hDo hp0 hp1
  have hangle1 := hN1 n (by omega) v A.lo p (Rat.le_refl) hV.2.1
    (Rat.le_refl) hAo hp0 hp1
  have hwU := hM0 n (by omega)
  have hwV := hM1 n (by omega)
  have hwA := arctanIntegralRectangleCompute_width_le_eps_of_precision
    hv.1 hv.2 eta n (by dsimp [NA] at hn; omega)
  have hwD := arctanIntegralRectangleCompute_width_le_eps_of_precision
    hu.1 hu.2 eta n (by dsimp [NA] at hn; omega)
  have hsource1 := sine_output_error B (x+h) hxh n ha0 ha1
  have hsource0 := sine_output_error B x hx n hb0 hb1
  have hcos := cosine_output_error B x hx n hc0 hc1
  have hs1 : qabs (a-pointIm v) <= eta.val := by
    dsimp [etaSlope] at hwV
    simp only [Rat.div_def] at hwV
    have he0 := Rat.le_of_lt eta.property
    grind
  have hs0 : qabs (b-pointIm u) <= eta.val := by
    dsimp [etaSlope] at hwU
    simp only [Rat.div_def] at hwU
    have he0 := Rat.le_of_lt eta.property
    grind
  have hcs : qabs (c-pointRe u) <= eta.val := by
    dsimp [etaSlope] at hwU
    simp only [Rat.div_def] at hwU
    grind
  have hclock := (clock_bounds hu.1 hu.2 hv.1 hv.2 n
    (Rat.le_refl : A.lo <= A.lo) hAo (Rat.le_refl : D.lo <= D.lo) hDo).2
  have hsine := sine_angle_residual hu.1 hu.2 hv.1 hv.2 n
    (Rat.le_refl : A.lo <= A.lo) hAo (Rat.le_refl : D.lo <= D.lo) hDo
  have hp := pi_output_bounds n hp0 hp1
  have hbound := finite_normalized_residual hu.1 hu.2 hp.1 hp.2 hH1
    (Rat.le_of_lt eta.property) hetaH (by grind : D.width+A.width <= 2*eta.val)
    hs1 hs0 hcs hangle1 hangle0 hclock hsine
  have hquad1 := Rat.mul_le_mul_of_nonneg_right hsmall hH0
  have hbudget : 1620*qabs h*qabs h+14*eta.val <= eps.val*qabs h := by
    change qabs h <= eps.val/4000 at hsmall
    have hquad := Rat.mul_le_mul_of_nonneg_right hsmall hH0
    have hnonneg := Rat.mul_nonneg (Rat.le_of_lt eps.property) hH0
    simp only [Rat.div_def] at hquad hetaE
    grind
  exact Rat.le_trans hbound hbudget

end GeometricSineDerivative
end ComputableAnalysis
