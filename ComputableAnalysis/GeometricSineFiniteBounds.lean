import ComputableAnalysis.GeometricSineDerivative

/-!
# Finite geometric sine residual inequalities

This statement uses the existing `sinPiRawOfArctan`, `cosPiRawOfArctan`, and
`piCircleArea` computations verbatim. The inverse data B is exactly the data
required by those definitions, not a differentiability assumption.
-/

namespace ComputableAnalysis
namespace GeometricSineFiniteBounds

open ArctanGeometry IntegralIdentities SinPiIntegral
open GeometricRotationODE GeometricSineSecant GeometricSineDerivative

theorem pi_initial_box :
    piCircleArea.compute 0 = ({lo := 2, hi := 4} : QInterval) := by
  decide +kernel

theorem pi_output_bounds (n : Nat) {p : Rat}
    (hp0 : (piCircleArea.compute n).lo <= p)
    (hp1 : p <= (piCircleArea.compute n).hi) : 0 <= p ∧ p <= 4 := by
  have hn := CauchyPi.piCircleArea_valid.2.1 0 n (Nat.zero_le n)
  rw [pi_initial_box] at hn
  dsimp only at hn
  constructor <;> grind

theorem sine_output_error
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

theorem cosine_output_error
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

theorem scaled_step_bound {p h : Rat} (hp0 : 0 <= p) (hp1 : p <= 4) :
    qabs ((h/2)*p) <= 2*qabs h := by
  have hi : qabs ((2 : Rat)⁻¹) = (1 : Rat)/2 := by decide +kernel
  have hm := Rat.mul_le_mul_of_nonneg_left hp1 (qabs_nonneg h)
  simp only [Rat.div_def, qabs_mul, hi, qabs_eq_self_of_nonneg hp0]
  simp only [Rat.div_def] at *
  grind

theorem finite_normalized_residual
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


end GeometricSineFiniteBounds
end ComputableAnalysis
