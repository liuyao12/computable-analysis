import ComputableAnalysis.GeometricSineDerivative
import ComputableAnalysis.MonotonicityConvexity
import ComputableAnalysis.CosineIntegralData
import ComputableAnalysis.ConcaveSecantFTC

namespace ComputableAnalysis
namespace GeometricSineConcavity
open ArctanGeometry GeometricRotationODE GeometricSineSecant
open IntegralIdentities SinPiIntegral GeometricSineDerivative

private theorem rat_square_nonneg (x : Rat) : 0 <= x*x :=
  RationalCircle.Stage.ratSquare_nonneg x

/-- A rational-circle chord is between its two tangent angular slopes.
This is polynomial/rational algebra, before introducing any derivative. -/
theorem chord_tangent_bounds {u v : Rat}
    (hu0 : 0 <= u) (huv : u <= v) (hv1 : v <= 1) :
    let t := (v-u)/(1+u*v)
    2*pointRe v*t <= pointIm v-pointIm u ∧
      pointIm v-pointIm u <= 2*pointRe u*(t*integralKernel t) := by
  have hv0 : 0 <= v := by grind
  have hu1 : u <= 1 := by grind
  have hu2 := rat_square_nonneg u
  have hv2 := rat_square_nonneg v
  have huv0 := Rat.mul_nonneg hu0 hv0
  have hdu : 0 < 1+u*u := by grind
  have hdv : 0 < 1+v*v := by grind
  have hduv : 0 < 1+u*v := by grind
  have iu0 := Rat.le_of_lt ((Rat.inv_pos).2 hdu)
  have iv0 := Rat.le_of_lt ((Rat.inv_pos).2 hdv)
  have iuv0 := Rat.le_of_lt ((Rat.inv_pos).2 hduv)
  have cu := Rat.mul_inv_cancel (1+u*u) (Rat.ne_of_gt hdu)
  have cv := Rat.mul_inv_cancel (1+v*v) (Rat.ne_of_gt hdv)
  have cuv := Rat.mul_inv_cancel (1+u*v) (Rat.ne_of_gt hduv)
  let t := (v-u)/(1+u*v)
  have ht2 := rat_square_nonneg t
  have hdt : 0 < 1+t*t := by grind
  have ct := Rat.mul_inv_cancel (1+t*t) (Rat.ne_of_gt hdt)
  have hleft : pointIm v-pointIm u-2*pointRe v*t =
      2*(v-u)*(v-u)*(u+v)*(1+u*u)⁻¹*(1+v*v)⁻¹*(1+u*v)⁻¹ := by
    dsimp [pointIm, pointRe, RationalCircle.Stage.point, t]
    simp only [Rat.div_def]
    grind
  have hright : 2*pointRe u*(t*integralKernel t)-(pointIm v-pointIm u) =
      4*u*(v-u)*(v-u)*(1+u*u)⁻¹*(1+u*u)⁻¹*(1+v*v)⁻¹ := by
    dsimp [pointIm, pointRe, RationalCircle.Stage.point, integralKernel, t] at *
    simp only [Rat.div_def, Rat.one_mul] at *
    grind
  have hl0 : 0 <= 2*(v-u)*(v-u)*(u+v)*(1+u*u)⁻¹*(1+v*v)⁻¹*(1+u*v)⁻¹ := by
    have hh := rat_square_nonneg (v-u)
    have hsum : 0 <= u+v := by grind
    have hp := Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg
      (Rat.mul_nonneg (Rat.mul_nonneg (by decide : (0 : Rat) <= 2) hh) hsum) iu0) iv0) iuv0
    simpa only [Rat.mul_assoc] using hp
  have hr0 : 0 <= 4*u*(v-u)*(v-u)*(1+u*u)⁻¹*(1+u*u)⁻¹*(1+v*v)⁻¹ := by
    have hh := rat_square_nonneg (v-u)
    have hp := Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg
      (Rat.mul_nonneg (Rat.mul_nonneg (by decide : (0 : Rat) <= 4) hu0) hh) iu0) iu0) iv0
    simpa only [Rat.mul_assoc] using hp
  dsimp only
  change 2*pointRe v*t <= _ ∧ _ <= 2*pointRe u*(t*integralKernel t)
  constructor <;> grind

/-- Finite clock outputs turn the chord inequality into angular supporting
lines. The only error is the explicitly displayed sum of clock widths. -/
theorem clock_support_sorted {u v alpha beta : Rat}
    (hu0 : 0 <= u) (huv : u <= v) (hv1 : v <= 1) (n : Nat)
    (ha0 : (arctanIntegralRectangleCompute v n).lo <= alpha)
    (ha1 : alpha <= (arctanIntegralRectangleCompute v n).hi)
    (hb0 : (arctanIntegralRectangleCompute u n).lo <= beta)
    (hb1 : beta <= (arctanIntegralRectangleCompute u n).hi) :
    let w := (arctanIntegralRectangleCompute u n).width +
      (arctanIntegralRectangleCompute v n).width
    2*pointRe v*(alpha-beta) <= pointIm v-pointIm u+2*w ∧
      pointIm v-pointIm u <= 2*pointRe u*(alpha-beta)+2*w := by
  have hu1 : u <= 1 := by grind
  have hv0 : 0 <= v := by grind
  have hCu := cosine_coordinate_bounds hu0 hu1
  have hCv := cosine_coordinate_bounds hv0 hv1
  have hCu0 : 0 <= 2*pointRe u := Rat.mul_nonneg (by decide) hCu.1
  have hCv0 : 0 <= 2*pointRe v := Rat.mul_nonneg (by decide) hCv.1
  have hCu2 : 2*pointRe u <= 2 := by grind
  have hCv2 : 2*pointRe v <= 2 := by grind
  let w := (arctanIntegralRectangleCompute u n).width +
    (arctanIntegralRectangleCompute v n).width
  have w0 : 0 <= w := by
    have h1 := (arctanIntegralRectangleRaw_valid hu0 hu1).1 n
    have h2 := (arctanIntegralRectangleRaw_valid hv0 hv1).1 n
    change 0 <= (arctanIntegralRectangleCompute u n).width at h1
    change 0 <= (arctanIntegralRectangleCompute v n).width at h2
    dsimp [w]; grind
  by_cases huvEq : u = v
  · subst v
    have hdiff : qabs (alpha-beta) <= w := by
      apply qabs_le_of_neg_le_le <;> dsimp [w] <;> unfold QInterval.width <;> grind
    have h1 := Rat.mul_le_mul_of_nonneg_left (self_le_qabs (alpha-beta)) hCu0
    have h2 := Rat.mul_le_mul_of_nonneg_left (neg_qabs_le_self (alpha-beta)) hCu0
    have h3 := Rat.mul_le_mul_of_nonneg_left hdiff hCu0
    have h4 := Rat.mul_le_mul_of_nonneg_right hCu2 w0
    dsimp only
    change _ <= _+2*w ∧ _ <= _+2*w
    constructor <;> grind
  · have hp : 0 < v-u := by grind
    have hcancel : u+(v-u) = v := by grind
    let t := tangentChartIncrement u (v-u)
    have ht0 : 0 <= t := Rat.le_of_lt (tangentChartIncrement_pos hu0 hp)
    have he := arctanIntegralRectangleRaw_forward_difference_equiv_tangentChartIncrement
      hu0 hu1 hp (by rw [hcancel]; exact hv1)
    rw [hcancel] at he
    have ho := (RealRaw.compareAt_overlap_iff _ _ n n).1 (he n)
    change (arctanIntegralRectangleCompute v n).lo -
        (arctanIntegralRectangleCompute u n).hi <=
        (arctanIntegralRectangleCompute t n).hi ∧
      (arctanIntegralRectangleCompute t n).lo <=
        (arctanIntegralRectangleCompute v n).hi -
        (arctanIntegralRectangleCompute u n).lo at ho
    have hlo := arctanIntegralRectangleCompute_input_mul_kernel_le_lower ht0 n
    have hhi := arctanIntegralRectangleCompute_upper_le_input ht0 n
    have hal : t*integralKernel t-w <= alpha-beta := by
      dsimp [w]; unfold QInterval.width; grind
    have hau : alpha-beta <= t+w := by
      dsimp [w]; unfold QInterval.width; grind
    have htEq : t = (v-u)/(1+u*v) := by
      dsimp [t, tangentChartIncrement]
      congr 1
      grind
    have hc := chord_tangent_bounds hu0 huv hv1
    dsimp only at hc
    rw [← htEq] at hc
    have hmullo := Rat.mul_le_mul_of_nonneg_left hal hCu0
    have hmulhi := Rat.mul_le_mul_of_nonneg_left hau hCv0
    have hwCu := Rat.mul_le_mul_of_nonneg_right hCu2 w0
    have hwCv := Rat.mul_le_mul_of_nonneg_right hCv2 w0
    dsimp only
    change _ <= _+2*w ∧ _ <= _+2*w
    constructor <;> grind

/-- Supporting-line inequalities hold on either side of the base point.
No ordering assumption on the approximating inverse slopes is needed. -/
theorem clock_support {u v alpha beta : Rat}
    (hu0 : 0 <= u) (hu1 : u <= 1) (hv0 : 0 <= v) (hv1 : v <= 1) (n : Nat)
    (ha0 : (arctanIntegralRectangleCompute v n).lo <= alpha)
    (ha1 : alpha <= (arctanIntegralRectangleCompute v n).hi)
    (hb0 : (arctanIntegralRectangleCompute u n).lo <= beta)
    (hb1 : beta <= (arctanIntegralRectangleCompute u n).hi) :
    let w := (arctanIntegralRectangleCompute u n).width +
      (arctanIntegralRectangleCompute v n).width
    2*pointRe v*(alpha-beta) <= pointIm v-pointIm u+2*w ∧
      pointIm v-pointIm u <= 2*pointRe u*(alpha-beta)+2*w := by
  by_cases huv : u <= v
  · exact clock_support_sorted hu0 huv hv1 n ha0 ha1 hb0 hb1
  · have h := clock_support_sorted hv0 (by grind : v <= u) hu1 n hb0 hb1 ha0 ha1
    dsimp only at *
    constructor <;> grind

open CosineFTC IntervalSelections

/-- Literal rational selections; every value here retains its stage index. -/
def sineSample (B : ArctanInverseBisection) (x : Rat) (n : Nat) : Rat :=
  ((sine B x).compute n).lo

def cosineSample (B : ArctanInverseBisection) (x : Rat) (n : Nat) : Rat :=
  ((cosine B x).compute n).hi

def primitiveSample (B : ArctanInverseBisection) (x : Rat) (n : Nat) : Rat :=
  (reciprocalPiRaw.compute n).hi * sineSample B x n

def parameterSample (B : ArctanInverseBisection) (x : Rat) (hx : OnHalf x)
    (n : Nat) : Rat := ((slope B x hx).compute n).lo

theorem sineSample_mem (B : ArctanInverseBisection) (x : Rat) (n : Nat) :
    InBox (sineSample B x n) ((sine B x).compute n) :=
  ⟨Rat.le_refl, RealRaw.interval_order_of_valid _ (sine_valid B x) n⟩

theorem cosineSample_mem (B : ArctanInverseBisection) (x : Rat) (n : Nat) :
    InBox (cosineSample B x n) ((cosine B x).compute n) :=
  ⟨RealRaw.interval_order_of_valid _ (cosine_valid B x) n, Rat.le_refl⟩

theorem primitiveSample_mem (B : ArctanInverseBisection) (x : Rat) (n : Nat) :
    InBox (primitiveSample B x n) ((primitive B x).compute n) :=
  mul_mem ⟨RealRaw.interval_order_of_valid _ reciprocalPiRaw_valid n, Rat.le_refl⟩
    (sineSample_mem B x n)

theorem sample_formulas (B : ArctanInverseBisection) (x : Rat) (hx : OnHalf x)
    (n : Nat) :
    sineSample B x n = pointIm (parameterSample B x hx n) ∧
      cosineSample B x n = pointRe (parameterSample B x hx n) := by
  simp only [sineSample, cosineSample, sine, cosine, dif_pos hx]
  exact ⟨rfl, rfl⟩

theorem parameterSample_unit (B : ArctanInverseBisection) (x : Rat)
    (hx : OnHalf x) (n : Nat) :
    0 <= parameterSample B x hx n ∧ parameterSample B x hx n <= 1 := by
  have hh := slope_unit B x hx n
  exact ⟨hh.1, Rat.le_trans hh.2.1 hh.2.2⟩

theorem piSample_bounds (n : Nat) :
    2 <= (piCircleArea.compute n).lo ∧ (piCircleArea.compute n).lo <= 4 := by
  have hh := CauchyPi.piCircleArea_valid.2.1 0 n (Nat.zero_le n)
  have hz : piCircleArea.compute 0 = ({lo := 2, hi := 4} : QInterval) := by decide +kernel
  rw [hz] at hh
  dsimp only at hh
  constructor <;> grind

/-- Supporting tangents of the normalized geometric sine, with arbitrary
rational slack and literal finite output selections. -/
theorem selected_support (B : ArctanInverseBisection) (x y : Rat)
    (hx : OnHalf x) (hy : OnHalf y) (eps : QPos) :
    ∃ N, ∀ n, N <= n ->
      sineSample B y n-sineSample B x n <=
        (y-x)*(piCircleArea.compute n).lo*cosineSample B x n+eps.val ∧
      (y-x)*(piCircleArea.compute n).lo*cosineSample B y n <=
        sineSample B y n-sineSample B x n+eps.val ∧
      qabs (cosineSample B y n-cosineSample B x n) <=
        32*qabs (y-x)+eps.val := by
  let eta : QPos := ⟨eps.val/128, by
    rw [Rat.div_def]
    exact Rat.mul_pos eps.property ((Rat.inv_pos).2 (by decide))⟩
  obtain ⟨Nx, hNx⟩ := slope_clock_close B x hx eta
  obtain ⟨Ny, hNy⟩ := slope_clock_close B y hy eta
  let NA := 4*(eta.val.den+1)
  refine ⟨max NA (max Nx Ny), ?_⟩
  intro n hn
  let u := parameterSample B x hx n
  let v := parameterSample B y hy n
  let A := arctanIntegralRectangleCompute v n
  let D := arctanIntegralRectangleCompute u n
  let p := (piCircleArea.compute n).lo
  have hu := parameterSample_unit B x hx n
  have hv := parameterSample_unit B y hy n
  have hU := slope_unit B x hx n
  have hV := slope_unit B y hy n
  have hAo : A.lo <= A.hi :=
    RealRaw.interval_order_of_valid _ (arctanIntegralRectangleRaw_valid hv.1 hv.2) n
  have hDo : D.lo <= D.hi :=
    RealRaw.interval_order_of_valid _ (arctanIntegralRectangleRaw_valid hu.1 hu.2) n
  have hpo := RealRaw.interval_order_of_valid _ CauchyPi.piCircleArea_valid n
  have hax := hNx n (by omega) u D.lo p (Rat.le_refl) hU.2.1
    (Rat.le_refl) hDo (Rat.le_refl) hpo
  have hay := hNy n (by omega) v A.lo p (Rat.le_refl) hV.2.1
    (Rat.le_refl) hAo (Rat.le_refl) hpo
  have wA := arctanIntegralRectangleCompute_width_le_eps_of_precision hv.1 hv.2 eta n
    (by dsimp [NA] at hn; omega)
  have wD := arctanIntegralRectangleCompute_width_le_eps_of_precision hu.1 hu.2 eta n
    (by dsimp [NA] at hn; omega)
  have hs := clock_support hu.1 hu.2 hv.1 hv.2 n (Rat.le_refl) hAo (Rat.le_refl) hDo
  have hclock := (clock_bounds hu.1 hu.2 hv.1 hv.2 n
    (Rat.le_refl : A.lo <= A.lo) hAo (Rat.le_refl : D.lo <= D.lo) hDo).2
  have hangle : qabs ((A.lo-D.lo)-(y-x)/2*p) <= 2*eta.val := by
    have hh := qabs_sub_le (A.lo-(y/2)*p) (D.lo-(x/2)*p)
    have he : (A.lo-D.lo)-(y-x)/2*p = (A.lo-(y/2)*p)-(D.lo-(x/2)*p) := by
      simp only [Rat.div_def]; grind
    rw [he]
    grind
  have hCu := cosine_coordinate_bounds hu.1 hu.2
  have hCv := cosine_coordinate_bounds hv.1 hv.2
  have hC2u : 0 <= 2*pointRe u := Rat.mul_nonneg (by decide) hCu.1
  have hC2v : 0 <= 2*pointRe v := Rat.mul_nonneg (by decide) hCv.1
  have hCl2u : 2*pointRe u <= 2 := by grind
  have hCl2v : 2*pointRe v <= 2 := by grind
  have hzero := Rat.le_of_lt eta.property
  have hneg := neg_qabs_le_self ((A.lo-D.lo)-(y-x)/2*p)
  have hpos := self_le_qabs ((A.lo-D.lo)-(y-x)/2*p)
  have hUpper : A.lo-D.lo <= (y-x)/2*p+2*eta.val := by grind
  have hLower : (y-x)/2*p-2*eta.val <= A.lo-D.lo := by grind
  have hup := Rat.mul_le_mul_of_nonneg_left hUpper hC2u
  have hlo := Rat.mul_le_mul_of_nonneg_left hLower hC2v
  have heru := Rat.mul_le_mul_of_nonneg_right hCl2u (Rat.mul_nonneg (by decide : (0 : Rat) <= 2) hzero)
  have herv := Rat.mul_le_mul_of_nonneg_right hCl2v (Rat.mul_nonneg (by decide : (0 : Rat) <= 2) hzero)
  have hPi := piSample_bounds n
  have hp0 : 0 <= p := by dsimp [p]; grind
  have hp4 : p <= 4 := hPi.2
  have hstep : qabs ((y-x)/2*p) <= 2*qabs (y-x) := by
    have hi : qabs ((2 : Rat)⁻¹) = (1 : Rat)/2 := by decide +kernel
    have hh := Rat.mul_le_mul_of_nonneg_left hp4 (qabs_nonneg (y-x))
    simp only [Rat.div_def, qabs_mul, hi, qabs_eq_self_of_nonneg hp0]
    simp only [Rat.div_def] at *
    grind
  have haSize : qabs (A.lo-D.lo) <= 2*qabs (y-x)+2*eta.val := by
    have ht := qabs_add_le ((A.lo-D.lo)-(y-x)/2*p) ((y-x)/2*p)
    have he : (A.lo-D.lo)-(y-x)/2*p+(y-x)/2*p = A.lo-D.lo := by grind
    rw [he] at ht
    grind
  have hcos := rationalCircleCos_difference_le_qabs hv.1 hv.2 hu.1 hu.2
  change qabs (pointRe v-pointRe u) <= 4*qabs (v-u) at hcos
  have hm := Rat.mul_le_mul_of_nonneg_left hclock (by decide : (0 : Rat) <= 4)
  have fx := sample_formulas B x hx n
  have fy := sample_formulas B y hy n
  rw [fx.1, fy.1, fx.2, fy.2]
  change _ <= (y-x)*p*pointRe u+eps.val ∧
    (y-x)*p*pointRe v <= _+eps.val ∧ _ <= _
  dsimp only at hs hclock
  change D.width <= eta.val at wD
  change A.width <= eta.val at wA
  have heta : 128*eta.val = eps.val := by
    dsimp [eta]; simp only [Rat.div_def]; grind
  simp only [Rat.div_def] at hup hlo
  constructor
  · grind
  constructor
  · grind
  · grind

/-- The normalized primitive has cosine supporting slopes. -/
theorem selected_primitive_support (B : ArctanInverseBisection) (x y : Rat)
    (hx : OnHalf x) (hy : OnHalf y) (eps : QPos) :
    ∃ N, ∀ n, N <= n ->
      primitiveSample B y n-primitiveSample B x n <=
        (y-x)*cosineSample B x n+eps.val ∧
      (y-x)*cosineSample B y n <=
        primitiveSample B y n-primitiveSample B x n+eps.val := by
  obtain ⟨N, hN⟩ := selected_support B x y hx hy eps
  refine ⟨N, ?_⟩
  intro n hn
  have hh := hN n hn
  have hr := reciprocal_corner n
  have h1 := Rat.mul_le_mul_of_nonneg_left hh.1 hr.1
  have h2 := Rat.mul_le_mul_of_nonneg_left hh.2.1 hr.1
  have he := Rat.mul_le_mul_of_nonneg_right hr.2.1 (Rat.le_of_lt eps.property)
  have hc := hr.2.2
  have hxCancel : (reciprocalPiRaw.compute n).hi *
      ((y-x)*(piCircleArea.compute n).lo*cosineSample B x n) =
      (y-x)*cosineSample B x n := by grind [Rat.mul_assoc, Rat.mul_comm]
  have hyCancel : (reciprocalPiRaw.compute n).hi *
      ((y-x)*(piCircleArea.compute n).lo*cosineSample B y n) =
      (y-x)*cosineSample B y n := by grind [Rat.mul_assoc, Rat.mul_comm]
  rw [Rat.mul_add, hxCancel] at h1
  rw [hyCancel, Rat.mul_add] at h2
  dsimp [primitiveSample]
  constructor <;> grind

/-- Exact supporting secants of sine/pi, with the original cosine. -/
theorem primitive_secant_bounds (B : ArctanInverseBisection) :
    ConcaveFTC.SecantBounds (primitiveFun B) (cosine B) 0 (1/2) := by
  apply ConcaveFTC.secant_bounds_of_selected_support (primitiveFun B) (cosine B)
    (primitiveSample B) (cosineSample B) 0 (1/2)
    (fun x _ => primitive_valid B x) (fun x _ => cosine_valid B x)
    (fun x _ => primitiveSample_mem B x) (fun x _ => cosineSample_mem B x)
  exact selected_primitive_support B

/-- The supporting slopes for the unscaled public sine have the pi factor. -/
def sineSlope (B : ArctanInverseBisection) (x : Rat) : RealRaw :=
  RealRaw.mul piCircleArea (cosine B x)

theorem sineSlope_valid (B : ArctanInverseBisection) (x : Rat) :
    (sineSlope B x).Valid :=
  RealRaw.mul_valid CauchyPi.piCircleArea_valid (cosine_valid B x)

theorem sine_secant_bounds (B : ArctanInverseBisection) :
    ConcaveFTC.SecantBounds (sineFun B) (sineSlope B) 0 (1/2) := by
  apply ConcaveFTC.secant_bounds_of_selected_support (sineFun B) (sineSlope B)
    (sineSample B) (fun x n => (piCircleArea.compute n).lo*cosineSample B x n)
    0 (1/2) (fun x _ => sine_valid B x) (fun x _ => sineSlope_valid B x)
    (fun x _ => sineSample_mem B x)
  · intro x _ n
    exact mul_mem
      ⟨Rat.le_refl, RealRaw.interval_order_of_valid _ CauchyPi.piCircleArea_valid n⟩
      (cosineSample_mem B x n)
  · intro x y hx hy eps
    obtain ⟨N, hN⟩ := selected_support B x y hx hy eps
    refine ⟨N, ?_⟩
    intro n hn
    have hh := hN n hn
    exact ⟨by simpa only [Rat.mul_assoc] using hh.1,
      by simpa only [Rat.mul_assoc] using hh.2.1⟩

/-- Concavity of precisely the existing geometric sin(pi*x), proved from
rational circle/clock supporting-line inequalities, not from differentiation. -/
theorem sine_concave (B : ArctanInverseBisection) :
    ExactConcaveOn (sineFun B) 0 (1/2) :=
  ConcaveFTC.concave_of_secant_bounds (sineFun B) (sineSlope B) 0 (1/2)
    (fun _ hx => hx) (fun x _ => sine_valid B x)
    (fun x _ => sineSlope_valid B x) (sine_secant_bounds B)

theorem primitive_concave (B : ArctanInverseBisection) :
    ExactConcaveOn (primitiveFun B) 0 (1/2) :=
  ConcaveFTC.concave_of_secant_bounds (primitiveFun B) (cosine B) 0 (1/2)
    (fun _ hx => hx) (fun x _ => primitive_valid B x)
    (fun x _ => cosine_valid B x) (primitive_secant_bounds B)

/-- A fixed rational Lipschitz bound for cosine, formulated only with
cross-stage rational endpoints. -/
theorem cosine_lipschitz (B : ArctanInverseBisection) (x y : Rat)
    (hx : OnHalf x) (hy : OnHalf y) :
    ∀ n m, ((cosine B y).compute n).lo <=
      ((cosine B x).compute m).hi+32*qabs (y-x) := by
  apply endpoint_le_of_eventually (cosine_valid B y) (cosine_valid B x)
    (cosineSample B y) (cosineSample B x)
    (cosineSample_mem B y) (cosineSample_mem B x) (32*qabs (y-x))
  intro eps
  obtain ⟨N, hN⟩ := selected_support B x y hx hy eps
  refine ⟨N, ?_⟩
  intro n hn
  have h1 := (hN n hn).2.2
  have h2 := self_le_qabs (cosineSample B y n-cosineSample B x n)
  grind

def sineSlopeSample (B : ArctanInverseBisection) (x : Rat) (n : Nat) : Rat :=
  (piCircleArea.compute n).lo*cosineSample B x n

theorem sineSlopeSample_mem (B : ArctanInverseBisection) (x : Rat) (n : Nat) :
    InBox (sineSlopeSample B x n) ((sineSlope B x).compute n) :=
  mul_mem ⟨Rat.le_refl, RealRaw.interval_order_of_valid _ CauchyPi.piCircleArea_valid n⟩
    (cosineSample_mem B x n)

theorem sineSlope_lipschitz (B : ArctanInverseBisection) (x y : Rat)
    (hx : OnHalf x) (hy : OnHalf y) :
    ∀ n m, ((sineSlope B y).compute n).lo <=
      ((sineSlope B x).compute m).hi+128*qabs (y-x) := by
  apply endpoint_le_of_eventually (sineSlope_valid B y) (sineSlope_valid B x)
    (sineSlopeSample B y) (sineSlopeSample B x)
    (sineSlopeSample_mem B y) (sineSlopeSample_mem B x) (128*qabs (y-x))
  intro eps
  let eta : QPos := ⟨eps.val/4, by
    rw [Rat.div_def]; exact Rat.mul_pos eps.property ((Rat.inv_pos).2 (by decide))⟩
  obtain ⟨N, hN⟩ := selected_support B x y hx hy eta
  refine ⟨N, ?_⟩
  intro n hn
  have hh := (hN n hn).2.2
  have hp := piSample_bounds n
  have hp0 : 0 <= (piCircleArea.compute n).lo := by grind
  have h1 := Rat.mul_le_mul_of_nonneg_left
    (self_le_qabs (cosineSample B y n-cosineSample B x n)) hp0
  have h2 := Rat.mul_le_mul_of_nonneg_right hp.2
    (qabs_nonneg (cosineSample B y n-cosineSample B x n))
  have h3 := Rat.mul_le_mul_of_nonneg_left hh (by decide : (0 : Rat) <= 4)
  dsimp [sineSlopeSample, eta]
  dsimp [eta] at h3
  simp only [Rat.div_def] at h3
  grind

/-- Concrete inhabitants: no derivative or FTC hypothesis is supplied by a
caller in addition to the existing inverse provider B. -/
def primitiveDerivativeData (B : ArctanInverseBisection) :
    ConcaveFTC.DerivativeData (primitiveFun B) (cosine B) 0 (1/2) where
  concave := primitive_concave B
  valid := fun x _ => cosine_valid B x
  secants := primitive_secant_bounds B
  K := 32
  lipschitz := cosine_lipschitz B

def sineDerivativeData (B : ArctanInverseBisection) :
    ConcaveFTC.DerivativeData (sineFun B) (sineSlope B) 0 (1/2) where
  concave := sine_concave B
  valid := fun x _ => sineSlope_valid B x
  secants := sine_secant_bounds B
  K := 128
  lipschitz := sineSlope_lipschitz B

/-- A rational radius, with no precision search. -/
def chartRadius (x : Rat) (hx : 0 < x ∧ x < (1 : Rat)/2) : QPos :=
  ⟨min x ((1 : Rat)/2-x), by
    have h1 := hx.1
    have h2 : 0 < (1 : Rat)/2-x := by grind
    grind⟩

theorem chartRadius_bounds (x : Rat) (hx : 0 < x ∧ x < (1 : Rat)/2) :
    (chartRadius x hx).val <= 1 ∧
      0 <= x-(chartRadius x hx).val ∧ x+(chartRadius x hx).val <= (1 : Rat)/2 := by
  have hx0 := hx.1
  have hx1 := hx.2
  dsimp [chartRadius]
  simp only [Rat.div_def] at *
  constructor
  · grind
  constructor <;> grind

/-- Concave derivative constructed solely from the original sine's secants. -/
def sineDerivative (B : ArctanInverseBisection) (x : Rat)
    (hx : 0 < x ∧ x < (1 : Rat)/2) : RealRaw :=
  ConcaveFTC.derivative (sine_concave B) x (chartRadius x hx)

theorem sineDerivative_valid (B : ArctanInverseBisection) (x : Rat)
    (hx : 0 < x ∧ x < (1 : Rat)/2) : (sineDerivative B x hx).Valid := by
  have hh := chartRadius_bounds x hx
  exact ConcaveFTC.derivative_valid (sineDerivativeData B) (chartRadius x hx)
    hh.1 hh.2.1 hh.2.2

theorem sineDerivative_equiv_pi_cosine (B : ArctanInverseBisection) (x : Rat)
    (hx : 0 < x ∧ x < (1 : Rat)/2) :
    (sineDerivative B x hx).Equiv (RealRaw.mul piCircleArea (cosine B x)) := by
  have hh := chartRadius_bounds x hx
  exact ConcaveFTC.derivative_equiv (sineDerivativeData B) (chartRadius x hx) hh.2.1 hh.2.2

end GeometricSineConcavity
end ComputableAnalysis
