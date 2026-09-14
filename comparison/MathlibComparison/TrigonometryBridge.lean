import MathlibComparison.RealModel
import MathlibComparison.ArctanBridge

/-!
# The original inverse-arctangent sine and cosine in Mathlib

These are representation theorems for the existing interval programs, not
new definitions of sine and cosine. The generic inverse provider is exactly
the data already required by those programs. Neither native cosine-integral
proof nor a native sine-derivative theorem is used.
-/
namespace MathlibComparison
open ComputableAnalysis ArctanGeometry IntegralIdentities SinPiIntegral
open GeometricSineDerivative IntervalSelections Filter Topology

/-- Identify the value of the inverse arctangent used by both coordinates. -/
lemma slope_arctan (B : ArctanInverseBisection) (x : Rat) (hx : OnHalf x) :
    Real.arctan (denote (slope B x hx) (slope_valid B x hx)) = (x : ℝ)/2*Real.pi := by
  let U := slope B x hx
  let us := fun n => (U.compute n).lo
  let u := denote U (slope_valid B x hx)
  have hU : U.Valid := slope_valid B x hx
  have htU : Tendsto (fun n => (us n : ℝ)) atTop (𝓝 u) :=
    lower_tendsto hU (denote_represents U hU)
  have htA := Real.continuous_arctan.continuousAt.tendsto.comp htU
  have htP := lower_tendsto CauchyPi.piCircleArea_valid piCircleArea_represents
  have ht : Tendsto (fun n => |Real.arctan (us n : ℝ)-(x:ℝ)/2*((piCircleArea.compute n).lo:ℝ)|)
      atTop (𝓝 |Real.arctan u-(x:ℝ)/2*Real.pi|) :=
    (htA.sub (tendsto_const_nhds.mul htP)).abs
  have hbound (eps : QPos) : |Real.arctan u-(x:ℝ)/2*Real.pi| ≤ (eps.val : ℝ) := by
    obtain ⟨N,hN⟩ := slope_clock_close B x hx eps
    apply le_of_tendsto ht
    filter_upwards [eventually_ge_atTop N] with n hn
    have hu := slope_unit B x hx n
    have hAr := arctan_rectangle_represents (u := us n) hu.1 n
    have hao := RealRaw.interval_order_of_valid _
      (arctanIntegralRectangleRaw_valid hu.1 (Rat.le_trans hu.2.1 hu.2.2)) n
    have hpo := RealRaw.interval_order_of_valid _ CauchyPi.piCircleArea_valid n
    have hl := hN n hn (us n) (arctanIntegralRectangleCompute (us n) n).lo
      (piCircleArea.compute n).lo Rat.le_refl hu.2.1 Rat.le_refl hao Rat.le_refl hpo
    have hh := hN n hn (us n) (arctanIntegralRectangleCompute (us n) n).hi
      (piCircleArea.compute n).lo Rat.le_refl hu.2.1 hao Rat.le_refl Rat.le_refl hpo
    have hl' : |((arctanIntegralRectangleCompute (us n) n).lo : ℝ) -
        (x:ℝ)/2*((piCircleArea.compute n).lo:ℝ)| ≤ (eps.val:ℝ) := by
      have hcast : ((qabs ((arctanIntegralRectangleCompute (us n) n).lo-
        (x/2)*(piCircleArea.compute n).lo)) : ℝ) ≤ (eps.val:ℝ) := by exact_mod_cast hl
      simpa only [qabs_cast,Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] using hcast
    have hh' : |((arctanIntegralRectangleCompute (us n) n).hi : ℝ) -
        (x:ℝ)/2*((piCircleArea.compute n).lo:ℝ)| ≤ (eps.val:ℝ) := by
      have hcast : ((qabs ((arctanIntegralRectangleCompute (us n) n).hi-
        (x/2)*(piCircleArea.compute n).lo)) : ℝ) ≤ (eps.val:ℝ) := by exact_mod_cast hh
      simpa only [qabs_cast,Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] using hcast
    have h1 := (abs_le.1 hl').1
    have h2 := (abs_le.1 hh').2
    change ((arctanIntegralRectangleCompute (us n) n).lo:ℝ) ≤ _ ∧
      _ ≤ ((arctanIntegralRectangleCompute (us n) n).hi:ℝ) at hAr
    exact abs_le.2 ⟨by linarith [hAr.1],by linarith [hAr.2]⟩
  by_contra h
  have hp : 0 < |Real.arctan u-(x:ℝ)/2*Real.pi| := abs_pos.mpr (sub_ne_zero.mpr h)
  obtain ⟨eps,heps⟩ := rational_tolerance hp
  have hh := hbound eps
  linarith

private lemma sin_double_arctan (u : ℝ) :
    Real.sin (2*Real.arctan u) = 2*u/(1+u*u) := by
  rw [Real.sin_two_mul,Real.sin_arctan,Real.cos_arctan]
  have hs : Real.sqrt (1+u^2) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by positivity))
  have hp : 1+u*u ≠ 0 := by nlinarith [sq_nonneg u]
  have hsq := Real.sq_sqrt (show 0 ≤ 1+u^2 by positivity)
  field_simp
  rw [hsq]

private lemma cos_double_arctan (u : ℝ) :
    Real.cos (2*Real.arctan u) = (1-u*u)/(1+u*u) := by
  rw [Real.cos_two_mul,Real.cos_sq_arctan]
  have hp : 1+u*u ≠ 0 := by nlinarith [sq_nonneg u]
  field_simp
  ring

/-- The exact existing geometric sine represents Mathlib's normalized sine. -/
theorem sine_represents (B : ArctanInverseBisection) (x : Rat) (hx : OnHalf x) :
    Represents (sinPiRawOfArctan B x hx) (Real.sin (Real.pi*(x:ℝ))) := by
  let U := slope B x hx
  let u := denote U (slope_valid B x hx)
  have hU : U.Valid := slope_valid B x hx
  have hu := lower_tendsto hU (denote_represents U hU)
  have hden : 1+u*u ≠ 0 := by nlinarith [sq_nonneg u]
  have ht : Tendsto (fun n => 2*((U.compute n).lo:ℝ)/(1+((U.compute n).lo:ℝ)*((U.compute n).lo:ℝ)))
      atTop (𝓝 (2*u/(1+u*u))) :=
    (tendsto_const_nhds.mul hu).div (tendsto_const_nhds.add (hu.mul hu)) hden
  have ha := slope_arctan B x hx
  have heq : 2*Real.arctan u = Real.pi*(x:ℝ) := by dsimp [u,U]; linarith
  have hv : 2*u/(1+u*u) = Real.sin (Real.pi*(x:ℝ)) := by
    rw [← sin_double_arctan,heq]
  apply represents_of_tendsto (sinPiRawOfArctan_valid B x hx)
    (fun n => ((sinPiRawOfArctan B x hx).compute n).lo)
  · intro n
    exact ⟨Rat.le_refl,RealRaw.interval_order_of_valid _ (sinPiRawOfArctan_valid B x hx) n⟩
  · change Tendsto (fun n => ((2*(U.compute n).lo/(1+(U.compute n).lo*(U.compute n).lo):Rat):ℝ))
      atTop (𝓝 (Real.sin (Real.pi*(x:ℝ))))
    simp only [Rat.cast_div,Rat.cast_mul,Rat.cast_add,Rat.cast_one,Rat.cast_ofNat]
    rw [← hv]
    exact ht

/-- The cosine program uses the same inverse parameter; its upper coordinate
endpoint corresponds to the lower inverse-slope endpoint. -/
theorem cosine_represents (B : ArctanInverseBisection) (x : Rat) (hx : OnHalf x) :
    Represents (cosPiRawOfArctan B x hx) (Real.cos (Real.pi*(x:ℝ))) := by
  let U := slope B x hx
  let u := denote U (slope_valid B x hx)
  have hU : U.Valid := slope_valid B x hx
  have hu := lower_tendsto hU (denote_represents U hU)
  have hden : 1+u*u ≠ 0 := by nlinarith [sq_nonneg u]
  have ht : Tendsto (fun n => (1-((U.compute n).lo:ℝ)*((U.compute n).lo:ℝ))/
      (1+((U.compute n).lo:ℝ)*((U.compute n).lo:ℝ))) atTop (𝓝 ((1-u*u)/(1+u*u))) :=
    (tendsto_const_nhds.sub (hu.mul hu)).div (tendsto_const_nhds.add (hu.mul hu)) hden
  have ha := slope_arctan B x hx
  have heq : 2*Real.arctan u = Real.pi*(x:ℝ) := by dsimp [u,U]; linarith
  have hv : (1-u*u)/(1+u*u) = Real.cos (Real.pi*(x:ℝ)) := by
    rw [← cos_double_arctan,heq]
  apply represents_of_tendsto (cosPiRawOfArctan_valid B x hx)
    (fun n => ((cosPiRawOfArctan B x hx).compute n).hi)
  · intro n
    exact ⟨RealRaw.interval_order_of_valid _ (cosPiRawOfArctan_valid B x hx) n,Rat.le_refl⟩
  · change Tendsto (fun n => (((1-(U.compute n).lo*(U.compute n).lo)/
        (1+(U.compute n).lo*(U.compute n).lo):Rat):ℝ))
      atTop (𝓝 (Real.cos (Real.pi*(x:ℝ))))
    simp only [Rat.cast_div,Rat.cast_mul,Rat.cast_add,Rat.cast_sub,Rat.cast_one]
    rw [← hv]
    exact ht

end MathlibComparison
