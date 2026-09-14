import ComputableAnalysis.GeometricSineFiniteBounds

/-! Direct finite geometric inequalities. The statement below is a quadratic
bound on positive increments, derived from rational circle/clock identities.
It does not invoke a derivative, concavity, or FTC theorem. -/
namespace ComputableAnalysis
namespace GeometricSineDirectBounds
open ArctanGeometry IntegralIdentities SinPiIntegral
open GeometricRotationODE GeometricSineSecant GeometricSineDerivative
open GeometricSineFiniteBounds

theorem positive_increment_error (B : ArctanInverseBisection) :
  ∀ x h : Rat,
    ∀ (hx : OnHalf x) (hxh : OnHalf (x+h)),
    0 < h ->
    ∃ N : Nat, ∀ n : Nat, N <= n -> ∀ a b c p : Rat,
      ((sinPiRawOfArctan B (x+h) hxh).compute n).lo <= a ->
      a <= ((sinPiRawOfArctan B (x+h) hxh).compute n).hi ->
      ((sinPiRawOfArctan B x hx).compute n).lo <= b ->
      b <= ((sinPiRawOfArctan B x hx).compute n).hi ->
      ((cosPiRawOfArctan B x hx).compute n).lo <= c ->
      c <= ((cosPiRawOfArctan B x hx).compute n).hi ->
      (piCircleArea.compute n).lo <= p -> p <= (piCircleArea.compute n).hi ->
      qabs (a-b-h*(p*c)) <= 4000*h*h := by
  intro x h hx hxh hp
  have hh : h ≠ 0 := Rat.ne_of_gt hp
  have habs : qabs h = h := qabs_eq_self_of_nonneg (Rat.le_of_lt hp)
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
    { val := h*h/64
      property := by
        rw [Rat.div_def]
        exact Rat.mul_pos (Rat.mul_pos hp hp) ((Rat.inv_pos).2 (by decide)) }
  have hetaH : eta.val <= qabs h/16 := by
    have hm := Rat.mul_le_mul_of_nonneg_right hH1 hH0
    dsimp [eta]
    rw [habs] at *
    simp only [Rat.div_def] at *
    grind
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
  have hPi := pi_output_bounds n hp0 hp1
  have hbound := finite_normalized_residual hu.1 hu.2 hPi.1 hPi.2 hH1
    (Rat.le_of_lt eta.property) hetaH (by grind : D.width+A.width <= 2*eta.val)
    hs1 hs0 hcs hangle1 hangle0 hclock hsine
  have hbudget : 1620*qabs h*qabs h+14*eta.val <= 4000*h*h := by
    have hs := Rat.mul_nonneg (Rat.le_of_lt hp) (Rat.le_of_lt hp)
    dsimp [eta]
    rw [habs]
    simp only [Rat.div_def]
    grind
  exact Rat.le_trans hbound hbudget

end GeometricSineDirectBounds
end ComputableAnalysis
