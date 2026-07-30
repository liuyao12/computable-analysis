import ComputableAnalysis.PiProofs
import ComputableAnalysis.AlgebraicFunctions

/-!
# Direct circumference refinement bridge

This module closes the direct chord-path circumference proof.  It compares the
fine secant certificates with the earlier curvature certificates, pays the
literal square-root bisection budget, and lifts the resulting local inequality
to every dyadic stage.
-/

namespace ComputableAnalysis

namespace PiProofs

/-- The two rational curvature certificates of the doubled circle stage cover
the squared chord at the previous stage.

This is the concrete `circleSamplePoint` form of
`RationalCircle.Stage.midpoint_curvature_certificate_refines_squared_chord_of_refinement`.
It contains no square roots or limit argument.  The secant--curvature budget
below pays the two bisection widths and turns this local comparison into the
original endpoint refinement. -/
theorem adjacentCurvatureCertificates_refineSquaredChord
    (stage k : Nat) (hstage : 0 < stage) (hk : k < stage) :
    pointSegmentNormSq (circleSamplePoint stage k)
        (circleSamplePoint stage (k + 1)) <=
      sq (curvatureChordLower
            (circleSamplePoint (2 * stage) (2 * k))
            (circleSamplePoint (2 * stage) (2 * k + 1)) +
          curvatureChordLower
            (circleSamplePoint (2 * stage) (2 * k + 1))
            (circleSamplePoint (2 * stage) (2 * k + 2))) := by
  have href : RationalCircle.Stage.RefinesByDoubling
      (rationalCircleStage stage) (rationalCircleStage (2 * stage)) := by
    rfl
  simpa [circleSamplePoint_eq_rationalCircleStage,
    pointSegmentNormSq_eq_rationalCircleSegmentNormSq,
    curvatureChordLower, pointCross_eq_rationalCircleCross,
    RationalCircle.Stage.refineIndex, RationalCircle.Stage.insertedIndex,
    Rat.add_assoc] using
    (RationalCircle.Stage.midpoint_curvature_certificate_refines_squared_chord_of_refinement
      href hstage k hk)

/-- The explicit secant-margin budget holds at the initial one-cell stage.
This is a finite rational normalization check, not a numerical approximation
or a claim about all later stages. -/
theorem adjacentChordSecantMarginCoversFineDyadicBudget_one :
    AdjacentChordSecantMarginCoversFineDyadicBudget 1 := by
  intro k
  have hkzero : k = (⟨0, by omega⟩ : Fin 1) :=
    Fin.ext (by omega)
  subst k
  native_decide

/-- The original square-root lower-chord endpoint refines at the first dyadic
step. -/
theorem adjacentChordLowerRefinesByDoubling_one :
    AdjacentChordLowerRefinesByDoubling 1 :=
  adjacentChordLowerRefinesByDoubling_of_secantMargin 1 (by native_decide)
    (adjacentChordSecantMargin_of_fineDyadicBudget 1 (by native_decide)
      adjacentChordSecantMarginCoversFineDyadicBudget_one)

/-- The same explicit secant-margin calculation succeeds for the two-cell
stage.  The cases are enumerated as rational arithmetic, not sampled
floating-point evidence. -/
theorem adjacentChordSecantMarginCoversFineDyadicBudget_two :
    AdjacentChordSecantMarginCoversFineDyadicBudget 2 := by
  intro k
  have hcases : k.1 = 0 ∨ k.1 = 1 := by omega
  rcases hcases with hzero | hone
  · have hk : k = (⟨0, by omega⟩ : Fin 2) := Fin.ext hzero
    rw [hk]
    simp
    native_decide
  · have hk : k = (⟨1, by omega⟩ : Fin 2) := Fin.ext hone
    rw [hk]
    simp
    native_decide

/-- The original chord endpoint also refines at the two-cell stage. -/
theorem adjacentChordLowerRefinesByDoubling_two :
    AdjacentChordLowerRefinesByDoubling 2 :=
  adjacentChordLowerRefinesByDoubling_of_secantMargin 2 (by native_decide)
    (adjacentChordSecantMargin_of_fineDyadicBudget 2 (by native_decide)
      adjacentChordSecantMarginCoversFineDyadicBudget_two)

private theorem point_cross_le_one (u v : Rat) :
    RationalCircle.Stage.cross
        (RationalCircle.Stage.point u) (RationalCircle.Stage.point v) <= 1 := by
  let d := v - u
  let a := 1 + u * v
  let D := (1 + u * u) * (1 + v * v)
  have hD : 0 < D := by
    dsimp [D]
    exact Rat.mul_pos
      (RationalCircle.Stage.one_add_square_pos u)
      (RationalCircle.Stage.one_add_square_pos v)
  have hidentity : D = a * a + d * d := by
    dsimp [D, a, d]
    grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.add_assoc,
      Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
  have hsq : 0 <= sq (a - d) := by
    unfold sq
    by_cases h : 0 <= a - d
    · exact Rat.mul_nonneg h h
    · have hneg : 0 <= -(a - d) := by grind
      have : 0 <= (-(a - d)) * (-(a - d)) := Rat.mul_nonneg hneg hneg
      grind [Rat.neg_mul, Rat.mul_neg, Rat.neg_neg]
  have hnumerator : 2 * d * a <= D := by
    rw [hidentity]
    unfold sq at hsq
    grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.add_assoc,
      Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
  rw [RationalCircle.Stage.point_cross_formula]
  apply Rat.le_of_mul_le_mul_right (c := D)
  · rw [Rat.div_def]
    have hDne : D ≠ 0 := Rat.ne_of_gt hD
    calc
      (2 * (v - u) * (1 + u * v) * D⁻¹) * D = 2 * d * a := by
        dsimp [D, d, a]
        grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
      _ <= D := hnumerator
      _ = 1 * D := by grind
  · exact hD

/-- Any adjacent chart sample pair has cross product at most one. -/
private theorem circleSamplePoint_cross_le_one (stage : Nat) (k : Nat) :
    RationalCircle.Stage.cross
        (circleSamplePoint stage k)
        (circleSamplePoint stage (k + 1)) <= 1 := by
  simpa [circleSamplePoint, circlePoint] using
    point_cross_le_one (circleParameter stage k) (circleParameter stage (k + 1))

private theorem secant_curvature_gap {p q : PiCirclePoint}
    (hcross : 0 < RationalCircle.Stage.cross p q)
    (hcross_le_one : RationalCircle.Stage.cross p q <= 1)
    (hdeficit : 0 <= 1 - RationalCircle.Stage.dot p q)
    (hdeficit_le_one : 1 - RationalCircle.Stage.dot p q <= 1) :
    curvatureChordLower p q +
        sq (1 - RationalCircle.Stage.dot p q) / 12 <=
      RationalCircle.Stage.secantChordLower p q := by
  let c := RationalCircle.Stage.cross p q
  let d := 1 - RationalCircle.Stage.dot p q
  let e := 2 * c + d
  have hc : 0 < c := by simpa [c] using hcross
  have hc1 : c <= 1 := by simpa [c] using hcross_le_one
  have hd : 0 <= d := by simpa [d] using hdeficit
  have hd1 : d <= 1 := by simpa [d] using hdeficit_le_one
  have he : 0 < e := by
    dsimp [e]
    have : 0 < 2 * c := Rat.mul_pos (by native_decide) hc
    grind
  have he3 : e <= 3 := by
    dsimp [e]
    grind
  have hrecip : (1 : Rat) / 3 <= e⁻¹ := by
    apply Rat.le_of_mul_le_mul_right (c := 3 * e)
    · have hthree : (3 : Rat) ≠ 0 := by native_decide
      have he_ne : e ≠ 0 := Rat.ne_of_gt he
      rw [Rat.div_def]
      calc
        (1 * (3 : Rat)⁻¹) * (3 * e) = e := by
          grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
        _ <= 3 := he3
        _ = e⁻¹ * (3 * e) := by
          grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
    · exact Rat.mul_pos (by native_decide) he
  have hd_sq : 0 <= sq d := by
    unfold sq
    exact Rat.mul_nonneg hd hd
  have hthird : sq d / 3 <= sq d / e := by
    rw [Rat.div_def, Rat.div_def]
    exact Rat.mul_le_mul_of_nonneg_left (by
      simpa [Rat.div_def] using hrecip) hd_sq
  have hcombine : sq d / 4 + sq d / 12 = sq d / 3 := by
    grind [Rat.div_def, Rat.mul_assoc]
  change c + sq d / 4 + sq d / 12 <= c + sq d / e
  calc
    c + sq d / 4 + sq d / 12 = c + (sq d / 4 + sq d / 12) := by
      grind [Rat.add_assoc]
    _ = c + sq d / 3 := by rw [hcombine]
    _ <= c + sq d / e := (Rat.add_le_add_left).2 hthird

private theorem adjacent_secant_curvature_gap
    (stage : Nat) (hstage : 0 < stage) (k : Nat) (hk : k < stage) :
    curvatureChordLower (circleSamplePoint stage k)
        (circleSamplePoint stage (k + 1)) +
      ((1 / (stage : Rat)) * (1 / (stage : Rat)) *
        (1 / (stage : Rat)) * (1 / (stage : Rat))) / 768 <=
      RationalCircle.Stage.secantChordLower
        (circleSamplePoint stage k) (circleSamplePoint stage (k + 1)) := by
  let p := circleSamplePoint stage k
  let q := circleSamplePoint stage (k + 1)
  let c := RationalCircle.Stage.cross p q
  let d := 1 - RationalCircle.Stage.dot p q
  let h : Rat := 1 / (stage : Rat)
  have hp : RationalCircle.Stage.normSq p = 1 := by
    dsimp [p]
    exact RationalCircle.Stage.samplePoint_normSq_unit
      (rationalCircleStage stage) k
  have hq : RationalCircle.Stage.normSq q = 1 := by
    dsimp [q]
    exact RationalCircle.Stage.samplePoint_normSq_unit
      (rationalCircleStage stage) (k + 1)
  have hcpos : 0 < c := by
    dsimp [c, p, q]
    exact RationalCircle.Stage.samplePoint_cross_pos_adjacent
      (rationalCircleStage stage) hstage k
  have hc_one : c <= 1 := by
    dsimp [c, p, q]
    exact circleSamplePoint_cross_le_one stage k
  have hd : 0 <= d := by
    dsimp [d, p, q]
    exact RationalCircle.Stage.one_sub_point_dot_nonneg
      (circleParameter stage k) (circleParameter stage (k + 1))
  have hdot : 0 <= RationalCircle.Stage.dot p q := by
    dsimp [p, q]
    exact circleSamplePoint_dot_nonneg_adjacent stage hstage k
  have hd_one : d <= 1 := by
    dsimp [d]
    grind [Rat.sub_eq_add_neg]
  have hh : 0 < h := by
    dsimp [h]
    rw [Rat.div_def, Rat.one_mul]
    exact Rat.inv_pos.mpr ((Rat.natCast_pos).2 hstage)
  have hcross_mesh : h / 2 <= c := by
    dsimp [h, c, p, q]
    simpa [circleSamplePoint, circlePoint] using
      (RationalCircle.Stage.samplePoint_cross_ge_half_step
        (rationalCircleStage stage) hstage k hk)
  have hhalf_nonneg : 0 <= h / 2 := by
    rw [Rat.div_def]
    exact Rat.le_of_lt (Rat.mul_pos hh (by native_decide))
  have hsquare_mesh : sq (h / 2) <= sq c :=
    sq_le_sq_of_nonneg_le hhalf_nonneg hcross_mesh
  have hcross_deficit : sq c <= 2 * d := by
    dsimp [c, d, p, q]
    exact RationalCircle.Stage.cross_sq_le_two_one_sub_dot_of_unit hp hq hd
  have hhalf_deficit : sq (h / 2) / 2 <= d := by
    apply Rat.le_of_mul_le_mul_right (c := 2)
    · calc
        (sq (h / 2) / 2) * 2 = sq (h / 2) := by
          rw [Rat.div_def]
          have htwo : (2 : Rat) ≠ 0 := by native_decide
          grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
        _ <= 2 * d := Rat.le_trans hsquare_mesh hcross_deficit
        _ = d * 2 := by grind [Rat.mul_comm]
    · native_decide
  have hhalf_deficit_nonneg : 0 <= sq (h / 2) / 2 := by
    rw [Rat.div_def]
    have hsq : 0 <= sq (h / 2) := by
      unfold sq
      exact Rat.mul_nonneg hhalf_nonneg hhalf_nonneg
    exact Rat.mul_nonneg hsq (by native_decide)
  have hfourth : sq (sq (h / 2) / 2) <= sq d :=
    sq_le_sq_of_nonneg_le hhalf_deficit_nonneg hhalf_deficit
  have hbudget :
      (h * h * h * h) / 768 <= sq d / 12 := by
    have hdiv := Rat.div_le_div_of_nonneg_right hfourth
      (by native_decide : (0 : Rat) < 12)
    have hformula :
        (h * h * h * h) / 768 = sq (sq (h / 2) / 2) / 12 := by
      unfold sq
      grind [Rat.div_def, Rat.mul_assoc, Rat.mul_comm]
    rw [hformula]
    exact hdiv
  calc
    curvatureChordLower p q + (h * h * h * h) / 768 <=
        curvatureChordLower p q + sq d / 12 :=
      (Rat.add_le_add_left).2 hbudget
    _ <= RationalCircle.Stage.secantChordLower p q :=
      secant_curvature_gap hcpos hc_one hd hd_one

private theorem secant_margin_of_bisection_budget
    (stage : Nat) (hstage : 0 < stage)
    (hbudget : adjacentChordBisectionWidth (2 * stage) <=
      ((1 / ((2 * stage : Nat) : Rat)) *
        (1 / ((2 * stage : Nat) : Rat)) *
        (1 / ((2 * stage : Nat) : Rat)) *
        (1 / ((2 * stage : Nat) : Rat))) / 768) :
    AdjacentChordSecantMarginCoversFineDyadicBudget stage := by
  intro k
  let p := circleSamplePoint stage k.1
  let q := circleSamplePoint stage (k.1 + 1)
  let p' := circleSamplePoint (2 * stage) (2 * k.1)
  let m := circleSamplePoint (2 * stage) (2 * k.1 + 1)
  let q' := circleSamplePoint (2 * stage) (2 * k.1 + 2)
  let b := adjacentChordBisectionWidth (2 * stage)
  let curvLeft := curvatureChordLower p' m
  let curvRight := curvatureChordLower m q'
  let secantLeft := RationalCircle.Stage.secantChordLower p' m
  let secantRight := RationalCircle.Stage.secantChordLower m q'
  let r := secantLeft + secantRight - b - b
  have htwostage : 0 < 2 * stage := by omega
  have hleft_gap := adjacent_secant_curvature_gap
    (2 * stage) htwostage (2 * k.1) (by omega)
  have hright_gap := adjacent_secant_curvature_gap
    (2 * stage) htwostage (2 * k.1 + 1) (by omega)
  have hleft : curvLeft + b <= secantLeft := by
    dsimp [curvLeft, b, secantLeft, p', m]
    calc
      curvatureChordLower
          (circleSamplePoint (2 * stage) (2 * k.1))
          (circleSamplePoint (2 * stage) (2 * k.1 + 1)) +
          adjacentChordBisectionWidth (2 * stage) <=
        curvatureChordLower
          (circleSamplePoint (2 * stage) (2 * k.1))
          (circleSamplePoint (2 * stage) (2 * k.1 + 1)) +
          ((1 / ((2 * stage : Nat) : Rat)) *
            (1 / ((2 * stage : Nat) : Rat)) *
            (1 / ((2 * stage : Nat) : Rat)) *
            (1 / ((2 * stage : Nat) : Rat))) / 768 :=
          (Rat.add_le_add_left).2 hbudget
      _ <= RationalCircle.Stage.secantChordLower
          (circleSamplePoint (2 * stage) (2 * k.1))
          (circleSamplePoint (2 * stage) (2 * k.1 + 1)) := by
          simpa using hleft_gap
  have hright : curvRight + b <= secantRight := by
    dsimp [curvRight, b, secantRight, m, q']
    calc
      curvatureChordLower
          (circleSamplePoint (2 * stage) (2 * k.1 + 1))
          (circleSamplePoint (2 * stage) (2 * k.1 + 2)) +
          adjacentChordBisectionWidth (2 * stage) <=
        curvatureChordLower
          (circleSamplePoint (2 * stage) (2 * k.1 + 1))
          (circleSamplePoint (2 * stage) (2 * k.1 + 2)) +
          ((1 / ((2 * stage : Nat) : Rat)) *
            (1 / ((2 * stage : Nat) : Rat)) *
            (1 / ((2 * stage : Nat) : Rat)) *
            (1 / ((2 * stage : Nat) : Rat))) / 768 :=
          (Rat.add_le_add_left).2 hbudget
      _ <= RationalCircle.Stage.secantChordLower
          (circleSamplePoint (2 * stage) (2 * k.1 + 1))
          (circleSamplePoint (2 * stage) (2 * k.1 + 2)) := by
          simpa using hright_gap
  have hcurvLeft : 0 <= curvLeft := by
    dsimp [curvLeft, p', m, curvatureChordLower]
    have hcross : 0 <= RationalCircle.Stage.cross
        (circleSamplePoint (2 * stage) (2 * k.1))
        (circleSamplePoint (2 * stage) (2 * k.1 + 1)) := by
      exact Rat.le_of_lt
        (RationalCircle.Stage.samplePoint_cross_pos_adjacent
          (rationalCircleStage (2 * stage)) htwostage (2 * k.1))
    have hsq : 0 <= sq (1 - RationalCircle.Stage.dot
        (circleSamplePoint (2 * stage) (2 * k.1))
        (circleSamplePoint (2 * stage) (2 * k.1 + 1))) := by
      unfold sq
      by_cases h : 0 <= 1 - RationalCircle.Stage.dot
          (circleSamplePoint (2 * stage) (2 * k.1))
          (circleSamplePoint (2 * stage) (2 * k.1 + 1))
      · exact Rat.mul_nonneg h h
      · have hneg : 0 <= -(1 - RationalCircle.Stage.dot
            (circleSamplePoint (2 * stage) (2 * k.1))
            (circleSamplePoint (2 * stage) (2 * k.1 + 1))) := by grind
        have : 0 <= (-(1 - RationalCircle.Stage.dot
              (circleSamplePoint (2 * stage) (2 * k.1))
              (circleSamplePoint (2 * stage) (2 * k.1 + 1)))) *
            (-(1 - RationalCircle.Stage.dot
              (circleSamplePoint (2 * stage) (2 * k.1))
              (circleSamplePoint (2 * stage) (2 * k.1 + 1)))) :=
          Rat.mul_nonneg hneg hneg
        grind [Rat.neg_mul, Rat.mul_neg, Rat.neg_neg]
    rw [Rat.div_def]
    exact Rat.add_nonneg hcross (Rat.mul_nonneg hsq (by native_decide))
  have hcurvRight : 0 <= curvRight := by
    dsimp [curvRight, m, q', curvatureChordLower]
    have hcross : 0 <= RationalCircle.Stage.cross
        (circleSamplePoint (2 * stage) (2 * k.1 + 1))
        (circleSamplePoint (2 * stage) (2 * k.1 + 2)) := by
      exact Rat.le_of_lt
        (RationalCircle.Stage.samplePoint_cross_pos_adjacent
          (rationalCircleStage (2 * stage)) htwostage (2 * k.1 + 1))
    have hsq : 0 <= sq (1 - RationalCircle.Stage.dot
        (circleSamplePoint (2 * stage) (2 * k.1 + 1))
        (circleSamplePoint (2 * stage) (2 * k.1 + 2))) := by
      unfold sq
      by_cases h : 0 <= 1 - RationalCircle.Stage.dot
          (circleSamplePoint (2 * stage) (2 * k.1 + 1))
          (circleSamplePoint (2 * stage) (2 * k.1 + 2))
      · exact Rat.mul_nonneg h h
      · have hneg : 0 <= -(1 - RationalCircle.Stage.dot
            (circleSamplePoint (2 * stage) (2 * k.1 + 1))
            (circleSamplePoint (2 * stage) (2 * k.1 + 2))) := by grind
        have : 0 <= (-(1 - RationalCircle.Stage.dot
              (circleSamplePoint (2 * stage) (2 * k.1 + 1))
              (circleSamplePoint (2 * stage) (2 * k.1 + 2)))) *
            (-(1 - RationalCircle.Stage.dot
              (circleSamplePoint (2 * stage) (2 * k.1 + 1))
              (circleSamplePoint (2 * stage) (2 * k.1 + 2)))) :=
          Rat.mul_nonneg hneg hneg
        grind [Rat.neg_mul, Rat.mul_neg, Rat.neg_neg]
    rw [Rat.div_def]
    exact Rat.add_nonneg hcross (Rat.mul_nonneg hsq (by native_decide))
  have hsum : curvLeft + curvRight <= r := by
    dsimp [r]
    grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]
  have hr : 0 <= r := Rat.le_trans (Rat.add_nonneg hcurvLeft hcurvRight) hsum
  have hsq : sq (curvLeft + curvRight) <= sq r :=
    sq_le_sq_of_nonneg_le (Rat.add_nonneg hcurvLeft hcurvRight) hsum
  have hcoarse := adjacentCurvatureCertificates_refineSquaredChord
    stage k.1 hstage k.2
  dsimp [AdjacentChordSecantMarginCoversFineDyadicBudget, p, q, p', m, q', b,
    secantLeft, secantRight, r]
  exact ⟨hr, Rat.le_trans hcoarse hsq⟩

private theorem four_mul_add_five_le_two_pow_succ (n : Nat) (hn : 4 <= n) :
    4 * n + 5 <= 2 ^ (n + 1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  induction k with
  | zero => native_decide
  | succ k ih =>
    have hfour : 4 <= 2 ^ (4 + k + 1) := by
      have hpow : 2 ^ 2 <= 2 ^ (4 + k + 1) :=
        Nat.pow_le_pow_right (by omega : 0 < 2) (by omega)
      have htwo : 2 ^ 2 = 4 := by native_decide
      rw [htwo] at hpow
      exact hpow
    calc
      4 * (4 + (k + 1)) + 5 = (4 * (4 + k) + 5) + 4 := by omega
      _ <= 2 ^ (4 + k + 1) + 4 :=
        Nat.add_le_add_right (ih (by omega)) 4
      _ <= 2 ^ (4 + k + 1) + 2 ^ (4 + k + 1) :=
        Nat.add_le_add_left hfour _
      _ = 2 ^ (4 + (k + 1) + 1) := by
        rw [show 4 + (k + 1) + 1 = (4 + k + 1) + 1 by omega,
          Nat.pow_succ]
        omega

private theorem bisection_budget_denominator_bound (n : Nat) (hn : 4 <= n) :
    12288 * ((2 ^ n) * (2 ^ n) * (2 ^ n) * (2 ^ n)) <=
      2 ^ (2 * (2 ^ n) + 9) := by
  have hconst : 12288 <= 2 ^ 14 := by native_decide
  have hpow :
      (2 ^ n) * (2 ^ n) * (2 ^ n) * (2 ^ n) = 2 ^ (4 * n) := by
    calc
      (2 ^ n) * (2 ^ n) * (2 ^ n) * (2 ^ n) =
          (2 ^ n * 2 ^ n) * (2 ^ n * 2 ^ n) := by ac_rfl
      _ = 2 ^ (n + n) * 2 ^ (n + n) := by rw [← Nat.pow_add]
      _ = 2 ^ ((n + n) + (n + n)) := by rw [← Nat.pow_add]
      _ = 2 ^ (4 * n) := by congr 1 <;> omega
  have hlinear : 4 * n + 5 <= 2 * (2 ^ n) := by
    have h := four_mul_add_five_le_two_pow_succ n hn
    rw [Nat.pow_succ] at h
    omega
  have hexponent : 4 * n + 14 <= 2 * (2 ^ n) + 9 := by omega
  calc
    12288 * ((2 ^ n) * (2 ^ n) * (2 ^ n) * (2 ^ n)) <=
        2 ^ 14 * ((2 ^ n) * (2 ^ n) * (2 ^ n) * (2 ^ n)) :=
      Nat.mul_le_mul_right _ hconst
    _ = 2 ^ 14 * 2 ^ (4 * n) := by rw [hpow]
    _ = 2 ^ (4 * n + 14) := by
      rw [← Nat.pow_add]
      congr 1 <;> omega
    _ <= 2 ^ (2 * (2 ^ n) + 9) :=
      Nat.pow_le_pow_right (by omega : 0 < 2) hexponent

private theorem bisection_budget_le_fine_mesh_fourth
    (n : Nat) (hn : 4 <= n) :
    adjacentChordBisectionWidth (2 * (2 ^ n)) <=
      ((1 / ((2 * (2 ^ n) : Nat) : Rat)) *
        (1 / ((2 * (2 ^ n) : Nat) : Rat)) *
        (1 / ((2 * (2 ^ n) : Nat) : Rat)) *
        (1 / ((2 * (2 ^ n) : Nat) : Rat))) / 768 := by
  let A : Nat := 2 ^ (2 * (2 ^ n) + 9)
  let B : Nat := 12288 * ((2 ^ n) * (2 ^ n) * (2 ^ n) * (2 ^ n))
  have hnat : B <= A := by
    simpa [A, B] using bisection_budget_denominator_bound n hn
  have hA : 0 < A := by
    dsimp [A]
    exact Nat.pow_pos (by omega)
  have hB : 0 < B := by
    dsimp [B]
    exact Nat.mul_pos (by omega) (Nat.mul_pos (Nat.mul_pos
      (Nat.mul_pos (Nat.pow_pos (by omega)) (Nat.pow_pos (by omega)))
      (Nat.pow_pos (by omega))) (Nat.pow_pos (by omega)))
  have hrat : (B : Rat) <= (A : Rat) := by exact_mod_cast hnat
  have hinv : (1 : Rat) / (A : Rat) <= 1 / (B : Rat) := by
    apply Rat.le_of_mul_le_mul_right (c := (A : Rat) * (B : Rat))
    · rw [Rat.div_def]
      have hAne : (A : Rat) ≠ 0 := Rat.ne_of_gt ((Rat.natCast_pos).2 hA)
      have hBne : (B : Rat) ≠ 0 := Rat.ne_of_gt ((Rat.natCast_pos).2 hB)
      calc
        (1 * (A : Rat)⁻¹) * ((A : Rat) * (B : Rat)) = (B : Rat) := by
          grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
        _ <= (A : Rat) := hrat
        _ = (1 * (B : Rat)⁻¹) * ((A : Rat) * (B : Rat)) := by
          grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
    · exact Rat.mul_pos ((Rat.natCast_pos).2 hA) ((Rat.natCast_pos).2 hB)
  have hformula :
      ((1 / ((2 * (2 ^ n) : Nat) : Rat)) *
          (1 / ((2 * (2 ^ n) : Nat) : Rat)) *
          (1 / ((2 * (2 ^ n) : Nat) : Rat)) *
          (1 / ((2 * (2 ^ n) : Nat) : Rat))) / 768 =
        1 / (B : Rat) := by
    dsimp [B]
    simp only [Rat.natCast_mul, Rat.natCast_pow]
    grind [Rat.div_def, Rat.mul_assoc, Rat.mul_comm]
  unfold adjacentChordBisectionWidth
  change (1 : Rat) / (A : Rat) <= _
  rw [hformula]
  exact hinv
private theorem secant_budget_four : AdjacentChordSecantMarginCoversFineDyadicBudget 4 := by
  unfold AdjacentChordSecantMarginCoversFineDyadicBudget
  rw [Fin.forall_fin_succ]
  constructor
  · native_decide
  rw [Fin.forall_fin_succ]
  constructor
  · native_decide
  rw [Fin.forall_fin_succ]
  constructor
  · native_decide
  rw [Fin.forall_fin_succ]
  constructor
  · native_decide
  intro i
  exact Fin.elim0 i

private theorem secant_budget_eight : AdjacentChordSecantMarginCoversFineDyadicBudget 8 := by
  unfold AdjacentChordSecantMarginCoversFineDyadicBudget
  rw [Fin.forall_fin_succ]
  constructor
  · native_decide
  rw [Fin.forall_fin_succ]
  constructor
  · native_decide
  rw [Fin.forall_fin_succ]
  constructor
  · native_decide
  rw [Fin.forall_fin_succ]
  constructor
  · native_decide
  rw [Fin.forall_fin_succ]
  constructor
  · native_decide
  rw [Fin.forall_fin_succ]
  constructor
  · native_decide
  rw [Fin.forall_fin_succ]
  constructor
  · native_decide
  rw [Fin.forall_fin_succ]
  constructor
  · native_decide
  intro i
  exact Fin.elim0 i
/-- The explicit secant budget proves the local chord refinement at every dyadic stage. -/
theorem innerChordLowerRefinement : InnerChordLowerRefinement := by
  intro n
  cases n with
  | zero =>
    simpa [piStage] using adjacentChordLowerRefinesByDoubling_one
  | succ n =>
    cases n with
    | zero =>
      simpa [piStage] using adjacentChordLowerRefinesByDoubling_two
    | succ n =>
      cases n with
      | zero =>
        have hmargin := adjacentChordSecantMargin_of_fineDyadicBudget 4
          (by native_decide) secant_budget_four
        simpa [piStage] using
          (adjacentChordLowerRefinesByDoubling_of_secantMargin 4
            (by native_decide) hmargin)
      | succ n =>
        cases n with
        | zero =>
          have hmargin := adjacentChordSecantMargin_of_fineDyadicBudget 8
            (by native_decide) secant_budget_eight
          simpa [piStage] using
            (adjacentChordLowerRefinesByDoubling_of_secantMargin 8
              (by native_decide) hmargin)
        | succ n =>
          have hbudget := secant_margin_of_bisection_budget
            (piStage (n + 4)) (piStage_pos (n + 4))
            (by simpa [piStage] using
              bisection_budget_le_fine_mesh_fourth (n + 4) (by omega))
          have hmargin := adjacentChordSecantMargin_of_fineDyadicBudget
            (piStage (n + 4)) (piStage_pos (n + 4)) hbudget
          exact adjacentChordLowerRefinesByDoubling_of_secantMargin
            (piStage (n + 4)) (piStage_pos (n + 4)) hmargin

/-- The original square-root chord-path circumference evaluator is a valid
computable real.  The finite stages 1, 2, 4, and 8 are checked by exact
rational normalization; the remaining dyadic stages follow from the uniform
secant-versus-curvature budget above. -/
theorem piCircumference_valid : piCircumference.Valid :=
  circumferenceValid_of_quarterLengthStepRefines
    (circumferenceQuarterLengthStepRefines_of_adjacentChordLowerRefinement
      innerChordLowerRefinement)

/-- Every direct circumference box is nonnegative and remains below the exact
stage-zero outer bound four.  This makes the path evaluator usable in
nonlinear constructions such as the Basel right-hand side. -/
theorem piCircumference_nonneg_bounded_by_four (n : Nat) :
    0 <= (piCircumference.compute n).lo ∧
      (piCircumference.compute n).hi <= 4 := by
  constructor
  · rw [piCircumference_compute_eq,
      piCircumferenceComputeAtStage_eq_common]
    simp only [piCircumferenceCommonComputeAtStage]
    have hinner := rationalPointPathLength_lo_nonneg
      (innerBoundary (piStage n)) (piStage n)
    change 0 <= (4 * (innerQuarterLength (piStage n)).lo) / 2
    rw [Rat.div_def]
    exact Rat.mul_nonneg
      (Rat.mul_nonneg (by native_decide) hinner)
      (by native_decide)
  · have hnest := piCircumference_valid.2.1 0 n (Nat.zero_le n)
    have hzero : (piCircumference.compute 0).hi = 4 := by
      native_decide
    simpa [hzero] using hnest.2.2

/-- The now-validated original chord-path evaluator agrees with the area
construction of pi by the finite Archimedean comparison. -/
theorem piCircumferenceDirect_equiv_piCircleArea :
    piCircumference.Equiv piCircleArea :=
  piCircumference_equiv_piCircleArea_of_verified_area_polygon

/-- The original square-root chord path and the default cross-fan
circumference evaluator are interchangeable certified geometric
computations.  The bridge is through their separately proved finite
Archimedean comparisons with the area loop. -/
theorem piCircumferenceDirect_equiv_piCircumferenceFan :
    piCircumference.Equiv piCircumferenceFan :=
  RealRaw.equiv_trans
    piCircumference_valid
    (by simpa [AreaValid] using AreaLoopValidity.areaValid)
    piCircumferenceFan_valid
    piCircumferenceDirect_equiv_piCircleArea
    (RealRaw.equiv_symm piCircumferenceFan_equiv_piCircleArea)

/-- A certified handle for the original chord-path circumference computation. -/
def piCircumferenceDirect : Real :=
  Real.ofRaw piCircumference piCircumference_valid

namespace pi

/-- The original square-root chord-path computation as a named representation
of the abstract certified value of pi.  It is kept separate from the
cross-fan default `pi.circumference` so a downstream theorem can select the
literal path-length evaluator explicitly. -/
def circumferenceDirect : Real.Representation value where
  raw := piCircumference
  valid := piCircumference_valid
  agrees := piCircumferenceDirect_equiv_piCircleArea

/-- Selecting the original chord path or the area loop from the abstract pi
handle gives equivalent certified raw computations. -/
theorem circumferenceDirect_equiv_circleArea :
    circumferenceDirect.raw.Equiv circleArea.raw :=
  representations_equiv circumferenceDirect circleArea

/-- The two named circumference views select equivalent certified raw
algorithms: the original chord-path computation and the default cross-fan
computation. -/
theorem circumferenceDirect_equiv_circumference :
    circumferenceDirect.raw.Equiv circumference.raw :=
  representations_equiv circumferenceDirect circumference

end pi
end PiProofs

end ComputableAnalysis
