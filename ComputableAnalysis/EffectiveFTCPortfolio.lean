import ComputableAnalysis.ArctanEffectiveFTC
import ComputableAnalysis.ExpProofs
import ComputableAnalysis.FiniteSinePrefixFTC
import ComputableAnalysis.FiniteFTCIntervalRegular
import ComputableAnalysis.FiniteFTCQuartic
import ComputableAnalysis.SinPiSquareFTC
import ComputableAnalysis.TangentPullbackEffectiveFTC

/-!
# Auditable effective-FTC portfolio

This module records the concrete certificates that currently form the
effective-FTC ladder.  It is intentionally a bundle of theorem statements,
not a claim that every continuous function is integrable: each field is backed
by a finite rational interval certificate in the imported module.

The nested-radical `sin^2` transport is not included in the completed bundle;
its unfinished endpoint bridge is tracked in `SinPiSquareFTC.lean`.
-/

namespace ComputableAnalysis

def ratNatListSum (f : Nat -> Rat) : List Nat -> Rat
  | [] => 0
  | k :: xs => f k + ratNatListSum f xs

theorem rat_list_sum_pair_error
    (xs : List Nat) (left endpoint width : Nat -> Rat)
    (hwidth : forall k, k ∈ xs ->
      endpoint k - width k <= left k /\
      left k <= endpoint k + width k) :
    ratNatListSum endpoint xs - ratNatListSum width xs <= ratNatListSum left xs /\
      ratNatListSum left xs <= ratNatListSum endpoint xs + ratNatListSum width xs := by
  induction xs with
  | nil =>
      simp [ratNatListSum]
      native_decide
  | cons k xs ih =>
      have hk := hwidth k (by simp)
      have hrest := ih (fun j hj => hwidth j (by simp [hj]))
      simp only [ratNatListSum]
      constructor <;> grind [Rat.sub_eq_add_neg, Rat.add_assoc,
        Rat.add_comm, Rat.add_left_comm]

/-! A parameterized affine calibration for the portfolio.

This is deliberately stated at the interval-regular/raw level: the
construction is an executable rational monotone integral, and the endpoint
value is itself a rational raw.  It supplies the linear rung that the
monomial examples use implicitly, without importing completed real numbers.
-/
theorem affine_signed_unitSlope_integral_equiv
    (r c a b : Rat) (hrneg : -1 <= r) (hrpos : r <= 1) :
    (Integral.raw
      (FunctionOnInterval.exactRat (fun x : Rat => r * x + c) a b)
      (Integral.exactRat_affine_signed_unitSlope r c a b hrneg hrpos)).Equiv
      (RealRaw.ofRat ((b - a) * (r * (a + b) / 2 + c))) := by
  rw [Integral.exactRat_affine_signed_unitSlope_raw_eq_ofRat]
  exact RealRaw.ofRat_equiv_self _

theorem piCircleArea_compute_lo_nonneg (n : Nat) :
    0 <= (piCircleArea.compute n).lo := by
  rw [← ArctanGeometry.four_arctanGeom_one_compute_eq_piCircleArea_compute n]
  change 0 <=
    ((RealRaw.scaleRat (4 : Rat)
      (ArctanGeometry.arctanGeom (1 : Rat))).compute n).lo
  unfold RealRaw.scaleRat RealRaw.scaleRatCompute
  simp only [if_pos (by native_decide : (0 : Rat) <= 4)]
  rw [ArctanGeometry.arctanGeom_one_compute_eq n]
  unfold ArctanGeometry.positiveLoopComputeAtStage
  change 0 <= 4 * (ArctanGeometry.arctanAreaLoopState 1 n).lo
  rw [ArctanGeometry.arctanAreaLoopState_lo_eq_geometricLowerSum]
  exact Rat.mul_nonneg (by native_decide)
    (ArctanGeometry.geometricLowerSum_nonneg _
        (ArctanGeometry.arctanAreaLoopState_intervals_nonnegative
          (by native_decide) n))

theorem piCircleArea_compute_lo_ge_two (n : Nat) :
    2 <= (piCircleArea.compute n).lo := by
  rw [← ArctanGeometry.four_arctanGeom_one_compute_eq_piCircleArea_compute n]
  change 2 <=
    ((RealRaw.scaleRat (4 : Rat)
      (ArctanGeometry.arctanGeom (1 : Rat))).compute n).lo
  unfold RealRaw.scaleRat RealRaw.scaleRatCompute
  simp only [if_pos (by native_decide : (0 : Rat) <= 4)]
  rw [ArctanGeometry.arctanGeom_one_compute_eq n]
  unfold ArctanGeometry.positiveLoopComputeAtStage
  change 2 <= 4 * (ArctanGeometry.arctanAreaLoopState 1 n).lo
  rw [ArctanGeometry.arctanAreaLoopState_lo_eq_geometricLowerSum]
  have hnest := ArctanGeometry.positiveLoopComputeAtStage_nested
    (x := (1 : Rat)) (by native_decide) 0 n (Nat.zero_le n)
  have hzero :
      (ArctanGeometry.positiveLoopComputeAtStage (1 : Rat) 0).lo =
        (1 / 2 : Rat) := by
    native_decide
  have hbase : (1 / 2 : Rat) <=
      (ArctanGeometry.positiveLoopComputeAtStage (1 : Rat) n).lo := by
    rw [← hzero]
    exact hnest.1
  unfold ArctanGeometry.positiveLoopComputeAtStage at hbase
  change (1 / 2 : Rat) <=
      (ArctanGeometry.arctanAreaLoopState 1 n).lo at hbase
  rw [ArctanGeometry.arctanAreaLoopState_lo_eq_geometricLowerSum] at hbase
  grind

set_option maxHeartbeats 1000000 in
theorem reciprocalPi_quarterTurn_equiv_quarter :
    (SinPiIntegral.reciprocalPiRaw *
      RationalCircle.GeometricTrig.halfQuarterTurnRaw (1 : Rat)).Equiv
      (RealRaw.ofRat (1 / 4)) := by
  intro n
  apply (RealRaw.compareAt_overlap_iff
    (SinPiIntegral.reciprocalPiRaw *
      RationalCircle.GeometricTrig.halfQuarterTurnRaw (1 : Rat))
    (RealRaw.ofRat (1 / 4)) n n).2
  change QInterval.Overlaps
    (QBox.mulRealInterval
      (SinPiIntegral.reciprocalPiRaw.compute n).lo
      (SinPiIntegral.reciprocalPiRaw.compute n).hi
      ((RationalCircle.GeometricTrig.halfQuarterTurnRaw
        (1 : Rat)).compute n).lo
      ((RationalCircle.GeometricTrig.halfQuarterTurnRaw
        (1 : Rat)).compute n).hi)
    ({ lo := 1 / 4, hi := 1 / 4 } : QInterval)
  have hrecip_compute :
      SinPiIntegral.reciprocalPiRaw.compute n =
        QInterval.inv (piCircleArea.compute n) := by rfl
  have hquarter_compute :
      (RationalCircle.GeometricTrig.halfQuarterTurnRaw
        (1 : Rat)).compute n =
        ({ lo := (1 : Rat) / 4 * (piCircleArea.compute n).lo,
           hi := (1 : Rat) / 4 * (piCircleArea.compute n).hi } : QInterval) := by
    unfold RationalCircle.GeometricTrig.halfQuarterTurnRaw
      RealRaw.scaleRat RealRaw.scaleRatCompute
    simp only [if_pos (by native_decide : (0 : Rat) <= (1 : Rat) / 4)]
  rw [hrecip_compute, hquarter_compute]
  have hPorder := RealRaw.interval_order_of_valid piCircleArea
    CauchyPi.piCircleArea_valid n
  have hPlo : 0 < (piCircleArea.compute n).lo := by
    have h := piCircleArea_compute_lo_ge_two n
    grind
  have hPhi : 0 < (piCircleArea.compute n).hi := by grind
  have hone_div_antitone : ∀ {a b : Rat}, 0 < a -> a <= b ->
      1 / b <= 1 / a := by
    intro a b ha hab
    apply Rat.le_of_mul_le_mul_right (c := a * b)
    · rw [Rat.div_def]
      have hane : a ≠ 0 := Rat.ne_of_gt ha
      have hbne : b ≠ 0 := Rat.ne_of_gt (by grind)
      calc
        1 * b⁻¹ * (a * b) = a := by
          grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel _ hbne]
        _ <= b := hab
        _ = (1 * a⁻¹) * (a * b) := by
          grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel _ hane]
    · exact Rat.mul_pos ha (by grind)
  have hinvnonneg : 0 <= (QInterval.inv (piCircleArea.compute n)).lo := by
    rw [show QInterval.inv (piCircleArea.compute n) =
        { lo := 1 / (piCircleArea.compute n).hi,
          hi := 1 / (piCircleArea.compute n).lo } by
      simp [QInterval.inv, hPlo]]
    rw [Rat.div_def]
    exact Rat.le_of_lt (Rat.mul_pos (by native_decide)
      ((Rat.inv_pos).2 hPhi))
  have hinvorder :
      (QInterval.inv (piCircleArea.compute n)).lo <=
        (QInterval.inv (piCircleArea.compute n)).hi := by
    rw [show QInterval.inv (piCircleArea.compute n) =
        { lo := 1 / (piCircleArea.compute n).hi,
          hi := 1 / (piCircleArea.compute n).lo } by
      simp [QInterval.inv, hPlo]]
    exact hone_div_antitone hPlo hPorder
  have hscale_nonneg : 0 <= (1 / 4 : Rat) *
      (piCircleArea.compute n).lo := by
    exact Rat.mul_nonneg (by native_decide)
      (Rat.le_of_lt hPlo)
  have hscale_order : (1 / 4 : Rat) *
      (piCircleArea.compute n).lo <= (1 / 4 : Rat) *
      (piCircleArea.compute n).hi := by
    exact Rat.mul_le_mul_of_nonneg_left hPorder (by native_decide)
  rw [QBox.mulRealInterval_of_nonneg hinvnonneg hinvorder
    hscale_nonneg hscale_order]
  unfold QInterval.Overlaps
  simp [QInterval.inv, hPlo, hPorder, hPhi]
  constructor
  · apply Rat.le_of_mul_le_mul_right (c := (piCircleArea.compute n).hi)
    · rw [Rat.div_def]
      have hhi_ne : (piCircleArea.compute n).hi ≠ 0 := Rat.ne_of_gt hPhi
      calc
        (1 * (piCircleArea.compute n).hi⁻¹ *
            (1 / 4 * (piCircleArea.compute n).lo)) *
            (piCircleArea.compute n).hi =
            (1 / 4 : Rat) * (piCircleArea.compute n).lo := by
              grind [Rat.mul_assoc, Rat.mul_comm,
                Rat.mul_inv_cancel _ hhi_ne]
        _ <= (1 / 4 : Rat) * (piCircleArea.compute n).hi :=
          hscale_order
    · exact hPhi
  · apply Rat.le_of_mul_le_mul_right (c := (piCircleArea.compute n).lo)
    · rw [Rat.div_def]
      have hlo_ne : (piCircleArea.compute n).lo ≠ 0 := Rat.ne_of_gt hPlo
      calc
        (1 / 4 : Rat) * (piCircleArea.compute n).lo =
            (1 / 4 : Rat) * (1 * (piCircleArea.compute n).lo) := by simp
        _ <= (1 * (piCircleArea.compute n).lo⁻¹ *
            (1 / 4 * (piCircleArea.compute n).hi) ) *
            (piCircleArea.compute n).lo := by
              grind [Rat.mul_assoc, Rat.mul_comm,
                Rat.mul_inv_cancel _ hlo_ne]
    · exact hPlo

theorem nestedRadicalSquare_tangent_stage_zero_overlap :
    QInterval.Overlaps
      (SinPiIntegral.dyadicNestedRadicalSquareLeftSum 0)
      (SinPiIntegral.tangentSquareIntegral.compute 0) := by
  unfold SinPiIntegral.dyadicNestedRadicalSquareLeftSum
  rw [SinPiIntegral.tangentSquareIntegral_compute]
  unfold QInterval.Overlaps
  native_decide

theorem nestedRadicalSquare_tangent_stage_one_overlap :
    QInterval.Overlaps
      (SinPiIntegral.dyadicNestedRadicalSquareLeftSum 1)
      (SinPiIntegral.tangentSquareIntegral.compute 1) := by
  unfold SinPiIntegral.dyadicNestedRadicalSquareLeftSum
  rw [SinPiIntegral.tangentSquareIntegral_compute]
  unfold QInterval.Overlaps
  native_decide

theorem nestedRadicalSquare_tangent_stage_two_overlap :
    QInterval.Overlaps
      (SinPiIntegral.dyadicNestedRadicalSquareLeftSum 2)
      (SinPiIntegral.tangentSquareIntegral.compute 2) := by
  unfold SinPiIntegral.dyadicNestedRadicalSquareLeftSum
  rw [SinPiIntegral.tangentSquareIntegral_compute]
  unfold QInterval.Overlaps
  native_decide

theorem tangentSquareCellControl_left_rectangle_contained
    (C : RationalSubinterval 0 1) (δ η : QPos) (N : Nat)
    (hC : 0 < C.width) (hη : η.val = C.width * δ.val / 3)
    (hN : 256 * (η.val.den + 1) <= N) :
    (C.scaleBound
      ((SinPiIntegral.tangentSquareCombinedDerivativeCellControl
        C δ η N hC hη hN).bound 0)).ContainsInterval
      (C.scaleBound
        ({ lo := SinPiIntegral.tangentSquareDensity C.lower,
           hi := SinPiIntegral.tangentSquareDensity C.lower } : QInterval)) := by
  let H := SinPiIntegral.tangentSquareCombinedDerivativeCellControl
    C δ η N hC hη hN
  have hcontains := H.candidate_contained 0 C.lower
    (by exact ⟨Rat.le_refl, C.ordered⟩)
  have heval : H.derivativeEvalPrecision 0 = 0 := by rfl
  rw [heval,
    SinPiIntegral.tangentSquareCombinedDerivativeRaw_compute_eq_density
    (x := C.lower) C.lower_mem (Rat.le_trans C.ordered C.upper_mem) 0] at hcontains
  change (QInterval.scaleByRat C.width (H.bound 0)).ContainsInterval
    (QInterval.scaleByRat C.width
      ({ lo := SinPiIntegral.tangentSquareDensity C.lower,
         hi := SinPiIntegral.tangentSquareDensity C.lower } : QInterval))
  exact QInterval.scaleByRat_contains_of_nonneg
    (Rat.le_of_lt hC) hcontains

theorem tangentSquareCellControl_left_and_endpoint_share_bound
    (C : RationalSubinterval 0 1) (δ η : QPos) (N : Nat)
    (hC : 0 < C.width) (hη : η.val = C.width * δ.val / 3)
    (hN : 256 * (η.val.den + 1) <= N) :
    let H := SinPiIntegral.tangentSquareCombinedDerivativeCellControl
      C δ η N hC hη hN
    (C.scaleBound (H.bound 0)).ContainsInterval
        (C.scaleBound
          ({ lo := SinPiIntegral.tangentSquareDensity C.lower,
             hi := SinPiIntegral.tangentSquareDensity C.lower } : QInterval)) /\
      (C.scaleBound (H.bound 0)).ContainsInterval
        (endpointDifferenceInterval
          (RealFunRaw.add Integral.arctanPrimitiveRaw
            SinPiIntegral.tangentSquareCorrectionRaw)
          C.lower C.upper N) := by
  dsimp
  constructor
  · exact tangentSquareCellControl_left_rectangle_contained C δ η N hC hη hN
  · exact (SinPiIntegral.tangentSquareCombinedDerivativeCellControl
      C δ η N hC hη hN).endpoint_difference_contained 0

def effectiveFTCIntervalFold (term : Nat -> QInterval) (xs : List Nat) : QInterval :=
  xs.foldl (fun acc k => QInterval.addInterval acc (term k))
    { lo := 0, hi := 0 }

theorem effectiveFTCIntervalFold_contains
    (xs : List Nat) (bound left endpoint : Nat -> QInterval)
    (hleft : forall k,
      (bound k).ContainsInterval (left k))
    (hendpoint : forall k,
      (bound k).ContainsInterval (endpoint k)) :
    (effectiveFTCIntervalFold bound xs).ContainsInterval
        (effectiveFTCIntervalFold left xs) /\
      (effectiveFTCIntervalFold bound xs).ContainsInterval
        (effectiveFTCIntervalFold endpoint xs) := by
  constructor
  · unfold effectiveFTCIntervalFold
    apply RationalPartition.addInterval_fold_contains xs bound left
      (QInterval.containsInterval_refl _)
    intro k
    exact hleft k
  · unfold effectiveFTCIntervalFold
    apply RationalPartition.addInterval_fold_contains xs bound endpoint
      (QInterval.containsInterval_refl _)
    intro k
    exact hendpoint k

theorem effectiveFTCIntervalFold_width
    (term : Nat -> QInterval) (xs : List Nat) :
    (effectiveFTCIntervalFold term xs).width =
      ratNatListSum (fun k => (term k).width) xs := by
  unfold effectiveFTCIntervalFold
  rw [RationalPartition.addInterval_fold_width]
  have hfold (f : Nat -> Rat) (ys : List Nat) :
      ys.foldl (fun total k => total + f k) 0 = ratNatListSum f ys := by
    induction ys with
    | nil => rfl
    | cons k ys ih =>
        simp only [List.foldl, ratNatListSum]
        rw [RationalPartition.rat_add_fold_initial]
        rw [ih]
        grind
  rw [hfold]
  have hzero : ({ lo := 0, hi := 0 } : QInterval).width = 0 := by
    unfold QInterval.width
    grind
  rw [hzero]
  grind

theorem squareEffectiveFTC_endpointRaw_valid :
    (Integral.squareEffectiveFTCData.toDerivativeBoundFTC.endpointRaw).Valid := by
  have heq :
      (fun n => endpointDifferenceCompute Integral.squarePrimitiveRaw 0 1
        (Integral.squareEffectiveFTCData.toDerivativeBoundFTC.chooseEndpointPrecision
          (precisionAtStage n))) =
      (fun _ => ({ lo := 1, hi := 1 } : QInterval)) := by
    funext n
    simp [Integral.squareEffectiveFTCData,
      DerivativeBoundFTC.endpointRaw, DerivativeBoundFTC.endpointCompute,
      Integral.squarePrimitiveRaw, RealFunRaw.exact,
      endpointDifferenceCompute, endpointDifferenceInterval]
    native_decide

  change RealRaw.ValidCompute
    (fun n => endpointDifferenceCompute Integral.squarePrimitiveRaw 0 1
      (Integral.squareEffectiveFTCData.toDerivativeBoundFTC.chooseEndpointPrecision
        (precisionAtStage n)))
  rw [heq]
  unfold RealRaw.ValidCompute
  constructor
  · intro n
    simp [QInterval.width] <;> grind
  constructor
  · intro n m hnm
    simp
  · intro eps
    refine ⟨0, ?_⟩
    intro n hn
    simp [QInterval.width] <;> grind

theorem cubeEffectiveFTC_endpointRaw_valid :
    (Integral.cubeEffectiveFTCData.toDerivativeBoundFTC.endpointRaw).Valid := by
  have heq :
      (fun n => endpointDifferenceCompute Integral.cubePrimitiveRaw 0 1
        (Integral.cubeEffectiveFTCData.toDerivativeBoundFTC.chooseEndpointPrecision
          (precisionAtStage n))) =
      (fun _ => ({ lo := 1, hi := 1 } : QInterval)) := by
    funext n
    simp [Integral.cubeEffectiveFTCData,
      DerivativeBoundFTC.endpointRaw, DerivativeBoundFTC.endpointCompute,
      Integral.cubePrimitiveRaw, RealFunRaw.exact,
      endpointDifferenceCompute, endpointDifferenceInterval]
    native_decide
  change RealRaw.ValidCompute
    (fun n => endpointDifferenceCompute Integral.cubePrimitiveRaw 0 1
      (Integral.cubeEffectiveFTCData.toDerivativeBoundFTC.chooseEndpointPrecision
        (precisionAtStage n)))
  rw [heq]
  unfold RealRaw.ValidCompute
  constructor
  · intro n
    simp [QInterval.width] <;> grind
  constructor
  · intro n m hnm
    simp
  · intro eps
    refine ⟨0, ?_⟩
    intro n hn
    simp [QInterval.width] <;> grind

structure EffectiveFTCPortfolio where
  square_value :
    (Integral.raw
      (FunctionOnInterval.exactRat (fun x : Rat => x * x) 0 1)
      Integral.exactRat_square_integral_certificate).Equiv
      (RealRaw.ofRat (1 / 3))
  square_effective_value :
    Integral.squareEffectiveFTCData.toDerivativeBoundFTC.boundedIntegralRaw.Equiv
      (RealRaw.ofRat 1)
  cube_effective_value :
    Integral.cubeEffectiveFTCData.toDerivativeBoundFTC.boundedIntegralRaw.Equiv
      (RealRaw.ofRat 1)
  quartic_effective_value :
    Integral.quarticIntegralEffectiveFTCData.toDerivativeBoundFTC.boundedIntegralRaw.Equiv
      (RealRaw.ofRat (1 / 5))
  sine_prefix_square_value :
    FiniteSinePrefix.sineTaylorPrefixThreeSquareEffectiveFTCData.toDerivativeBoundFTC.boundedIntegralRaw.Equiv
      (RealRaw.ofRat (6389 / 161280))
  tangent_pullback_value :
    SinPiIntegral.tangentPullbackIntegral.Equiv (RealRaw.ofRat 1)
  cube_value :
    (Integral.raw
      (FunctionOnInterval.exactRat (fun x : Rat => x ^ 3) 0 1)
      Integral.exactRat_cube_integral_certificate).Equiv
      (RealRaw.ofRat (1 / 4))
  quartic_value :
    (Integral.raw
      (FunctionOnInterval.exactRat (fun x : Rat => x ^ 4) 0 1)
      Integral.exactRat_quartic_integral_certificate).Equiv
      (RealRaw.ofRat (1 / 5))
  fifth_value :
    Integral.fifthIntegralEffectiveFTCData.toDerivativeBoundFTC.boundedIntegralRaw.Equiv
      (RealRaw.ofRat (1 / 6))
  square :
    (Integral.squareEffectiveFTCData.toDerivativeBoundFTC.boundedIntegralRaw).Equiv
      Integral.squareEffectiveFTCData.toDerivativeBoundFTC.endpointRaw
  cube :
    (Integral.cubeEffectiveFTCData.toDerivativeBoundFTC.boundedIntegralRaw).Equiv
      Integral.cubeEffectiveFTCData.toDerivativeBoundFTC.endpointRaw
  quartic :
    (Integral.quarticEffectiveFTCData.toDerivativeBoundFTC.boundedIntegralRaw).Equiv
      Integral.quarticEffectiveFTCData.toDerivativeBoundFTC.endpointRaw
  fifth :
    (Integral.fifthIntegralEffectiveFTCData.toDerivativeBoundFTC.boundedIntegralRaw).Equiv
      Integral.fifthIntegralEffectiveFTCData.toDerivativeBoundFTC.endpointRaw
  arctan :
    (Integral.arctanEffectiveFTCData.toDerivativeBoundFTC.boundedIntegralRaw).Equiv
      Integral.arctanEffectiveFTCData.toDerivativeBoundFTC.endpointRaw
  tangentPullback :
    SinPiIntegral.tangentPullbackCandidateFTCData.toDerivativeBoundFTC.boundedIntegralRaw.Equiv
      SinPiIntegral.tangentPullbackCandidateFTCData.toDerivativeBoundFTC.endpointRaw
  tangentSquareEffective :
    SinPiIntegral.tangentSquareEffectiveIntegralRaw.Equiv
      SinPiIntegral.tangentSquareEffectiveCandidateFTC.toDerivativeBoundFTC.endpointRaw
  tangentSquareEndpoint :
    (endpointDifferenceRaw SinPiIntegral.tangentSquareEffectivePrimitiveOnUnit 0 1
      SinPiIntegral.tangentSquareEffectivePrimitive_endpointDifference_valid).Equiv
      (RationalCircle.GeometricTrig.halfQuarterTurnRaw (1 : Rat))
  sinePrefixSquare :
    FiniteSinePrefix.sineTaylorPrefixThreeSquareEffectiveFTCData.toDerivativeBoundFTC.boundedIntegralRaw.Equiv
      FiniteSinePrefix.sineTaylorPrefixThreeSquareEffectiveFTCData.toDerivativeBoundFTC.endpointRaw
  exponential :
    (ExpProofs.uniformExpOnUnit_selectedStageFTCIndexed.toSelected.boundedIntegralRaw).Equiv
      ExpProofs.uniformExpOnUnit_selectedStageFTCIndexed.toSelected.endpointRaw

/- The raw `tangentSquareIntegral` is unscaled: its natural endpoint is the
   quarter-turn raw.  The rational `1/4` target below is retained only as a
   provisional contract for the normalized reciprocal-pi product; it must not
   be read as a value theorem for the unscaled chart integral. -/
structure TangentSquareIntegralValueSubgoal where
  lower_contains :
    forall n, (SinPiIntegral.tangentSquareIntegral.compute n).lo <= (1 / 4 : Rat)
  upper_contains :
    forall n, (1 / 4 : Rat) <= (SinPiIntegral.tangentSquareIntegral.compute n).hi

def normalizedTangentSquareIntegral : RealRaw :=
  SinPiIntegral.reciprocalPiRaw * SinPiIntegral.tangentSquareIntegral

structure NormalizedTangentSquareValueSubgoal where
  normalized_valid : normalizedTangentSquareIntegral.Valid
  anchor_valid :
    (SinPiIntegral.reciprocalPiRaw *
      RationalCircle.GeometricTrig.halfQuarterTurnRaw (1 : Rat)).Valid
  chart_transport :
    normalizedTangentSquareIntegral.Equiv
      (SinPiIntegral.reciprocalPiRaw *
        RationalCircle.GeometricTrig.halfQuarterTurnRaw (1 : Rat))

/-! The correctly scaled transport obligation for the genuine `sin²` target.
The equal-dyadic integral is in the original `x` variable, whereas the
tangent-chart integral is in `u`; the Jacobian contributes `1/pi`.  Thus the
finite overlap must be against `normalizedTangentSquareIntegral`, not the
unscaled chart integral. -/
structure NormalizedTangentSquareCommonWitness where
  witness : Nat -> Rat
  candidate_lo_le : forall n,
    (SinPiIntegral.dyadicNestedRadicalSquareLeftSum n).lo <= witness n
  witness_le_candidate_hi : forall n,
    witness n <= (SinPiIntegral.dyadicNestedRadicalSquareLeftSum n).hi
  normalized_lo_le : forall n,
    (normalizedTangentSquareIntegral.compute n).lo <= witness n
  witness_le_normalized_hi : forall n,
    witness n <= (normalizedTangentSquareIntegral.compute n).hi

theorem NormalizedTangentSquareCommonWitness.to_equiv
    (H : NormalizedTangentSquareCommonWitness) :
    SinPiIntegral.dyadicNestedRadicalSquareIntegralRaw.Equiv
      normalizedTangentSquareIntegral := by
  apply SinPiIntegral.dyadicNestedRadicalSquareIntegralRaw_equiv_of_overlap
  intro n
  unfold QInterval.Overlaps
  exact ⟨Rat.le_trans (H.candidate_lo_le n)
      (H.witness_le_normalized_hi n),
    Rat.le_trans (H.normalized_lo_le n)
      (H.witness_le_candidate_hi n)⟩

/-! A signed product cannot use the nonnegative-product shortcut at coarse
stages.  This certificate exposes exactly the three obligations required by
`RealRaw.Valid`, rather than assuming a convergence theorem for multiplication.
-/
structure SignedRawProductValiditySubgoal (x y : RealRaw) where
  ordered : forall n, 0 <= ((x * y).compute n).width
  nested : forall n m, n <= m ->
    ((x * y).compute n).lo <= ((x * y).compute m).lo /\
    ((x * y).compute m).lo <= ((x * y).compute m).hi /\
    ((x * y).compute m).hi <= ((x * y).compute n).hi
  widths_shrink : RealRaw.WidthsShrinkToZero (x * y).compute

theorem SignedRawProductValiditySubgoal.valid
    {x y : RealRaw} (H : SignedRawProductValiditySubgoal x y) :
    (x * y).Valid := by
  exact ⟨H.ordered, H.nested, H.widths_shrink⟩

theorem normalizedTangentSquareProduct_ordered (n : Nat) :
    0 <= (normalizedTangentSquareIntegral.compute n).width := by
  change 0 <= (QBox.mulRealInterval
    (SinPiIntegral.reciprocalPiRaw.compute n).lo
    (SinPiIntegral.reciprocalPiRaw.compute n).hi
    (SinPiIntegral.tangentSquareIntegral.compute n).lo
    (SinPiIntegral.tangentSquareIntegral.compute n).hi).width
  have hrecip := RealRaw.interval_order_of_valid
    SinPiIntegral.reciprocalPiRaw SinPiIntegral.reciprocalPiRaw_valid n
  have htangent := RealRaw.interval_order_of_valid
    SinPiIntegral.tangentSquareIntegral SinPiIntegral.tangentSquareIntegral_valid n
  have h := QBox.mulRealInterval_ordered
    (a := (SinPiIntegral.reciprocalPiRaw.compute n).lo)
    (b := (SinPiIntegral.reciprocalPiRaw.compute n).hi)
    (c := (SinPiIntegral.tangentSquareIntegral.compute n).lo)
    (d := (SinPiIntegral.tangentSquareIntegral.compute n).hi) hrecip htangent
  unfold QInterval.width
  grind

theorem normalizedTangentSquareProduct_nested (n m : Nat) (hnm : n <= m) :
    (normalizedTangentSquareIntegral.compute n).lo <=
        (normalizedTangentSquareIntegral.compute m).lo /\
      (normalizedTangentSquareIntegral.compute m).lo <=
        (normalizedTangentSquareIntegral.compute m).hi /\
      (normalizedTangentSquareIntegral.compute m).hi <=
        (normalizedTangentSquareIntegral.compute n).hi := by
  have hrecip := SinPiIntegral.reciprocalPiRaw_valid.2.1 n m hnm
  have htangent := SinPiIntegral.tangentSquareIntegral_valid.2.1 n m hnm
  change (QBox.mulRealInterval
      (SinPiIntegral.reciprocalPiRaw.compute n).lo
      (SinPiIntegral.reciprocalPiRaw.compute n).hi
      (SinPiIntegral.tangentSquareIntegral.compute n).lo
      (SinPiIntegral.tangentSquareIntegral.compute n).hi).lo <=
      (QBox.mulRealInterval
        (SinPiIntegral.reciprocalPiRaw.compute m).lo
        (SinPiIntegral.reciprocalPiRaw.compute m).hi
        (SinPiIntegral.tangentSquareIntegral.compute m).lo
        (SinPiIntegral.tangentSquareIntegral.compute m).hi).lo /\
    (QBox.mulRealInterval
        (SinPiIntegral.reciprocalPiRaw.compute m).lo
        (SinPiIntegral.reciprocalPiRaw.compute m).hi
        (SinPiIntegral.tangentSquareIntegral.compute m).lo
        (SinPiIntegral.tangentSquareIntegral.compute m).hi).lo <=
      (QBox.mulRealInterval
        (SinPiIntegral.reciprocalPiRaw.compute m).lo
        (SinPiIntegral.reciprocalPiRaw.compute m).hi
        (SinPiIntegral.tangentSquareIntegral.compute m).lo
        (SinPiIntegral.tangentSquareIntegral.compute m).hi).hi /\
    (QBox.mulRealInterval
        (SinPiIntegral.reciprocalPiRaw.compute m).lo
        (SinPiIntegral.reciprocalPiRaw.compute m).hi
        (SinPiIntegral.tangentSquareIntegral.compute m).lo
        (SinPiIntegral.tangentSquareIntegral.compute m).hi).hi <=
      (QBox.mulRealInterval
        (SinPiIntegral.reciprocalPiRaw.compute n).lo
        (SinPiIntegral.reciprocalPiRaw.compute n).hi
        (SinPiIntegral.tangentSquareIntegral.compute n).lo
        (SinPiIntegral.tangentSquareIntegral.compute n).hi).hi
  have hproduct := QBox.mulRealInterval_nested
    hrecip.1 hrecip.2.1 hrecip.2.2
    htangent.1 htangent.2.1 htangent.2.2
  have hrecipM := RealRaw.interval_order_of_valid
    SinPiIntegral.reciprocalPiRaw SinPiIntegral.reciprocalPiRaw_valid m
  have htangentM := RealRaw.interval_order_of_valid
    SinPiIntegral.tangentSquareIntegral SinPiIntegral.tangentSquareIntegral_valid m
  have hm := QBox.mulRealInterval_ordered
    (a := (SinPiIntegral.reciprocalPiRaw.compute m).lo)
    (b := (SinPiIntegral.reciprocalPiRaw.compute m).hi)
    (c := (SinPiIntegral.tangentSquareIntegral.compute m).lo)
    (d := (SinPiIntegral.tangentSquareIntegral.compute m).hi)
    hrecipM htangentM
  exact ⟨hproduct.1, hm, hproduct.2⟩

theorem normalizedTangentSquareProduct_widths_shrink_of_bounds
    {B : Rat} (hB : 0 < B)
    (hbound : forall n,
      qabs (SinPiIntegral.reciprocalPiRaw.compute n).lo <= B /\
      qabs (SinPiIntegral.tangentSquareIntegral.compute n).lo <= B /\
      qabs (SinPiIntegral.tangentSquareIntegral.compute n).hi <= B) :
    RealRaw.WidthsShrinkToZero normalizedTangentSquareIntegral.compute := by
  intro eps
  let delta : QPos := ⟨eps.val / ((4 : Rat) * B), by
    rw [Rat.div_def]
    exact Rat.mul_pos eps.property ((Rat.inv_pos).2
      (Rat.mul_pos (by native_decide) hB))⟩
  obtain ⟨Nr, hr⟩ := SinPiIntegral.reciprocalPiRaw_valid.2.2 delta
  obtain ⟨Nt, ht⟩ := SinPiIntegral.tangentSquareIntegral_valid.2.2 delta
  refine ⟨Nat.max Nr Nt, ?_⟩
  intro n hn
  have hnr : Nr <= n := Nat.le_trans (Nat.le_max_left _ _) hn
  have hnt : Nt <= n := Nat.le_trans (Nat.le_max_right _ _) hn
  have hwr := hr n hnr
  have hwt := ht n hnt
  have hro := RealRaw.interval_order_of_valid
    SinPiIntegral.reciprocalPiRaw SinPiIntegral.reciprocalPiRaw_valid n
  have hto := RealRaw.interval_order_of_valid
    SinPiIntegral.tangentSquareIntegral SinPiIntegral.tangentSquareIntegral_valid n
  have hp := QBox.mulRealInterval_width_le_of_abs_bounded
    hro hto (hbound n).1 (hbound n).2.1 (hbound n).2.2
  change (QBox.mulRealInterval
      (SinPiIntegral.reciprocalPiRaw.compute n).lo
      (SinPiIntegral.reciprocalPiRaw.compute n).hi
      (SinPiIntegral.tangentSquareIntegral.compute n).lo
      (SinPiIntegral.tangentSquareIntegral.compute n).hi).width <= eps.val
  calc
    _ <= (2 : Rat) * B *
        ((SinPiIntegral.reciprocalPiRaw.compute n).width +
          (SinPiIntegral.tangentSquareIntegral.compute n).width) := hp
    _ <= (2 : Rat) * B * (delta.val + delta.val) := by
      exact Rat.mul_le_mul_of_nonneg_left
        (rat_add_le_add hwr hwt)
        (Rat.mul_nonneg (by native_decide) (Rat.le_of_lt hB))
    _ = eps.val := by
      dsimp [delta]
      rw [Rat.div_def]
      grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

theorem normalizedTangentSquareProduct_endpoint_bounds :
    forall n,
      qabs (SinPiIntegral.reciprocalPiRaw.compute n).lo <= (128 : Rat) /\
      qabs (SinPiIntegral.tangentSquareIntegral.compute n).lo <= (128 : Rat) /\
      qabs (SinPiIntegral.tangentSquareIntegral.compute n).hi <= (128 : Rat) := by
  intro n
  have hrecip := SinPiIntegral.reciprocalPiRaw_bounds n
  have hrecip_lo : qabs (SinPiIntegral.reciprocalPiRaw.compute n).lo <=
      (128 : Rat) := by
    have horder := RealRaw.interval_order_of_valid
      SinPiIntegral.reciprocalPiRaw SinPiIntegral.reciprocalPiRaw_valid n
    rw [qabs_eq_self_of_nonneg hrecip.1]
    grind [hrecip.2]
  have hrecip_hi : qabs (SinPiIntegral.reciprocalPiRaw.compute n).hi <=
      (128 : Rat) := by
    have hhi0 : 0 <= (SinPiIntegral.reciprocalPiRaw.compute n).hi := by
      exact Rat.le_trans hrecip.1
        (RealRaw.interval_order_of_valid
          SinPiIntegral.reciprocalPiRaw SinPiIntegral.reciprocalPiRaw_valid n)
    rw [qabs_eq_self_of_nonneg hhi0]
    grind [hrecip.2]
  have htan0lo : qabs (SinPiIntegral.tangentSquareIntegral.compute 0).lo <=
      (128 : Rat) := by
    rw [SinPiIntegral.tangentSquareIntegral_compute]
    native_decide
  have htan0hi : qabs (SinPiIntegral.tangentSquareIntegral.compute 0).hi <=
      (128 : Rat) := by
    rw [SinPiIntegral.tangentSquareIntegral_compute]
    native_decide
  have htan_nested := SinPiIntegral.tangentSquareIntegral_valid.2.1
    0 n (Nat.zero_le n)
  have htan_order_n := RealRaw.interval_order_of_valid
    SinPiIntegral.tangentSquareIntegral SinPiIntegral.tangentSquareIntegral_valid n
  have htan_lo_lower : -(128 : Rat) <=
      (SinPiIntegral.tangentSquareIntegral.compute n).lo := by
    exact Rat.le_trans
      (Rat.le_trans (by grind) (neg_qabs_le_self _))
      htan_nested.1
  have htan_hi_upper :
      (SinPiIntegral.tangentSquareIntegral.compute n).hi <= (128 : Rat) := by
    have h0hi :
        (SinPiIntegral.tangentSquareIntegral.compute 0).hi <= (128 : Rat) :=
      Rat.le_trans (self_le_qabs _) htan0hi
    exact Rat.le_trans htan_nested.2.2 h0hi
  have htan_lo_upper :
      (SinPiIntegral.tangentSquareIntegral.compute n).lo <= (128 : Rat) :=
    Rat.le_trans htan_order_n htan_hi_upper
  have htan_hi_lower : -(128 : Rat) <=
      (SinPiIntegral.tangentSquareIntegral.compute n).hi :=
    Rat.le_trans htan_lo_lower htan_order_n
  refine ⟨hrecip_lo, ?_, ?_⟩
  · exact qabs_le_of_neg_le_le htan_lo_lower htan_lo_upper
  · exact qabs_le_of_neg_le_le htan_hi_lower htan_hi_upper

theorem normalizedTangentSquareProduct_valid_of_bounds
    {B : Rat} (hB : 0 < B)
    (hbound : forall n,
      qabs (SinPiIntegral.reciprocalPiRaw.compute n).lo <= B /\
      qabs (SinPiIntegral.tangentSquareIntegral.compute n).lo <= B /\
      qabs (SinPiIntegral.tangentSquareIntegral.compute n).hi <= B) :
    SignedRawProductValiditySubgoal
      SinPiIntegral.reciprocalPiRaw SinPiIntegral.tangentSquareIntegral := by
  exact {
    ordered := normalizedTangentSquareProduct_ordered
    nested := normalizedTangentSquareProduct_nested
    widths_shrink := normalizedTangentSquareProduct_widths_shrink_of_bounds hB hbound }

theorem normalizedTangentSquareProduct_valid :
    SignedRawProductValiditySubgoal
      SinPiIntegral.reciprocalPiRaw SinPiIntegral.tangentSquareIntegral := by
  exact normalizedTangentSquareProduct_valid_of_bounds
    (by native_decide) normalizedTangentSquareProduct_endpoint_bounds

theorem normalizedTangentSquareIntegral_valid :
    normalizedTangentSquareIntegral.Valid := by
  exact normalizedTangentSquareProduct_valid.valid

theorem normalizedTangentSquare_stage_zero_overlap :
    QInterval.Overlaps
      (SinPiIntegral.dyadicNestedRadicalSquareLeftSum 0)
      (normalizedTangentSquareIntegral.compute 0) := by
  change QInterval.Overlaps
    (SinPiIntegral.dyadicNestedRadicalSquareLeftSum 0)
    (QBox.mulRealInterval
      (SinPiIntegral.reciprocalPiRaw.compute 0).lo
      (SinPiIntegral.reciprocalPiRaw.compute 0).hi
      (SinPiIntegral.tangentSquareIntegral.compute 0).lo
      (SinPiIntegral.tangentSquareIntegral.compute 0).hi)
  unfold QInterval.Overlaps
  rw [SinPiIntegral.tangentSquareIntegral_compute]
  native_decide

theorem normalizedTangentSquare_stage_one_overlap :
    QInterval.Overlaps
      (SinPiIntegral.dyadicNestedRadicalSquareLeftSum 1)
      (normalizedTangentSquareIntegral.compute 1) := by
  change QInterval.Overlaps
    (SinPiIntegral.dyadicNestedRadicalSquareLeftSum 1)
    (QBox.mulRealInterval
      (SinPiIntegral.reciprocalPiRaw.compute 1).lo
      (SinPiIntegral.reciprocalPiRaw.compute 1).hi
      (SinPiIntegral.tangentSquareIntegral.compute 1).lo
      (SinPiIntegral.tangentSquareIntegral.compute 1).hi)
  unfold QInterval.Overlaps
  rw [SinPiIntegral.tangentSquareIntegral_compute]
  native_decide

theorem normalizedTangentSquare_stage_two_overlap :
    QInterval.Overlaps
      (SinPiIntegral.dyadicNestedRadicalSquareLeftSum 2)
      (normalizedTangentSquareIntegral.compute 2) := by
  change QInterval.Overlaps
    (SinPiIntegral.dyadicNestedRadicalSquareLeftSum 2)
    (QBox.mulRealInterval
      (SinPiIntegral.reciprocalPiRaw.compute 2).lo
      (SinPiIntegral.reciprocalPiRaw.compute 2).hi
      (SinPiIntegral.tangentSquareIntegral.compute 2).lo
      (SinPiIntegral.tangentSquareIntegral.compute 2).hi)
  unfold QInterval.Overlaps
  rw [SinPiIntegral.tangentSquareIntegral_compute]
  native_decide

/-! Signed product equivalence is a stagewise interval obligation.  The
nonnegative-product shortcut is intentionally not used here: both products
may contain negative coarse-stage endpoints. -/
structure SignedRawProductEquivalenceSubgoal
    (x x' y y' : RealRaw) where
  left_valid : (x * y).Valid
  right_valid : (x' * y').Valid
  stage_overlap : forall n,
    QInterval.Overlaps ((x * y).compute n) ((x' * y').compute n)

theorem SignedRawProductEquivalenceSubgoal.equiv
    {x x' y y' : RealRaw}
    (H : SignedRawProductEquivalenceSubgoal x x' y y') :
    (x * y).Equiv (x' * y') := by
  apply RealRaw.sameStageOverlap_equiv
  intro n
  exact (RealRaw.compareAt_overlap_iff (x * y) (x' * y') n n).2
    (H.stage_overlap n)

structure NormalizedTangentSquareTransportSubgoal where
  commonWitness : NormalizedTangentSquareCommonWitness
  normalized_validity :
    SignedRawProductValiditySubgoal
      SinPiIntegral.reciprocalPiRaw SinPiIntegral.tangentSquareIntegral
  normalized_anchor_valid :
    (SinPiIntegral.reciprocalPiRaw *
      RationalCircle.GeometricTrig.halfQuarterTurnRaw (1 : Rat)).Valid
  chart_transport :
    normalizedTangentSquareIntegral.Equiv
      (SinPiIntegral.reciprocalPiRaw *
        RationalCircle.GeometricTrig.halfQuarterTurnRaw (1 : Rat))

theorem NormalizedTangentSquareTransportSubgoal.value
    (H : NormalizedTangentSquareTransportSubgoal) :
    (SinPiIntegral.dyadicNestedRadicalSquareIntegralRaw_stabilized
      normalizedTangentSquareIntegral).Equiv
      (RealRaw.ofRat (1 / 4)) := by
  have hcandidate := H.commonWitness.to_equiv
  have hnormalized : normalizedTangentSquareIntegral.Valid := by
    exact H.normalized_validity.valid
  have hstable :=
    SinPiIntegral.dyadicNestedRadicalSquareIntegralRaw_stabilized_equiv_anchor_of_overlap
      hnormalized hcandidate
  have hanchor :
      normalizedTangentSquareIntegral.Equiv (RealRaw.ofRat (1 / 4)) := by
    exact RealRaw.equiv_trans hnormalized
      H.normalized_anchor_valid (RealRaw.ofRat_valid _)
      H.chart_transport reciprocalPi_quarterTurn_equiv_quarter
  exact RealRaw.equiv_trans
    (SinPiIntegral.dyadicNestedRadicalSquareIntegralRaw_stabilized_valid_of_overlap
      hnormalized hcandidate)
    hnormalized (RealRaw.ofRat_valid _) hstable hanchor

theorem NormalizedTangentSquareValueSubgoal.value
    (H : NormalizedTangentSquareValueSubgoal) :
    normalizedTangentSquareIntegral.Equiv (RealRaw.ofRat (1 / 4)) := by
  exact RealRaw.equiv_trans H.normalized_valid
    H.anchor_valid (RealRaw.ofRat_valid _) H.chart_transport
    reciprocalPi_quarterTurn_equiv_quarter

theorem tangentSquareIntegral_stage_zero_contains_quarter :
    QInterval.Overlaps
      (SinPiIntegral.tangentSquareIntegral.compute 0)
      ({ lo := (1 / 4 : Rat), hi := 1 / 4 } : QInterval) := by
  unfold QInterval.Overlaps
  rw [SinPiIntegral.tangentSquareIntegral_compute]
  native_decide

theorem tangentSquareIntegral_width (n : Nat) :
    (SinPiIntegral.tangentSquareIntegral.compute n).width =
      (128 : Rat) / (((2 ^ n : Nat) : Rat)) := by
  rw [SinPiIntegral.tangentSquareIntegral_compute]
  rw [IntegralIdentities.LipschitzDyadic.compute_width
    (f := SinPiIntegral.tangentSquareDensity) 64 n]
  change (2 : Rat) * 64 * (1 / (((2 ^ n : Nat) : Rat))) =
    128 / (((2 ^ n : Nat) : Rat))
  rw [show (2 : Rat) * 64 = 128 by native_decide]
  simp [Rat.div_def]

theorem tangentSquareLeftSum_stage_one_quarter_certificate :
    ((1 / 4 : Rat) - (64 : Rat) / (((2 ^ 1 : Nat) : Rat)) <=
        IntegralIdentities.LipschitzDyadic.uniformLeftEndpointSum
          SinPiIntegral.tangentSquareDensity (2 ^ 1)) ∧
      (IntegralIdentities.LipschitzDyadic.uniformLeftEndpointSum
          SinPiIntegral.tangentSquareDensity (2 ^ 1) <=
        (1 / 4 : Rat) + (64 : Rat) / (((2 ^ 1 : Nat) : Rat))) := by
  native_decide

theorem tangentSquareLeftSum_stage_two_quarter_certificate :
    ((1 / 4 : Rat) - (64 : Rat) / (((2 ^ 2 : Nat) : Rat)) <=
        IntegralIdentities.LipschitzDyadic.uniformLeftEndpointSum
          SinPiIntegral.tangentSquareDensity (2 ^ 2)) ∧
      (IntegralIdentities.LipschitzDyadic.uniformLeftEndpointSum
          SinPiIntegral.tangentSquareDensity (2 ^ 2) <=
        (1 / 4 : Rat) + (64 : Rat) / (((2 ^ 2 : Nat) : Rat))) := by
  native_decide

structure TangentSquareLeftSumQuarterCertificate where
  lower_sum :
    forall n,
      IntegralIdentities.LipschitzDyadic.uniformLeftEndpointSum
          SinPiIntegral.tangentSquareDensity (2 ^ n) <=
        (1 / 4 : Rat) +
          (64 : Rat) / (((2 ^ n : Nat) : Rat))
  upper_sum :
    forall n,
      (1 / 4 : Rat) -
          (64 : Rat) / (((2 ^ n : Nat) : Rat))
          <= IntegralIdentities.LipschitzDyadic.uniformLeftEndpointSum
            SinPiIntegral.tangentSquareDensity (2 ^ n)

theorem TangentSquareLeftSumQuarterCertificate.to_value_subgoal
    (H : TangentSquareLeftSumQuarterCertificate) :
    TangentSquareIntegralValueSubgoal := by
  constructor
  · intro n
    have hmargin :=
      IntegralIdentities.LipschitzDyadic.compute_contains_uniformLeftEndpointSum_margin
        SinPiIntegral.tangentSquareDensity_lipschitz_on_unit n
    rw [SinPiIntegral.tangentSquareIntegral_compute]
    change (IntegralIdentities.LipschitzDyadic.compute
      SinPiIntegral.tangentSquareDensity 64 n).lo <= (1 / 4 : Rat)
    have hleft := hmargin.1
    have hsum := H.lower_sum n
    exact Rat.le_trans hleft (by
      grind [Rat.sub_eq_add_neg, Rat.div_def, Rat.mul_assoc, Rat.mul_comm])
  · intro n
    have hmargin :=
      IntegralIdentities.LipschitzDyadic.compute_contains_uniformLeftEndpointSum_margin
        SinPiIntegral.tangentSquareDensity_lipschitz_on_unit n
    rw [SinPiIntegral.tangentSquareIntegral_compute]
    change (1 / 4 : Rat) <=
      (IntegralIdentities.LipschitzDyadic.compute
        SinPiIntegral.tangentSquareDensity 64 n).hi
    have hright := hmargin.2
    have hsum := H.upper_sum n
    exact Rat.le_trans (by
      grind [Rat.sub_eq_add_neg, Rat.div_def, Rat.mul_assoc, Rat.mul_comm]) hright

structure TangentSquareFTCIntegralCompatibilitySubgoal where
  stage_overlap :
    forall n, QInterval.Overlaps
      (SinPiIntegral.tangentSquareEffectiveIntegralRaw.compute n)
      (SinPiIntegral.tangentSquareIntegral.compute n)

structure TangentSquareFTCIntegralCommonWitness where
  witness : Nat -> Rat
  effective_lo_le :
    forall n,
      (SinPiIntegral.tangentSquareEffectiveIntegralRaw.compute n).lo <= witness n
  witness_le_effective_hi :
    forall n,
      witness n <= (SinPiIntegral.tangentSquareEffectiveIntegralRaw.compute n).hi
  anchor_lo_le :
    forall n,
      (SinPiIntegral.tangentSquareIntegral.compute n).lo <= witness n
  witness_le_anchor_hi :
    forall n,
      witness n <= (SinPiIntegral.tangentSquareIntegral.compute n).hi

theorem TangentSquareFTCIntegralCommonWitness.to_compatibility
    (H : TangentSquareFTCIntegralCommonWitness) :
    TangentSquareFTCIntegralCompatibilitySubgoal := by
  exact {
    stage_overlap := fun n => by
      unfold QInterval.Overlaps
      exact ⟨Rat.le_trans (H.effective_lo_le n)
          (H.witness_le_anchor_hi n),
        Rat.le_trans (H.anchor_lo_le n)
          (H.witness_le_effective_hi n)⟩ }

theorem TangentSquareFTCIntegralCompatibilitySubgoal.equivalent
    (H : TangentSquareFTCIntegralCompatibilitySubgoal) :
    SinPiIntegral.tangentSquareEffectiveIntegralRaw.Equiv
      SinPiIntegral.tangentSquareIntegral := by
  apply RealRaw.sameStageOverlap_equiv
  intro n
  exact (RealRaw.compareAt_overlap_iff
    SinPiIntegral.tangentSquareEffectiveIntegralRaw
    SinPiIntegral.tangentSquareIntegral n n).2 (H.stage_overlap n)

/- The correctly normalized tangent-chart value is obtained in two stages:
   first identify the unscaled chart integral with the quarter-turn endpoint;
   only then apply the reciprocal-pi factor.  The scheduled endpoint validity
   is kept as data because an arbitrary endpoint-stage selector need not be
   nested by itself. -/
structure TangentSquareQuarterTurnValueSubgoal where
  tangent_integral_valid : SinPiIntegral.tangentSquareIntegral.Valid
  effective_integral_valid :
    SinPiIntegral.tangentSquareEffectiveIntegralRaw.Valid
  endpoint_valid :
    SinPiIntegral.tangentSquareEffectiveCandidateFTC.toDerivativeBoundFTC.endpointRaw.Valid
  quarter_valid :
    (RationalCircle.GeometricTrig.halfQuarterTurnRaw (1 : Rat)).Valid
  compatibility : TangentSquareFTCIntegralCompatibilitySubgoal
  endpoint_equiv_quarter :
    SinPiIntegral.tangentSquareEffectiveCandidateFTC.toDerivativeBoundFTC.endpointRaw.Equiv
      (RationalCircle.GeometricTrig.halfQuarterTurnRaw (1 : Rat))

def TangentSquareQuarterTurnValueSubgoal.of_common_witness
    (effective_integral_valid :
      SinPiIntegral.tangentSquareEffectiveIntegralRaw.Valid)
    (endpoint_valid :
      SinPiIntegral.tangentSquareEffectiveCandidateFTC.toDerivativeBoundFTC.endpointRaw.Valid)
    (common : TangentSquareFTCIntegralCommonWitness)
    (endpoint_equiv_quarter :
      SinPiIntegral.tangentSquareEffectiveCandidateFTC.toDerivativeBoundFTC.endpointRaw.Equiv
        (RationalCircle.GeometricTrig.halfQuarterTurnRaw (1 : Rat))) :
    TangentSquareQuarterTurnValueSubgoal := by
  refine {
    tangent_integral_valid := SinPiIntegral.tangentSquareIntegral_valid
    effective_integral_valid := effective_integral_valid
    endpoint_valid := endpoint_valid
    quarter_valid := ?_
    compatibility := common.to_compatibility
    endpoint_equiv_quarter := endpoint_equiv_quarter }
  change (RealRaw.scaleRat ((1 : Rat) / 4) piCircleArea).Valid
  exact RealRaw.scaleRat_valid_of_nonneg (by native_decide)
    CauchyPi.piCircleArea_valid

theorem TangentSquareQuarterTurnValueSubgoal.tangent_equiv_effective
    (H : TangentSquareQuarterTurnValueSubgoal) :
    SinPiIntegral.tangentSquareIntegral.Equiv
      SinPiIntegral.tangentSquareEffectiveIntegralRaw := by
  exact RealRaw.equiv_symm H.compatibility.equivalent

theorem tangentSquareIntegral_equiv_halfQuarterTurn_of_common_witness
    (effective_integral_valid :
      SinPiIntegral.tangentSquareEffectiveIntegralRaw.Valid)
    (endpoint_valid :
      SinPiIntegral.tangentSquareEffectiveCandidateFTC.toDerivativeBoundFTC.endpointRaw.Valid)
    (common : TangentSquareFTCIntegralCommonWitness)
    (endpoint_equiv_quarter :
      SinPiIntegral.tangentSquareEffectiveCandidateFTC.toDerivativeBoundFTC.endpointRaw.Equiv
        (RationalCircle.GeometricTrig.halfQuarterTurnRaw (1 : Rat))) :
    SinPiIntegral.tangentSquareIntegral.Equiv
      (RationalCircle.GeometricTrig.halfQuarterTurnRaw (1 : Rat)) := by
  let H := TangentSquareQuarterTurnValueSubgoal.of_common_witness
    effective_integral_valid endpoint_valid common endpoint_equiv_quarter
  have hanchor_endpoint := RealRaw.equiv_trans
    H.tangent_integral_valid H.effective_integral_valid H.endpoint_valid
    H.tangent_equiv_effective
    SinPiIntegral.tangentSquareEffectiveIntegralRaw_equiv_endpoint
  exact RealRaw.equiv_trans
    H.tangent_integral_valid H.endpoint_valid H.quarter_valid
    hanchor_endpoint H.endpoint_equiv_quarter

theorem TangentSquareQuarterTurnValueSubgoal.effective_equiv_endpoint
    (H : TangentSquareQuarterTurnValueSubgoal) :
    SinPiIntegral.tangentSquareEffectiveIntegralRaw.Equiv
      SinPiIntegral.tangentSquareEffectiveCandidateFTC.toDerivativeBoundFTC.endpointRaw := by
  exact SinPiIntegral.tangentSquareEffectiveIntegralRaw_equiv_endpoint

theorem TangentSquareQuarterTurnValueSubgoal.value
    (H : TangentSquareQuarterTurnValueSubgoal) :
    SinPiIntegral.tangentSquareIntegral.Equiv
      (RationalCircle.GeometricTrig.halfQuarterTurnRaw (1 : Rat)) := by
  have hanchor_eff := H.tangent_equiv_effective
  have heff_endpoint := H.effective_equiv_endpoint
  have hanchor_endpoint := RealRaw.equiv_trans
    H.tangent_integral_valid H.effective_integral_valid H.endpoint_valid
    hanchor_eff heff_endpoint
  exact RealRaw.equiv_trans
    H.tangent_integral_valid H.endpoint_valid H.quarter_valid
    hanchor_endpoint H.endpoint_equiv_quarter

theorem TangentSquareIntegralValueSubgoal.value
    (H : TangentSquareIntegralValueSubgoal) :
    SinPiIntegral.tangentSquareIntegral.Equiv (RealRaw.ofRat (1 / 4)) := by
  intro n
  apply (RealRaw.compareAt_overlap_iff
    SinPiIntegral.tangentSquareIntegral (RealRaw.ofRat (1 / 4)) n n).2
  change QInterval.Overlaps
    (SinPiIntegral.tangentSquareIntegral.compute n)
    ((RealRaw.ofRat (1 / 4)).compute n)
  unfold QInterval.Overlaps RealRaw.ofRat
  exact ⟨H.lower_contains n, H.upper_contains n⟩

/-! The remaining genuine `sin(pi*x)^2` transport is packaged as two finite
certificates.  The closure theorem below is unconditional once these fields
are supplied; no completed-real existence theorem is hidden in the package. -/
structure NestedRadicalSinPiSquareValueSubgoal where
  commonWitness :
    SinPiIntegral.DyadicNestedRadicalSquareTangentCommonWitness
  tangentAnchorValue :
    TangentSquareIntegralValueSubgoal

theorem NestedRadicalSinPiSquareValueSubgoal.value
    (H : NestedRadicalSinPiSquareValueSubgoal) :
    (SinPiIntegral.dyadicNestedRadicalSquareIntegralRaw_stabilized
      SinPiIntegral.tangentSquareIntegral).Equiv
      (RealRaw.ofRat (1 / 4)) := by
  exact SinPiIntegral.dyadicNestedRadicalSquareIntegralRaw_stabilized_equiv_value_of_anchor
    H.commonWitness.to_equiv H.tangentAnchorValue.value

/- The specialized construction boundary for the squared nested-radical
   evaluator.  Once these fields are supplied, the generic equal-plan
   interval-sum theorem transports the public `sin²` integral to the
   evaluator's certified integral. -/
structure NestedRadicalSquareIntegralConstructionSubgoal
    (S : SinPiIntegral.ArctanSinPiConstruction) where
  publicConstruction : Integral.Construction
    (SinPiIntegral.sinPiSquareOnHalf S) 0 ((1 : Rat) / 2)
  evaluator : RealFunRaw
  integral : Integral.Construction evaluator 0 ((1 : Rat) / 2)
  same_plan : publicConstruction.plan = integral.plan
  sample_overlap : forall n k,
    k < (publicConstruction.plan n).subdivisions ->
    QInterval.Overlaps
      ((SinPiIntegral.sinPiSquareOnHalf S).compute
        (leftPoint 0 ((1 : Rat) / 2)
          (publicConstruction.plan n).subdivisions k)
        (publicConstruction.plan n).evalPrecision)
      (evaluator.compute
        (leftPoint 0 ((1 : Rat) / 2)
          (publicConstruction.plan n).subdivisions k)
        (publicConstruction.plan n).evalPrecision)

theorem NestedRadicalSquareIntegralConstructionSubgoal.public_equiv_evaluator
    {S : SinPiIntegral.ArctanSinPiConstruction}
    (H : NestedRadicalSquareIntegralConstructionSubgoal S) :
    (Integral.integral (SinPiIntegral.sinPiSquareOnHalf S) 0 ((1 : Rat) / 2)
      H.publicConstruction).Equiv
      (Integral.integral H.evaluator 0 ((1 : Rat) / 2) H.integral) := by
  exact Integral.integral_equiv_of_plan_and_sample_overlaps
    (by native_decide : (0 : Rat) <= (1 : Rat) / 2)
    H.publicConstruction H.integral H.same_plan H.sample_overlap

/- The next constructor makes the remaining `sin²` obligation concrete.  The
   evaluator is required only to return the squared nested-radical box at the
   public plan's sample points; the canonical half-angle certificates then
   supply the interval overlaps needed by the generic integral transport. -/
def NestedRadicalSquareIntegralConstructionSubgoal.of_canonical_search
    (S : SinPiIntegral.ArctanSinPiConstruction)
    (publicConstruction : Integral.Construction
      (SinPiIntegral.sinPiSquareOnHalf S) 0 ((1 : Rat) / 2))
    (evaluator : RealFunRaw)
    (integral : Integral.Construction evaluator 0 ((1 : Rat) / 2))
    (hdyadic : publicConstruction.plan = Integral.staticDyadicPlan)
    (hplan : publicConstruction.plan = integral.plan)
    (hevaluator : forall n k,
      k < (publicConstruction.plan n).subdivisions ->
      evaluator.compute
        (leftPoint 0 ((1 : Rat) / 2)
          (publicConstruction.plan n).subdivisions k)
        (publicConstruction.plan n).evalPrecision =
        SinPiIntegral.rationalSquareInterval
          (SinPiIntegral.dyadicNestedRadicalStageSinAt n k))
    (ht0 : (S.inverse.tangentAt 0
      RationalCircle.GeometricTrig.firstQuadrantBranch_zero).Equiv
      RealRaw.zero)
    (hcertificate : forall (n k : Nat) (hk : k < 2 ^ n),
      0 < k -> SinPiIntegral.CanonicalDyadicHalfAngleCertificate
        S.inverse n k hk) :
    NestedRadicalSquareIntegralConstructionSubgoal S := by
  refine {
    publicConstruction := publicConstruction
    evaluator := evaluator
    integral := integral
    same_plan := hplan
    sample_overlap := ?_ }
  intro n k hk
  have hk' : k < 2 ^ n := by
    simpa [hdyadic, Integral.staticDyadicPlan,
      Integral.staticDyadicSubdivisions] using hk
  obtain ⟨m, u, hu⟩ :=
    SinPiIntegral.canonical_dyadic_search_of_halfAngle_certificate_family
      S.inverse ht0 hcertificate n k hk'
  have hover := SinPiIntegral.sinPiSquare_nestedRadicalStage_sample_overlap_of_canonical_box_search
    S hk' m u hu
  have he := hevaluator n k hk
  rw [he]
  simpa [hdyadic, Integral.staticDyadicPlan,
    Integral.staticDyadicSubdivisions] using hover

/- The square-sum width estimate and orderedness are already proved.  This
   isolates the one missing raw-real property: cross-stage nesting of the
   finite dyadic square sums. -/
structure NestedRadicalSquareCandidateValiditySubgoal where
  nested : forall n m, n <= m ->
    (SinPiIntegral.dyadicNestedRadicalSquareLeftSum n).lo <=
      (SinPiIntegral.dyadicNestedRadicalSquareLeftSum m).lo /\
    (SinPiIntegral.dyadicNestedRadicalSquareLeftSum m).lo <=
      (SinPiIntegral.dyadicNestedRadicalSquareLeftSum m).hi /\
    (SinPiIntegral.dyadicNestedRadicalSquareLeftSum m).hi <=
      (SinPiIntegral.dyadicNestedRadicalSquareLeftSum n).hi

theorem NestedRadicalSquareCandidateValiditySubgoal.valid
    (H : NestedRadicalSquareCandidateValiditySubgoal) :
    SinPiIntegral.dyadicNestedRadicalSquareIntegralRaw.Valid := by
  refine ⟨?_, H.nested, ?_⟩
  · intro n
    exact SinPiIntegral.dyadicNestedRadicalSquareLeftSum_ordered n
  · exact SinPiIntegral.dyadicNestedRadicalSquareIntegralRaw_widths_shrink

/- The arbitrary common witness can be specialized to the expected value.
   This leaves precisely the two-sided finite enclosure of `1/4` for the
   nested-radical square sums; the tangent-square side already has the same
   two-sided interface. -/
structure NestedRadicalSquareQuarterBoundsSubgoal where
  lower_contains : forall n,
    (SinPiIntegral.dyadicNestedRadicalSquareLeftSum n).lo <= (1 / 4 : Rat)
  upper_contains : forall n,
    (1 / 4 : Rat) <=
      (SinPiIntegral.dyadicNestedRadicalSquareLeftSum n).hi

def NestedRadicalSquareQuarterBoundsSubgoal.toCommonWitness
    (H : NestedRadicalSquareQuarterBoundsSubgoal)
    (T : TangentSquareIntegralValueSubgoal) :
    SinPiIntegral.DyadicNestedRadicalSquareTangentCommonWitness := by
  refine {
    witness := fun _ => (1 / 4 : Rat)
    candidate_lo_le := H.lower_contains
    witness_le_candidate_hi := H.upper_contains
    tangent_lo_le := T.lower_contains
    witness_le_tangent_hi := T.upper_contains }

def NestedRadicalSquareQuarterBoundsSubgoal.toValueSubgoal
    (H : NestedRadicalSquareQuarterBoundsSubgoal)
    (T : TangentSquareIntegralValueSubgoal) :
    NestedRadicalSinPiSquareValueSubgoal :=
  { commonWitness := H.toCommonWitness T
    tangentAnchorValue := T }

def NestedRadicalSquareQuarterBoundsSubgoal.toValueSubgoal_of_tangent_sum_certificate
    (H : NestedRadicalSquareQuarterBoundsSubgoal)
    (T : TangentSquareLeftSumQuarterCertificate) :
    NestedRadicalSinPiSquareValueSubgoal :=
  H.toValueSubgoal T.to_value_subgoal

theorem NestedRadicalSquareIntegralConstructionSubgoal.transport_of_compute
    {S : SinPiIntegral.ArctanSinPiConstruction}
    (H : NestedRadicalSquareIntegralConstructionSubgoal S)
    (hcompute : forall n,
      (Integral.integral H.evaluator 0 ((1 : Rat) / 2) H.integral).compute n =
        SinPiIntegral.dyadicNestedRadicalSquareIntegralRaw.compute n)
    (hcommon : SinPiIntegral.DyadicNestedRadicalSquareTangentCommonWitness) :
    (Integral.integral H.evaluator 0 ((1 : Rat) / 2) H.integral).Equiv
      (SinPiIntegral.dyadicNestedRadicalSquareIntegralRaw_stabilized
        SinPiIntegral.tangentSquareIntegral) := by
  have hevaluator :
      (Integral.integral H.evaluator 0 ((1 : Rat) / 2) H.integral).Valid := by
    exact FTC.integral_valid_of_construction H.integral
  have hanchor := hcommon.to_equiv
  have hcontains := RealRaw.prefixStabilize_contains_anchor
    (candidate := SinPiIntegral.dyadicNestedRadicalSquareIntegralRaw)
    (anchor := SinPiIntegral.tangentSquareIntegral)
    SinPiIntegral.tangentSquareIntegral_valid hanchor
    (fun n => Rat.le_refl)
  apply RealRaw.sameStageOverlap_equiv
  intro n
  apply (RealRaw.compareAt_overlap_iff
    (Integral.integral H.evaluator 0 ((1 : Rat) / 2) H.integral)
    (SinPiIntegral.dyadicNestedRadicalSquareIntegralRaw_stabilized
      SinPiIntegral.tangentSquareIntegral) n n).2
  rw [hcompute n]
  have hcommon' :=
    (RealRaw.compareAt_overlap_iff
      SinPiIntegral.dyadicNestedRadicalSquareIntegralRaw
      SinPiIntegral.tangentSquareIntegral n n).1 (hanchor n)
  have hstable' := hcontains n
  exact ⟨Rat.le_trans hcommon'.1 hstable'.2,
    Rat.le_trans hstable'.1 hcommon'.2⟩

theorem NestedRadicalSquareIntegralConstructionSubgoal.value_of_tangent_anchor
    {S : SinPiIntegral.ArctanSinPiConstruction}
    (H : NestedRadicalSquareIntegralConstructionSubgoal S)
    (htransport :
      (Integral.integral H.evaluator 0 ((1 : Rat) / 2) H.integral).Equiv
        (SinPiIntegral.dyadicNestedRadicalSquareIntegralRaw_stabilized
          SinPiIntegral.tangentSquareIntegral))
    (hvalue : NestedRadicalSinPiSquareValueSubgoal) :
    (Integral.integral (SinPiIntegral.sinPiSquareOnHalf S) 0 ((1 : Rat) / 2)
      H.publicConstruction).Equiv (RealRaw.ofRat (1 / 4)) := by
  have hpublic :
      (Integral.integral (SinPiIntegral.sinPiSquareOnHalf S)
        0 ((1 : Rat) / 2) H.publicConstruction).Valid := by
    exact FTC.integral_valid_of_construction H.publicConstruction
  have hevaluator :
      (Integral.integral H.evaluator 0 ((1 : Rat) / 2) H.integral).Valid := by
    exact FTC.integral_valid_of_construction H.integral
  have hstable :
      (SinPiIntegral.dyadicNestedRadicalSquareIntegralRaw_stabilized
        SinPiIntegral.tangentSquareIntegral).Valid := by
    exact SinPiIntegral.dyadicNestedRadicalSquareIntegralRaw_stabilized_valid_of_tangentSquareIntegral_overlap
      hvalue.commonWitness.to_equiv
  exact RealRaw.equiv_trans hpublic hevaluator
    (RealRaw.ofRat_valid (1 / 4)) H.public_equiv_evaluator
      (RealRaw.equiv_trans hevaluator hstable (RealRaw.ofRat_valid (1 / 4))
        htransport hvalue.value)

theorem NestedRadicalSquareIntegralConstructionSubgoal.value_of_quarter_bounds
    {S : SinPiIntegral.ArctanSinPiConstruction}
    (H : NestedRadicalSquareIntegralConstructionSubgoal S)
    (htransport :
      (Integral.integral H.evaluator 0 ((1 : Rat) / 2) H.integral).Equiv
        (SinPiIntegral.dyadicNestedRadicalSquareIntegralRaw_stabilized
          SinPiIntegral.tangentSquareIntegral))
    (hsquare : NestedRadicalSquareQuarterBoundsSubgoal)
    (htangent : TangentSquareIntegralValueSubgoal) :
    (Integral.integral (SinPiIntegral.sinPiSquareOnHalf S) 0 ((1 : Rat) / 2)
      H.publicConstruction).Equiv (RealRaw.ofRat (1 / 4)) := by
  exact H.value_of_tangent_anchor htransport
    (hsquare.toValueSubgoal htangent)

theorem effectiveFTCPortfolio : EffectiveFTCPortfolio where
  square_value := Integral.exactRat_square_integral_raw_equiv_one_third
  cube_value := Integral.exactRat_cube_integral_raw_equiv_one_fourth
  quartic_value := Integral.exactRat_quartic_integral_raw_equiv_one_fifth
  fifth_value := Integral.fifthIntegralEffectiveFTC_equiv_one_sixth
  square_effective_value := by
    intro n
    apply (RealRaw.compareAt_overlap_iff
      Integral.squareEffectiveFTCData.toDerivativeBoundFTC.boundedIntegralRaw
      (RealRaw.ofRat 1) n n).2
    let H := Integral.squareEffectiveFTCData.toDerivativeBoundFTC
    change QInterval.Overlaps
      (H.boundedIntegralInterval (precisionAtStage n))
      ({ lo := 1, hi := 1 } : QInterval)
    have hover := H.overlap (precisionAtStage n)
    simp [H, Integral.squareEffectiveFTCData, endpointDifferenceInterval,
      Integral.squarePrimitiveRaw, RealFunRaw.exact] at hover
    simp [H, DerivativeBoundFTC.boundedIntegralInterval,
      DerivativeBoundFTC.endpointInterval,
      Integral.squareEffectiveFTCData, Integral.squarePrimitiveRaw,
      RealFunRaw.exact, endpointDifferenceInterval] at ⊢
    unfold QInterval.Overlaps at hover ⊢
    grind
  cube_effective_value := by
    intro n
    apply (RealRaw.compareAt_overlap_iff
      Integral.cubeEffectiveFTCData.toDerivativeBoundFTC.boundedIntegralRaw
      (RealRaw.ofRat 1) n n).2
    let H := Integral.cubeEffectiveFTCData.toDerivativeBoundFTC
    change QInterval.Overlaps
      (H.boundedIntegralInterval (precisionAtStage n))
      ({ lo := 1, hi := 1 } : QInterval)
    have hover := H.overlap (precisionAtStage n)
    simp [H, Integral.cubeEffectiveFTCData, endpointDifferenceInterval,
      Integral.cubePrimitiveRaw, RealFunRaw.exact] at hover
    simp [H, DerivativeBoundFTC.boundedIntegralInterval,
      Integral.cubeEffectiveFTCData, Integral.cubePrimitiveRaw,
      RealFunRaw.exact] at ⊢
    unfold QInterval.Overlaps at hover ⊢
    grind
  quartic_effective_value := Integral.quarticIntegralEffectiveFTC_equiv_one_fifth
  sine_prefix_square_value :=
    FiniteSinePrefix.sineTaylorPrefixThreeSquareEffectiveFTC_equiv_value
  tangent_pullback_value := SinPiIntegral.tangentPullbackIntegral_equiv_one
  square := Integral.squareEffectiveFTC_equiv_endpoint
  cube := Integral.cubeEffectiveFTC_equiv_endpoint
  quartic := Integral.quarticEffectiveFTC_equiv_endpoint
  fifth := Integral.fifthIntegralEffectiveFTC_equiv_endpoint
  arctan := Integral.arctanEffectiveFTC_equiv_endpoint
  tangentPullback := SinPiIntegral.tangentPullbackEffectiveFTC_equiv_endpoint
  tangentSquareEffective := SinPiIntegral.tangentSquareEffectiveIntegralRaw_equiv_endpoint
  tangentSquareEndpoint :=
    SinPiIntegral.tangentSquareEffectivePrimitive_endpointDifference_equiv_halfQuarterTurn
  sinePrefixSquare := FiniteSinePrefix.sineTaylorPrefixThreeSquareEffectiveFTC_equiv_endpoint
  exponential := ExpProofs.uniformExpOnUnit_effectiveFTC

/-!
The next rung is deliberately represented by the exact missing proof data.
The generic certificate already turns the integral into an endpoint raw; the
only remaining value theorem is that this endpoint raw is `1/4`.
-/

structure SinPiSquareEffectiveFTCEndpointSubgoal
    (S : SinPiIntegral.ArctanSinPiConstruction) where
  data : SinPiIntegral.SinPiSquareEffectiveFTCData S
  endpoint_value :
    data.endpointRaw.Equiv (RealRaw.ofRat (1 / 4))

theorem SinPiSquareEffectiveFTCEndpointSubgoal.integral_value
    {S : SinPiIntegral.ArctanSinPiConstruction}
    (H : SinPiSquareEffectiveFTCEndpointSubgoal S) :
    H.data.integralRaw.Equiv (RealRaw.ofRat (1 / 4)) := by
  exact H.data.endpoint_equiv_of_value H.endpoint_value

end ComputableAnalysis
