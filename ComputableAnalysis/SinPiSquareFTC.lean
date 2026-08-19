import ComputableAnalysis.SinPiIntegral
import ComputableAnalysis.FiniteSinePrefixFTC

/-!
# The squared-sine test function

This file records the first product-valued non-polynomial integrand.  The
pointwise square is built from the same arctangent/nested-radical sine
representation as the half-interval sine integral; no real-number product or
Lebesgue integral is introduced.
-/

namespace ComputableAnalysis

namespace SinPiIntegral

/-! The finite polynomial rung is already a complete effective-FTC theorem.
Expose it here as the algebraic shadow of the nested-radical target, so that
the later tail-transport proof has a fixed, checked predecessor. -/

def finiteSineSquarePrefixRaw : RealFunRaw :=
  FiniteSinePrefix.sineTaylorPrefixThreeSquareRaw

def finiteSineSquarePrefixPrimitiveRaw : RealFunRaw :=
  FiniteSinePrefix.sineTaylorPrefixThreeSquarePrimitiveRaw

/-! Tangent-chart endpoint algebra for the true squared-sine target.  With
`u = tan(pi*x/2)`, the normalized density is
`8*u^2/(1+u^2)^3`.  Its primitive splits into the existing arctangent kernel
and an exact rational correction. -/

def tangentSquareDensity (u : Rat) : Rat :=
  (8 * u * u) / (1 + u * u) ^ 3

def tangentSquareRationalPart (u : Rat) : Rat :=
  -((2 * u) / (1 + u * u) ^ 2) + u / (1 + u * u)

def tangentSquareRationalDerivative (u : Rat) : Rat :=
  (-1 + 6 * u * u - u ^ 4) / (1 + u * u) ^ 3

theorem tangentSquareDensity_decomposition (u : Rat) :
    tangentSquareDensity u =
      1 / (1 + u * u) + tangentSquareRationalDerivative u := by
  unfold tangentSquareDensity tangentSquareRationalDerivative
  have hden : 1 + u * u > 0 := by
    have hsq : 0 <= u * u := by
      exact rat_square_nonneg_basic u
    grind
  have hdenne : 1 + u * u ≠ 0 := Rat.ne_of_gt hden
  rw [Rat.div_def, Rat.div_def]
  have hpow : (1 + u * u) ^ 3 =
      (1 + u * u) * (1 + u * u) * (1 + u * u) := by
    simp [Rat.pow_succ]
  rw [hpow]
  have hcancel : (1 + u * u)⁻¹ * (1 + u * u) = 1 :=
    Rat.inv_mul_cancel _ hdenne
  grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_add, Rat.add_mul,
    Rat.sub_eq_add_neg]

theorem tangentSquareDensity_eq_circleSin_sq_mul_chartJacobian (u : Rat) :
    tangentSquareDensity u =
      RationalCircle.Trigonometry.sin u *
          RationalCircle.Trigonometry.sin u *
          (2 / (1 + u * u)) := by
  rw [RationalCircle.Trigonometry.sin_eq]
  have hden : 1 + u * u ≠ 0 :=
    Rat.ne_of_gt (RationalCircle.Stage.one_add_square_pos u)
  rw [tangentSquareDensity, Rat.div_def, Rat.div_def, Rat.div_def]
  grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_add, Rat.add_mul,
    Rat.sub_eq_add_neg, Rat.mul_inv_cancel _ hden]

theorem tangentSquareRationalPart_zero :
    tangentSquareRationalPart 0 = 0 := by
  native_decide

theorem tangentSquareRationalPart_one :
    tangentSquareRationalPart 1 = 0 := by
  native_decide

/- The tangent-coordinate primitive is the arctangent geometry evaluator plus
the rational correction from the decomposition above.  The correction is
kept as an exact rational function, so this is a genuine computable function
object rather than only a symbolic antiderivative. -/
def tangentSquareRationalPrimitive (u : Rat) : Rat :=
  2 * tangentSquareRationalPart u

def tangentSquarePrimitiveOnUnit : RealFunRaw :=
  RealFunRaw.add IntegralIdentities.arctanGeomOnUnit.toRealFunRaw
    (RealFunRaw.exact tangentSquareRationalPrimitive)

theorem tangentSquarePrimitiveOnUnit_valid :
    tangentSquarePrimitiveOnUnit.Valid := by
  apply RealFunRaw.add_valid
  · exact FunctionOnInterval.toRealFunRaw_valid IntegralIdentities.arctanGeomOnUnit
  · exact RealFunRaw.exact_valid tangentSquareRationalPrimitive

theorem tangentSquareRationalPrimitive_zero :
    tangentSquareRationalPrimitive 0 = 0 := by
  simp [tangentSquareRationalPrimitive, tangentSquareRationalPart_zero]

theorem tangentSquareRationalPrimitive_one :
    tangentSquareRationalPrimitive 1 = 0 := by
  simp [tangentSquareRationalPrimitive, tangentSquareRationalPart_one]

theorem tangentSquarePrimitiveOnUnit_endpointDifference_compute_eq (n : Nat) :
    endpointDifferenceCompute tangentSquarePrimitiveOnUnit 0 1 n =
      (ArctanGeometry.arctanGeom (1 : Rat) -
        ArctanGeometry.arctanGeom (0 : Rat)).compute n := by
  simp only [endpointDifferenceCompute, endpointDifferenceInterval,
    tangentSquarePrimitiveOnUnit, RealFunRaw.add, RealFunRaw.exact]
  rw [IntegralIdentities.arctanGeomOnUnit_toRealFunRaw_compute_one n,
    IntegralIdentities.arctanGeomOnUnit_toRealFunRaw_compute_zero n,
    tangentSquareRationalPrimitive_one,
    tangentSquareRationalPrimitive_zero]
  change _ = QInterval.mk
    (((ArctanGeometry.arctanGeom (1 : Rat)).compute n).lo -
      ((ArctanGeometry.arctanGeom (0 : Rat)).compute n).hi)
    (((ArctanGeometry.arctanGeom (1 : Rat)).compute n).hi -
      ((ArctanGeometry.arctanGeom (0 : Rat)).compute n).lo)
  congr 1 <;> grind

theorem tangentSquarePrimitiveOnUnit_endpointDifference_valid :
    RealRaw.ValidCompute
      (endpointDifferenceCompute tangentSquarePrimitiveOnUnit 0 1) := by
  have hsub :
      (ArctanGeometry.arctanGeom (1 : Rat) -
        ArctanGeometry.arctanGeom (0 : Rat)).Valid :=
    RealRaw.sub_valid
      (ArctanGeometry.arctanGeom_valid_on_unit
        (x := (1 : Rat)) (by native_decide) (by native_decide))
      (ArctanGeometry.arctanGeom_valid_on_unit
        (x := (0 : Rat)) (by native_decide) (by native_decide))
  have hcompute :
      endpointDifferenceCompute tangentSquarePrimitiveOnUnit 0 1 =
        (ArctanGeometry.arctanGeom (1 : Rat) -
          ArctanGeometry.arctanGeom (0 : Rat)).compute := by
    funext n
    exact tangentSquarePrimitiveOnUnit_endpointDifference_compute_eq n
  rw [hcompute]
  exact hsub

theorem tangentSquarePrimitiveOnUnit_endpointDifference_equiv_arctan :
    (endpointDifferenceRaw tangentSquarePrimitiveOnUnit 0 1
      tangentSquarePrimitiveOnUnit_endpointDifference_valid).Equiv
        (ArctanGeometry.arctanGeom (1 : Rat) -
          ArctanGeometry.arctanGeom (0 : Rat)) := by
  apply RealRaw.sameStageOverlap_equiv
  intro n
  apply (RealRaw.compareAt_overlap_iff
    (endpointDifferenceRaw tangentSquarePrimitiveOnUnit 0 1
      tangentSquarePrimitiveOnUnit_endpointDifference_valid)
    (ArctanGeometry.arctanGeom (1 : Rat) -
      ArctanGeometry.arctanGeom (0 : Rat)) n n).2
  change QInterval.Overlaps
    (endpointDifferenceCompute tangentSquarePrimitiveOnUnit 0 1 n)
    ((ArctanGeometry.arctanGeom (1 : Rat) -
      ArctanGeometry.arctanGeom (0 : Rat)).compute n)
  rw [tangentSquarePrimitiveOnUnit_endpointDifference_compute_eq n]
  have hvalid :
      (ArctanGeometry.arctanGeom (1 : Rat) -
        ArctanGeometry.arctanGeom (0 : Rat)).Valid :=
    RealRaw.sub_valid
      (ArctanGeometry.arctanGeom_valid_on_unit
        (x := (1 : Rat)) (by native_decide) (by native_decide))
      (ArctanGeometry.arctanGeom_valid_on_unit
        (x := (0 : Rat)) (by native_decide) (by native_decide))
  have horder := RealRaw.interval_order_of_valid
    (ArctanGeometry.arctanGeom (1 : Rat) -
      ArctanGeometry.arctanGeom (0 : Rat)) hvalid n
  exact ⟨horder, horder⟩

theorem finiteSineSquarePrefix_effectiveFTC_equiv_endpoint :
    FiniteSinePrefix.sineTaylorPrefixThreeSquareEffectiveFTCData.toDerivativeBoundFTC.boundedIntegralRaw.Equiv
      FiniteSinePrefix.sineTaylorPrefixThreeSquareEffectiveFTCData.toDerivativeBoundFTC.endpointRaw := by
  exact FiniteSinePrefix.sineTaylorPrefixThreeSquareEffectiveFTC_equiv_endpoint

theorem finiteSineSquarePrefix_effectiveFTC_equiv_value :
    FiniteSinePrefix.sineTaylorPrefixThreeSquareEffectiveFTCData.toDerivativeBoundFTC.boundedIntegralRaw.Equiv
      (RealRaw.ofRat (6389 / 161280)) := by
  exact FiniteSinePrefix.sineTaylorPrefixThreeSquareEffectiveFTC_equiv_value

def sinPiOnHalfRaw (S : ArctanSinPiConstruction) : RealFunRaw where
  domain := fun x => 0 <= x /\ x <= (1 : Rat) / 2
  compute := fun x n =>
    if hx : 0 <= x /\ x <= (1 : Rat) / 2 then
      (sinPiRawOfArctan S.inverse x hx).compute n
    else
      { lo := 0, hi := 0 }

def sinPiSquareOnHalf (S : ArctanSinPiConstruction) : RealFunRaw :=
  RealFunRaw.mul (sinPiOnHalfRaw S) (sinPiOnHalfRaw S)

def rationalSquareInterval (I : QInterval) : QInterval :=
  { lo := I.lo * I.lo, hi := I.hi * I.hi }

def rationalOneMinusSquareInterval (I : QInterval) : QInterval :=
  { lo := 1 - I.hi * I.hi, hi := 1 - I.lo * I.lo }

/- The raw equal-dyadic square candidate.  Its validity/nesting certificate
is intentionally separate: this definition is only the finite algorithm. -/
def dyadicNestedRadicalSquareLeftSum (n : Nat) : QInterval :=
  let N := 2 ^ n
  let h := mesh 0 ((1 : Rat) / 2) N
  (List.range N).foldl
    (fun acc k =>
      QInterval.addInterval acc
        (QInterval.scaleByRat h
          (rationalSquareInterval (dyadicNestedRadicalStageSinAt n k))))
    { lo := 0, hi := 0 }

theorem dyadicNestedRadicalSquareStage_width_le
    (n k : Nat) (hk : k < 2 ^ n) :
    (rationalSquareInterval (dyadicNestedRadicalStageSinAt n k)).width <=
      2 / ((n + 1 : Nat) : Rat) := by
  have hbounds := dyadicNestedRadicalTableAt_bounds n n k (by omega)
  have hwidth := dyadicNestedRadicalStageSinAt_width_le n k hk
  have hbounds' : subintervalOf
      (dyadicNestedRadicalStageSinAt n k) 0 1 := by
    change subintervalOf (dyadicNestedRadicalTableAt n n k).1 0 1
    exact hbounds.1
  unfold rationalSquareInterval QInterval.width at *
  dsimp only at *
  have hfactor :
      (dyadicNestedRadicalStageSinAt n k).hi *
          (dyadicNestedRadicalStageSinAt n k).hi -
          (dyadicNestedRadicalStageSinAt n k).lo *
            (dyadicNestedRadicalStageSinAt n k).lo =
        ((dyadicNestedRadicalStageSinAt n k).hi -
          (dyadicNestedRadicalStageSinAt n k).lo) *
          ((dyadicNestedRadicalStageSinAt n k).hi +
            (dyadicNestedRadicalStageSinAt n k).lo) := by
    grind [Rat.mul_add, Rat.add_mul, Rat.mul_assoc,
      Rat.mul_comm, Rat.sub_eq_add_neg]
  rw [hfactor]
  have hsum :
      (dyadicNestedRadicalStageSinAt n k).hi +
          (dyadicNestedRadicalStageSinAt n k).lo <= 2 := by
    have hlo1 :
        (dyadicNestedRadicalStageSinAt n k).lo <= 1 :=
      Rat.le_trans hbounds'.2.1 hbounds'.2.2
    have hsum' := rat_add_le_add hbounds'.2.2 hlo1
    grind
  have hgap : 0 <=
      (dyadicNestedRadicalStageSinAt n k).hi -
        (dyadicNestedRadicalStageSinAt n k).lo := by
    have h := (Rat.add_le_add_left (c :=
      -(dyadicNestedRadicalStageSinAt n k).lo)).2 hbounds'.2.1
    have hzero :
        -(dyadicNestedRadicalStageSinAt n k).lo +
            (dyadicNestedRadicalStageSinAt n k).lo = 0 := by
      grind
    rw [hzero] at h
    simpa [Rat.sub_eq_add_neg, Rat.add_comm] using h
  have hscaled := Rat.mul_le_mul_of_nonneg_left hsum hgap
  calc
    ((dyadicNestedRadicalStageSinAt n k).hi -
        (dyadicNestedRadicalStageSinAt n k).lo) *
        ((dyadicNestedRadicalStageSinAt n k).hi +
          (dyadicNestedRadicalStageSinAt n k).lo) <=
        2 * (dyadicNestedRadicalStageSinAt n k).width := by
          simpa [QInterval.width, Rat.mul_comm] using hscaled
    _ <= 2 / ((n + 1 : Nat) : Rat) := by
      have hwidth' := Rat.mul_le_mul_of_nonneg_left
        (by simpa [QInterval.width, Rat.div_def] using hwidth)
        (by native_decide : (0 : Rat) <= 2)
      simpa [QInterval.width, Rat.div_def] using hwidth'

theorem dyadicNestedRadicalSquareLeftSum_width_le
    (n : Nat) :
    (dyadicNestedRadicalSquareLeftSum n).width <=
      1 / ((n + 1 : Nat) : Rat) := by
  let N := 2 ^ n
  have hN : 0 < N := by
    dsimp [N]
    exact Nat.pow_pos (by omega)
  have hmesh : 0 <= mesh 0 ((1 : Rat) / 2) N :=
    mesh_nonneg_of_le hN (by native_decide)
  have hsum := RationalPartition.rat_add_fold_le_length_mul (List.range N)
    (fun k =>
      (QInterval.scaleByRat (mesh 0 ((1 : Rat) / 2) N)
        (rationalSquareInterval (dyadicNestedRadicalStageSinAt n k))).width)
    (mesh 0 ((1 : Rat) / 2) N *
      (2 / ((n + 1 : Nat) : Rat))) (by
      intro k hk
      have hklt : k < N := List.mem_range.mp hk
      rw [QInterval.scaleByRat_width_of_nonneg hmesh]
      exact Rat.mul_le_mul_of_nonneg_left
        (dyadicNestedRadicalSquareStage_width_le n k
          (by simpa [N] using hklt)) hmesh)
  calc
    (dyadicNestedRadicalSquareLeftSum n).width =
        (List.range N).foldl
          (fun total k => total +
            (QInterval.scaleByRat (mesh 0 ((1 : Rat) / 2) N)
              (rationalSquareInterval
                (dyadicNestedRadicalStageSinAt n k))).width) 0 := by
      unfold dyadicNestedRadicalSquareLeftSum
      rw [RationalPartition.addInterval_fold_width]
      have hzero : ({ lo := 0, hi := 0 } : QInterval).width = 0 := by
        unfold QInterval.width
        grind
      rw [hzero]
      simp [N]
      grind
    _ <= (N : Rat) * (mesh 0 ((1 : Rat) / 2) N *
      (2 / ((n + 1 : Nat) : Rat))) := by simpa using hsum
    _ = 1 / ((n + 1 : Nat) : Rat) := by
      have hmesh_total := natCast_mul_mesh_eq_sub
        (a := (0 : Rat)) (b := (1 : Rat) / 2) hN
      rw [show (N : Rat) *
          (mesh 0 ((1 : Rat) / 2) N *
            (2 / ((n + 1 : Nat) : Rat))) =
          ((N : Rat) * mesh 0 ((1 : Rat) / 2) N) *
            (2 / ((n + 1 : Nat) : Rat)) by
          grind [Rat.mul_assoc]]
      rw [hmesh_total]
      have hden : ((n + 1 : Nat) : Rat) ≠ 0 := by
        exact_mod_cast (Nat.succ_ne_zero n)
      rw [Rat.div_def, Rat.div_def, Rat.div_def]
      grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel _ hden]

def dyadicNestedRadicalSquareIntegralRaw : RealRaw where
  compute := dyadicNestedRadicalSquareLeftSum

theorem dyadicNestedRadicalSquareIntegralRaw_widths_shrink :
    RealRaw.WidthsShrinkToZero
      dyadicNestedRadicalSquareIntegralRaw.compute := by
  change RealRaw.WidthsShrinkToZero dyadicNestedRadicalSquareLeftSum
  exact shrinksToZero_of_natOverSuccBound
    (fun n => dyadicNestedRadicalSquareLeftSum_width_le n)

/- The finite rational-circle identity used by the future primitive proof.
   Keeping this as an algebraic theorem makes the intended `sin²` route
   explicit before any interval-level cosine transport is added. -/
theorem rationalCircleSin_sq_eq_one_sub_cos_sq (u : Rat) :
    rationalCircleSin u * rationalCircleSin u =
      1 - rationalCircleCos u * rationalCircleCos u := by
  have h := rationalCircleSin_sq_add_cos_sq u
  grind

/-! A box-level form of the circle identity.  It is intentionally stated for
rational witness values: the later nested-radical transport supplies such
witnesses through its tangent-box overlap certificates. -/

theorem rationalSquareInterval_overlap_of_interval_overlap
    {I J : QInterval}
    (hI : subintervalOf I 0 1)
    (hJ : subintervalOf J 0 1)
    (hover : QInterval.Overlaps I J) :
    QInterval.Overlaps (rationalSquareInterval I)
      (rationalSquareInterval J) := by
  have hIlo : 0 <= I.lo := hI.1
  have hJlo : 0 <= J.lo := hJ.1
  have hIhi : I.hi <= 1 := hI.2.2
  have hJhi : J.hi <= 1 := hJ.2.2
  have hIorder : I.lo <= I.hi := hI.2.1
  have hJorder : J.lo <= J.hi := hJ.2.1
  have hsquare_mono {a b : Rat} (ha : 0 <= a) (hab : a <= b) :
      a * a <= b * b := by
    have hb : 0 <= b := Rat.le_trans ha hab
    exact Rat.le_trans
      (Rat.mul_le_mul_of_nonneg_left hab ha)
      (Rat.mul_le_mul_of_nonneg_right hab hb)
  unfold rationalSquareInterval QInterval.Overlaps
  constructor
  · exact hsquare_mono hIlo hover.1
  · exact hsquare_mono hJlo hover.2

theorem rationalSquareInterval_mul_self_eq
    {I : QInterval} (hI : subintervalOf I 0 1) :
    QBox.mulRealInterval I.lo I.hi I.lo I.hi =
      rationalSquareInterval I := by
  have horder : I.lo <= I.hi := hI.2.1
  unfold rationalSquareInterval
  exact QBox.mulRealInterval_self_of_nonneg hI.1 horder

theorem sinPiSquareOnHalf_compute_of_mem
    (S : ArctanSinPiConstruction) {x : Rat}
    (hx : 0 <= x /\ x <= (1 : Rat) / 2) (n : Nat) :
    (sinPiSquareOnHalf S).compute x n =
      QBox.mulRealInterval
        ((sinPiRawOfArctan S.inverse x hx).compute n).lo
        ((sinPiRawOfArctan S.inverse x hx).compute n).hi
        ((sinPiRawOfArctan S.inverse x hx).compute n).lo
        ((sinPiRawOfArctan S.inverse x hx).compute n).hi := by
  change QBox.mulRealInterval
      ((sinPiOnHalfRaw S).compute x n).lo
      ((sinPiOnHalfRaw S).compute x n).hi
      ((sinPiOnHalfRaw S).compute x n).lo
      ((sinPiOnHalfRaw S).compute x n).hi = _
  rw [show (sinPiOnHalfRaw S).compute x n =
      (sinPiRawOfArctan S.inverse x hx).compute n by
        simp [sinPiOnHalfRaw, hx]]

theorem sinPiSquare_sample_overlap_of_sine_and_table_overlap
    (S : ArctanSinPiConstruction) {x : Rat}
    (hx : 0 <= x /\ x <= (1 : Rat) / 2) (n : Nat)
    {T : QInterval}
    (hT : subintervalOf T 0 1)
    (hsample : QInterval.Overlaps
      ((sinPiRawOfArctan S.inverse x hx).compute n) T) :
    QInterval.Overlaps
      ((sinPiSquareOnHalf S).compute x n)
      (rationalSquareInterval T) := by
  have hS : subintervalOf
      ((sinPiRawOfArctan S.inverse x hx).compute n) 0 1 := by
    have hb := S.sinPiRawOfArctan_bounds hx n
    have hv := S.sin_valid x hx
    have ho := RealRaw.interval_order_of_valid
      (x := (sinPiRawOfArctan S.inverse x hx)) hv n
    exact ⟨hb.1, ho, hb.2⟩
  rw [sinPiSquareOnHalf_compute_of_mem S hx n,
    rationalSquareInterval_mul_self_eq hS]
  exact rationalSquareInterval_overlap_of_interval_overlap
    hS hT hsample

theorem sinPiSquare_nestedRadicalStage_sample_overlap_of_canonical_box_search
    (S : ArctanSinPiConstruction)
    {n k : Nat} (hk : k < 2 ^ n) (m : Nat) (u : Rat)
    (hsearch : rationalTangentWitnessBoxSearch
      (dyadicTangentBox S.inverse hk)
      (dyadicNestedRadicalStageSinAt n k) m = some u) :
    QInterval.Overlaps
      ((sinPiSquareOnHalf S).compute
        (leftPoint 0 ((1 : Rat) / 2) (2 ^ n) k) n)
      (rationalSquareInterval (dyadicNestedRadicalStageSinAt n k)) := by
  have hsin :=
    arctanSinPi_nestedRadicalStage_sample_overlap_of_canonical_box_search
      S.inverse hk m u hsearch
  exact sinPiSquare_sample_overlap_of_sine_and_table_overlap S
    (dyadicHalfDomain hk) n
    (by
      change subintervalOf
        (dyadicNestedRadicalTableAt n n k).1 0 1
      exact (dyadicNestedRadicalTableAt_bounds n n k
        (Nat.le_of_lt hk)).1)
    (by simpa [sinPiSquareOnHalf, sinPiOnHalfRaw] using hsin)

theorem square_sample_overlap_of_sine_sample_overlap
    {I J : QInterval}
    (hI : subintervalOf I 0 1)
    (hJ : subintervalOf J 0 1)
    (hover : QInterval.Overlaps I J) :
    QInterval.Overlaps
      (QBox.mulRealInterval I.lo I.hi I.lo I.hi)
      (QBox.mulRealInterval J.lo J.hi J.lo J.hi) := by
  rw [rationalSquareInterval_mul_self_eq hI,
    rationalSquareInterval_mul_self_eq hJ]
  exact rationalSquareInterval_overlap_of_interval_overlap hI hJ hover

theorem rationalSquareInterval_overlap_oneMinusSquareInterval_of_circle
    {S C : QInterval} {s c : Rat}
    (hS : subintervalOf S 0 1) (hC : subintervalOf C 0 1)
    (hs : S.lo <= s ∧ s <= S.hi) (hc : C.lo <= c ∧ c <= C.hi)
    (hcircle : s * s + c * c = 1) :
    QInterval.Overlaps (rationalSquareInterval S)
      (rationalOneMinusSquareInterval C) := by
  have hSlo : 0 <= S.lo := hS.1
  have hChi : C.hi <= 1 := hC.2.2
  have hs0 : 0 <= s := Rat.le_trans hSlo hs.1
  have hc0 : 0 <= c := Rat.le_trans hC.1 hc.1
  have Shi0 : 0 <= S.hi := Rat.le_trans hSlo hS.2.1
  have Clo0 : 0 <= C.lo := hC.1
  have Chi0 : 0 <= C.hi := Rat.le_trans Clo0 hC.2.1
  have hSsq_lo : S.lo * S.lo <= s * s := by
    have h := Rat.mul_le_mul_of_nonneg_right hs.1
      (Rat.add_nonneg hs0 hSlo)
    grind [Rat.mul_add, Rat.add_mul]
  have hSsq_hi : s * s <= S.hi * S.hi := by
    have h := Rat.mul_le_mul_of_nonneg_right hs.2
      (Rat.add_nonneg hs0 Shi0)
    grind [Rat.mul_add, Rat.add_mul]
  have hCsq_lo : C.lo * C.lo <= c * c := by
    have h := Rat.mul_le_mul_of_nonneg_right hc.1
      (Rat.add_nonneg hc0 Clo0)
    grind [Rat.mul_add, Rat.add_mul]
  have hCsq_hi : c * c <= C.hi * C.hi := by
    have h := Rat.mul_le_mul_of_nonneg_right hc.2
      (Rat.add_nonneg hc0 Chi0)
    grind [Rat.mul_add, Rat.add_mul]
  have hsquare_mem :
      S.lo * S.lo <= s * s ∧ s * s <= S.hi * S.hi :=
    ⟨hSsq_lo, hSsq_hi⟩
  have hcomplement_mem :
      1 - C.hi * C.hi <= 1 - c * c ∧
        1 - c * c <= 1 - C.lo * C.lo := by
    constructor <;> grind
  unfold rationalSquareInterval rationalOneMinusSquareInterval
    QInterval.Overlaps
  change S.lo * S.lo <= 1 - C.lo * C.lo ∧
    1 - C.hi * C.hi <= S.hi * S.hi
  constructor
  · calc
      S.lo * S.lo <= s * s := hsquare_mem.1
      _ = 1 - c * c := by grind
      _ <= 1 - C.lo * C.lo := hcomplement_mem.2
  · calc
      1 - C.hi * C.hi <= 1 - c * c := hcomplement_mem.1
      _ = s * s := by grind
      _ <= S.hi * S.hi := hsquare_mem.2

/-! A square-aware variant of the finite tangent search.  The existing search
checks only the sine box; this predicate checks both circle coordinates, so a
successful result can be consumed by the square/complement transport above. -/

def rationalTangentSquareWitnessAdmissibleBool
    (U S C : QInterval) (u : Rat) : Bool :=
  (U.lo <= u) && (u <= U.hi) &&
    (S.lo <= rationalCircleSin u) &&
    (rationalCircleSin u <= S.hi) &&
    (C.lo <= rationalCircleCos u) &&
    (rationalCircleCos u <= C.hi)

def rationalTangentSquareWitnessSearchList
    (U S C : QInterval) : List Rat -> Option Rat
  | [] => none
  | u :: us =>
      if rationalTangentSquareWitnessAdmissibleBool U S C u then some u
      else rationalTangentSquareWitnessSearchList U S C us

theorem rationalTangentSquareWitnessSearchList_sound
    {U S C : QInterval} {us : List Rat} {u : Rat}
    (h : rationalTangentSquareWitnessSearchList U S C us = some u) :
    rationalTangentSquareWitnessAdmissibleBool U S C u = true := by
  induction us with
  | nil => simp [rationalTangentSquareWitnessSearchList] at h
  | cons v vs ih =>
      simp only [rationalTangentSquareWitnessSearchList] at h
      split at h
      · cases h
        assumption
      · exact ih h

theorem rationalTangentSquareWitnessSearchList_complete
    {U S C : QInterval} {us : List Rat} {u : Rat}
    (hmem : u ∈ us)
    (hadm : rationalTangentSquareWitnessAdmissibleBool U S C u = true) :
    ∃ v, rationalTangentSquareWitnessSearchList U S C us = some v := by
  induction us with
  | nil => simp at hmem
  | cons q qs ih =>
      simp only [List.mem_cons] at hmem
      simp only [rationalTangentSquareWitnessSearchList]
      split
      · exact ⟨q, rfl⟩
      · rcases hmem with rfl | hmem
        · contradiction
        · exact ih hmem

def rationalTangentSquareWitnessSearch
    (U S C : QInterval) (m : Nat) : Option Rat :=
  rationalTangentSquareWitnessSearchList U S C
    (rationalTangentWitnessBoxGrid U m)

theorem rationalTangentSquareWitnessSearch_complete_of_grid_candidate
    {U S C : QInterval} (m k : Nat) (hk : k <= 2 ^ m)
    (hadm : rationalTangentSquareWitnessAdmissibleBool U S C
      (U.lo + U.width * ((k : Rat) / ((2 ^ m : Nat) : Rat))) = true) :
    ∃ v, rationalTangentSquareWitnessSearch U S C m = some v := by
  apply rationalTangentSquareWitnessSearchList_complete
    (u := U.lo + U.width * ((k : Rat) / ((2 ^ m : Nat) : Rat)))
  · unfold rationalTangentWitnessBoxGrid
    let N := 2 ^ m
    have hk' : k < N + 1 := by dsimp [N]; omega
    apply List.mem_map.mpr
    exact ⟨k, by simpa using hk', rfl⟩
  · exact hadm

theorem rationalTangentSquareWitnessSearch_sound
    {U S C : QInterval} {m : Nat} {u : Rat}
    (h : rationalTangentSquareWitnessSearch U S C m = some u) :
    U.lo <= u /\ u <= U.hi /\
      S.lo <= rationalCircleSin u /\ rationalCircleSin u <= S.hi /\
      C.lo <= rationalCircleCos u /\ rationalCircleCos u <= C.hi := by
  have hb := rationalTangentSquareWitnessSearchList_sound h
  simp only [rationalTangentSquareWitnessAdmissibleBool,
    Bool.and_eq_true] at hb
  refine ⟨of_decide_eq_true hb.1.1.1.1.1,
    of_decide_eq_true hb.1.1.1.1.2,
    of_decide_eq_true hb.1.1.1.2,
    of_decide_eq_true hb.1.1.2,
    of_decide_eq_true hb.1.2,
    of_decide_eq_true hb.2⟩

theorem CanonicalDyadicHalfAngleCertificateAt.to_square_complement_overlap
    {B : IntegralIdentities.ArctanInverseBisection}
    {precision depth k : Nat} {hk : k < 2 ^ depth}
    (h : CanonicalDyadicHalfAngleCertificateAt B precision depth k hk) :
    QInterval.Overlaps
      (rationalSquareInterval
        (dyadicNestedRadicalTableAt precision depth k).1)
      (rationalOneMinusSquareInterval h.cosineBox) := by
  exact rationalSquareInterval_overlap_oneMinusSquareInterval_of_circle
    (dyadicNestedRadicalTableAt_bounds precision depth k
      (Nat.le_of_lt hk)).1
    h.cosineBox_subinterval h.sine_contains h.cosine_contains
    h.circle_identity

theorem canonical_dyadic_certificate_at_of_rational_witness_square_overlap
    (B : IntegralIdentities.ArctanInverseBisection)
    {precision depth k : Nat} (hk : k < 2 ^ depth)
    (u : Rat) (hu0 : 0 <= u) (hu1 : u <= 1)
    (hsine : (dyadicNestedRadicalTableAt precision depth k).1.lo <=
        rationalCircleSin u /\
      rationalCircleSin u <=
        (dyadicNestedRadicalTableAt precision depth k).1.hi)
    (houter : (dyadicTangentBoxAt B precision depth k hk).ContainsInterval
      (rationalHalfAngleTangentInterval
        ((dyadicNestedRadicalTableAt precision depth k).1)
        { lo := rationalCircleCos u, hi := rationalCircleCos u })) :
    QInterval.Overlaps
      (rationalSquareInterval
        (dyadicNestedRadicalTableAt precision depth k).1)
      (rationalOneMinusSquareInterval
        ({ lo := rationalCircleCos u, hi := rationalCircleCos u } : QInterval)) := by
  let h := canonical_dyadic_certificate_at_of_rational_witness
    B hk u hu0 hu1 hsine houter
  exact h.to_square_complement_overlap

/-! The same transport target, named at a dyadic nested-radical sample.  The
remaining witness-search proof only has to supply the two interval-membership
facts and the rational circle equation. -/

def dyadicNestedRadicalStageCosAt (n k : Nat) : QInterval :=
  (dyadicNestedRadicalStageTable n k).2

theorem dyadicNestedRadicalStage_square_complement_overlap
    {n k : Nat} (_hk : k <= 2 ^ n) (s c : Rat)
    (hS : subintervalOf (dyadicNestedRadicalStageSinAt n k) 0 1)
    (hC : subintervalOf (dyadicNestedRadicalStageCosAt n k) 0 1)
    (hs : (dyadicNestedRadicalStageSinAt n k).lo <= s ∧
      s <= (dyadicNestedRadicalStageSinAt n k).hi)
    (hc : (dyadicNestedRadicalStageCosAt n k).lo <= c ∧
      c <= (dyadicNestedRadicalStageCosAt n k).hi)
    (hcircle : s * s + c * c = 1) :
    QInterval.Overlaps
      (rationalSquareInterval (dyadicNestedRadicalStageSinAt n k))
      (rationalOneMinusSquareInterval
        (dyadicNestedRadicalStageCosAt n k)) := by
  exact rationalSquareInterval_overlap_oneMinusSquareInterval_of_circle
    hS hC hs hc hcircle

theorem sinPiSquareOnHalf_valid (S : ArctanSinPiConstruction) :
    (sinPiSquareOnHalf S).Valid := by
  have hvalid : (sinPiOnHalfRaw S).Valid := by
    intro x hx
    change RealRaw.ValidCompute
      (fun n => if h : 0 <= x /\ x <= (1 : Rat) / 2 then
        (sinPiRawOfArctan S.inverse x h).compute n else { lo := 0, hi := 0 })
    split
    · exact S.sin_valid x hx
    · rename_i hfalse
      exact False.elim (hfalse hx)
  apply RealFunRaw.mul_valid_of_nonneg_bounded
    hvalid hvalid
  · intro x hx
    refine ⟨1, by native_decide, ?_⟩
    intro n
    change 0 <= (if h : 0 <= x /\ x <= (1 : Rat) / 2 then
      (sinPiRawOfArctan S.inverse x h).compute n else { lo := 0, hi := 0 }).lo /\
      (if h : 0 <= x /\ x <= (1 : Rat) / 2 then
        (sinPiRawOfArctan S.inverse x h).compute n else { lo := 0, hi := 0 }).hi <= 1
    split
    · exact S.sinPiRawOfArctan_bounds hx n
    · rename_i hfalse
      exact False.elim (hfalse hx)
  · intro x hx
    refine ⟨1, by native_decide, ?_⟩
    intro n
    change 0 <= (if h : 0 <= x /\ x <= (1 : Rat) / 2 then
      (sinPiRawOfArctan S.inverse x h).compute n else { lo := 0, hi := 0 }).lo /\
      (if h : 0 <= x /\ x <= (1 : Rat) / 2 then
        (sinPiRawOfArctan S.inverse x h).compute n else { lo := 0, hi := 0 }).hi <= 1
    split
    · exact S.sinPiRawOfArctan_bounds hx n
    · rename_i hfalse
      exact False.elim (hfalse hx)

/-!
## The effective-FTC acceptance interface

The structure below is deliberately the concrete subgoal for the squared-sine
application.  It does not postulate an analytic primitive: an inhabitant must
provide a computable primitive and the finite local endpoint controls required
by `EffectiveDerivativeBoundFTC`.  Once those data exist, the generic closure
theorem supplies the FTC equivalence.
-/

structure SinPiSquareEffectiveFTCData
    (S : ArctanSinPiConstruction) where
  primitive : RealFunRaw
  certificate :
    EffectiveDerivativeBoundFTC primitive (sinPiSquareOnHalf S) 0 ((1 : Rat) / 2)
  integral_valid :
    certificate.toDerivativeBoundFTC.boundedIntegralRaw.Valid
  endpoint_valid :
    certificate.toDerivativeBoundFTC.endpointRaw.Valid

def SinPiSquareEffectiveFTCData.integralRaw
    {S : ArctanSinPiConstruction}
    (D : SinPiSquareEffectiveFTCData S) : RealRaw :=
  D.certificate.toDerivativeBoundFTC.boundedIntegralRaw

def SinPiSquareEffectiveFTCData.endpointRaw
    {S : ArctanSinPiConstruction}
    (D : SinPiSquareEffectiveFTCData S) : RealRaw :=
  D.certificate.toDerivativeBoundFTC.endpointRaw

theorem SinPiSquareEffectiveFTCData.integral_equiv_endpoint
    {S : ArctanSinPiConstruction}
    (D : SinPiSquareEffectiveFTCData S) :
    D.integralRaw.Equiv D.endpointRaw := by
  exact effectiveDerivativeBoundFTC D.certificate

theorem SinPiSquareEffectiveFTCData.endpoint_equiv_of_value
    {S : ArctanSinPiConstruction}
    (D : SinPiSquareEffectiveFTCData S)
    (hvalue : D.endpointRaw.Equiv (RealRaw.ofRat (1 / 4))) :
    D.integralRaw.Equiv (RealRaw.ofRat (1 / 4)) := by
  exact RealRaw.equiv_trans
    D.integral_valid D.endpoint_valid (RealRaw.ofRat_valid _)
    D.integral_equiv_endpoint hvalue

end SinPiIntegral

end ComputableAnalysis
