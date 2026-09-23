import ComputableAnalysis.ComplexLogarithmSecant

/-!
# Secant certificate for the completed local complex logarithm

The finite-prefix estimate is uniform in the Taylor depth.  This module
transfers it to the actual rational centers returned by the stabilized value
and derivative evaluators.  At one synchronized stage, the only additional
errors are the two value-box radii and the derivative-box radius multiplied
by the increment.  A finite half-geometric schedule makes their sum smaller
than any requested positive rational tolerance.
-/

namespace ComputableAnalysis
namespace ComplexLogarithmCompletedSecant

private def half : Rat := (1 : Rat) / 2

open ComplexLogarithmSecant

/-- A point contained in an ordered rational complex box is within the sum
of the two coordinate widths of the box center. -/
theorem center_sub_point_normBound_le_width_add_height
    {box : QBox} {point : QComplex}
    (hbox : box.Ordered) (hpoint : (QBox.point point).NestedIn box) :
    QComplex.normBound (QComplex.sub box.center point) <=
      box.width + box.height := by
  have hcenter := QBox.center_mem hbox
  have hpointBounds : box.lo <= point /\ point <= box.hi := by
    change box.lo <= point /\ point <= box.hi at hpoint
    exact hpoint
  have hre : qabs (box.center.re - point.re) <= box.width :=
    qabs_sub_le_of_common_bounds hcenter.1.1 hcenter.2.1
      hpointBounds.1.1 hpointBounds.2.1
  have him : qabs (box.center.im - point.im) <= box.height :=
    qabs_sub_le_of_common_bounds hcenter.1.2 hcenter.2.2
      hpointBounds.1.2 hpointBounds.2.2
  simpa only [QComplex.normBound, QComplex.sub, QComplex.add, QComplex.neg,
    QBox.width, QBox.height, Rat.sub_eq_add_neg] using rat_add_le_add hre him

private theorem derivativeRawAt_contained_current_expand
    (w : QComplex) (stage : Nat) :
    ((ComplexLogarithmJet.derivativeRawAt w).compute stage).NestedIn
      (QBox.expand
        ((ComplexLogarithmJet.derivativeDirectCandidate w).compute stage)
        (ComplexLogarithmJet.derivativeStageRadius stage)) := by
  cases stage with
  | zero =>
      exact ⟨QComplex.le_refl _, QComplex.le_refl _⟩
  | succ stage =>
      change (QBox.intersection
        (ComplexRaw.cauchyStabilizeCompute
          (ComplexLogarithmJet.derivativeDirectCandidate w).compute
          ComplexLogarithmJet.derivativeStageRadius stage)
        (QBox.expand
          ((ComplexLogarithmJet.derivativeDirectCandidate w).compute
            (stage + 1))
          (ComplexLogarithmJet.derivativeStageRadius (stage + 1)))).NestedIn
        (QBox.expand
          ((ComplexLogarithmJet.derivativeDirectCandidate w).compute
            (stage + 1))
          (ComplexLogarithmJet.derivativeStageRadius (stage + 1)))
      exact QBox.intersection_contained_right _ _

/-- Both coordinate widths of the completed derivative evaluator decay with
the explicit bound `4 / 2^stage`. -/
theorem derivativeRawAt_width_height_geometric
    (w : QComplex) (stage : Nat) :
    ((ComplexLogarithmJet.derivativeRawAt w).compute stage).width <=
        4 * half ^ stage /\
      ((ComplexLogarithmJet.derivativeRawAt w).compute stage).height <=
        4 * half ^ stage := by
  have hnested := derivativeRawAt_contained_current_expand w stage
  have hwidthHeight := QBox.width_height_le_of_nested hnested
  rw [QBox.expand_width, QBox.expand_height,
    ComplexLogarithmJet.derivativeStageRadius_eq_two_mul_half_pow]
    at hwidthHeight
  simp only [ComplexLogarithmJet.derivativeDirectCandidate, QBox.point,
    QBox.width, QBox.height, Rat.sub_self, Rat.zero_add]
    at hwidthHeight
  have hwidth :
      ((ComplexLogarithmJet.derivativeRawAt w).compute stage).width <=
        2 * (2 * half ^ stage) := hwidthHeight.1
  have hheight :
      ((ComplexLogarithmJet.derivativeRawAt w).compute stage).height <=
        2 * (2 * half ^ stage) := hwidthHeight.2
  constructor
  · exact Rat.le_trans hwidth (by
      grind [Rat.mul_assoc, Rat.mul_comm])
  · exact Rat.le_trans hheight (by
      grind [Rat.mul_assoc, Rat.mul_comm])

/-- Error between the completed value evaluator's current box center and its
exact Taylor prefix at the same stage. -/
def valueCenterError (w : QComplex) (stage : Nat) : QComplex :=
  QComplex.sub
    ((ComplexLogarithmApproximation.logOnePlusRawAt w).compute stage).center
    (ComplexLogarithmApproximation.logPrefix w stage)

theorem valueCenterError_normBound_le {w : QComplex}
    (hw : QComplex.normBound w <= half) (stage : Nat) :
    QComplex.normBound (valueCenterError w stage) <= 4 * half ^ stage := by
  have hvalid := ComplexLogarithmApproximation.logOnePlusRawAt_valid hw
  have hcenter := center_sub_point_normBound_le_width_add_height
    (ComplexRaw.valid_ordered hvalid stage)
    (ComplexLogarithmApproximation.logOnePlusRawAt_contains_prefix hw stage)
  have hwidth :=
    ComplexLogarithmApproximation.logOnePlusRawAt_width_height_geometric
      w stage
  have hwidth' :
      ((ComplexLogarithmApproximation.logOnePlusRawAt w).compute stage).width <=
        2 * half ^ stage := hwidth.1
  have hheight' :
      ((ComplexLogarithmApproximation.logOnePlusRawAt w).compute stage).height <=
        2 * half ^ stage := hwidth.2
  unfold valueCenterError
  grind [Rat.mul_add, Rat.add_mul, Rat.mul_assoc]

/-- Error between the completed derivative evaluator's current box center
and its exact geometric prefix at the same stage. -/
def derivativeCenterError (w : QComplex) (stage : Nat) : QComplex :=
  QComplex.sub
    ((ComplexLogarithmJet.derivativeRawAt w).compute stage).center
    (ComplexLogarithmJet.derivativePrefix w stage)

theorem derivativeCenterError_normBound_le {w : QComplex}
    (hw : QComplex.normBound w <= half) (stage : Nat) :
    QComplex.normBound (derivativeCenterError w stage) <=
      8 * half ^ stage := by
  have hvalid := ComplexLogarithmJet.derivativeRawAt_valid hw
  have hcenter := center_sub_point_normBound_le_width_add_height
    (ComplexRaw.valid_ordered hvalid stage)
    (ComplexLogarithmJet.derivativeRawAt_contains_prefix hw stage)
  have hwidth := derivativeRawAt_width_height_geometric w stage
  unfold derivativeCenterError
  grind [Rat.mul_add, Rat.add_mul, Rat.mul_assoc]

/-- The linear remainder formed from the actual synchronized centers returned
by the completed value and derivative evaluators. -/
def centerLinearRemainder (w h : QComplex) (stage : Nat) : QComplex :=
  QComplex.sub
    (QComplex.sub
      ((ComplexLogarithmApproximation.logOnePlusRawAt
        (QComplex.add w h)).compute stage).center
      ((ComplexLogarithmApproximation.logOnePlusRawAt w).compute stage).center)
    (QComplex.mul
      ((ComplexLogarithmJet.derivativeRawAt w).compute stage).center h)

/-- Exact decomposition into the finite-prefix remainder and the three
representation errors introduced by sampling completed evaluator boxes. -/
theorem centerLinearRemainder_eq_prefix_add_errors
    (w h : QComplex) (stage : Nat) :
    centerLinearRemainder w h stage =
      QComplex.add (prefixLinearRemainder w h stage)
        (QComplex.sub
          (QComplex.sub (valueCenterError (QComplex.add w h) stage)
            (valueCenterError w stage))
          (QComplex.mul (derivativeCenterError w stage) h)) := by
  cases w with
  | mk wre wim =>
      cases h with
      | mk hre him =>
          cases hplusCenter :
              ((ComplexLogarithmApproximation.logOnePlusRawAt
                (QComplex.add { re := wre, im := wim }
                  { re := hre, im := him })).compute stage).center with
          | mk plusCenterRe plusCenterIm =>
              cases hbaseCenter :
                  ((ComplexLogarithmApproximation.logOnePlusRawAt
                    { re := wre, im := wim }).compute stage).center with
              | mk baseCenterRe baseCenterIm =>
                  cases hderivativeCenter :
                      ((ComplexLogarithmJet.derivativeRawAt
                        { re := wre, im := wim }).compute stage).center with
                  | mk derivativeCenterRe derivativeCenterIm =>
                      cases hplusPrefix :
                          ComplexLogarithmApproximation.logPrefix
                            (QComplex.add { re := wre, im := wim }
                              { re := hre, im := him }) stage with
                      | mk plusPrefixRe plusPrefixIm =>
                          cases hbasePrefix :
                              ComplexLogarithmApproximation.logPrefix
                                { re := wre, im := wim } stage with
                          | mk basePrefixRe basePrefixIm =>
                              cases hderivativePrefix :
                                  ComplexLogarithmJet.derivativePrefix
                                    { re := wre, im := wim } stage with
                              | mk derivativePrefixRe derivativePrefixIm =>
                                  simp [centerLinearRemainder,
                                    prefixLinearRemainder, valueCenterError,
                                    derivativeCenterError, QComplex.add,
                                    QComplex.sub, QComplex.neg, QComplex.mul,
                                    hbaseCenter, hderivativeCenter,
                                    hbasePrefix, hderivativePrefix]
                                  constructor <;>
                                    grind [Rat.sub_eq_add_neg, Rat.mul_add,
                                      Rat.add_mul, Rat.mul_assoc,
                                      Rat.mul_comm, Rat.add_assoc,
                                      Rat.add_comm, Rat.neg_mul, Rat.mul_neg,
                                      Rat.neg_neg]

/-- Before scheduling, the completed-center secant estimate is the uniform
quadratic prefix bound plus one explicit half-geometric representation tail. -/
theorem centerLinearRemainder_normBound_le
    {w h : QComplex} {H : Rat}
    (hw : QComplex.normBound w <= half)
    (hwh : QComplex.normBound (QComplex.add w h) <= half)
    (hH : 0 <= H) (hh : QComplex.normBound h <= H)
    (stage : Nat) :
    QComplex.normBound (centerLinearRemainder w h stage) <=
      2 * H * H + 8 * (1 + H) * half ^ stage := by
  rw [centerLinearRemainder_eq_prefix_add_errors]
  have hprefix :=
    prefixLinearRemainder_normBound_le_uniformHalfBall
      hw hwh hH hh stage
  have hplus := valueCenterError_normBound_le hwh stage
  have hbase := valueCenterError_normBound_le hw stage
  have hderivative := derivativeCenterError_normBound_le hw stage
  have hmul : QComplex.normBound
      (QComplex.mul (derivativeCenterError w stage) h) <=
        (8 * half ^ stage) * H := by
    calc
      QComplex.normBound
          (QComplex.mul (derivativeCenterError w stage) h) <=
        QComplex.normBound (derivativeCenterError w stage) *
          QComplex.normBound h := QComplex.normBound_mul_le _ _
      _ <= (8 * half ^ stage) * QComplex.normBound h :=
        Rat.mul_le_mul_of_nonneg_right hderivative
          (QComplex.normBound_nonneg h)
      _ <= (8 * half ^ stage) * H :=
        Rat.mul_le_mul_of_nonneg_left hh
          (Rat.mul_nonneg (by decide +kernel)
            (Rat.pow_nonneg (by decide +kernel)))
  calc
    QComplex.normBound
        (QComplex.add (prefixLinearRemainder w h stage)
          (QComplex.sub
            (QComplex.sub (valueCenterError (QComplex.add w h) stage)
              (valueCenterError w stage))
            (QComplex.mul (derivativeCenterError w stage) h))) <=
      QComplex.normBound (prefixLinearRemainder w h stage) +
        QComplex.normBound
          (QComplex.sub
            (QComplex.sub (valueCenterError (QComplex.add w h) stage)
              (valueCenterError w stage))
            (QComplex.mul (derivativeCenterError w stage) h)) :=
        QComplex.normBound_add_le _ _
    _ <= QComplex.normBound (prefixLinearRemainder w h stage) +
        (QComplex.normBound
            (QComplex.sub (valueCenterError (QComplex.add w h) stage)
              (valueCenterError w stage)) +
          QComplex.normBound
            (QComplex.mul (derivativeCenterError w stage) h)) :=
      Rat.add_le_add_left.mpr (QComplex.normBound_sub_le _ _)
    _ <= QComplex.normBound (prefixLinearRemainder w h stage) +
        ((QComplex.normBound (valueCenterError (QComplex.add w h) stage) +
            QComplex.normBound (valueCenterError w stage)) +
          QComplex.normBound
            (QComplex.mul (derivativeCenterError w stage) h)) :=
      Rat.add_le_add_left.mpr
        (Rat.add_le_add_right.mpr (QComplex.normBound_sub_le _ _))
    _ <= 2 * H * H +
        (((4 * half ^ stage) + (4 * half ^ stage)) +
          ((8 * half ^ stage) * H)) :=
      rat_add_le_add hprefix
        (rat_add_le_add (rat_add_le_add hplus hbase) hmul)
    _ = 2 * H * H + 8 * (1 + H) * half ^ stage := by
      grind [Rat.mul_add, Rat.add_mul, Rat.mul_assoc, Rat.mul_comm]

/-- Executable synchronized stage for the completed secant transfer. -/
def secantStage (H : Rat) (eps : QPos) : Nat :=
  RationalMajorant.halfDecayShift (8 * (1 + H)) eps

theorem secantStage_tail_le {H : Rat} (hH : 0 <= H) (eps : QPos) :
    8 * (1 + H) * half ^ secantStage H eps <= eps.val := by
  exact RationalMajorant.halfDecayShift_spec
    (by grind : 0 <= 8 * (1 + H)) eps

/-- Scheduled analytic secant certificate for the completed local logarithm
evaluator.  All quantities are finite rational-complex box centers, and the
right side tends quadratically in the increment up to the requested rational
runtime tolerance. -/
theorem scheduled_centerLinearRemainder_normBound_le
    {w h : QComplex} {H : Rat}
    (hw : QComplex.normBound w <= half)
    (hwh : QComplex.normBound (QComplex.add w h) <= half)
    (hH : 0 <= H) (hh : QComplex.normBound h <= H)
    (eps : QPos) :
    QComplex.normBound (centerLinearRemainder w h (secantStage H eps)) <=
      2 * H * H + eps.val := by
  exact Rat.le_trans
    (centerLinearRemainder_normBound_le hw hwh hH hh (secantStage H eps))
    (Rat.add_le_add_left.mpr (secantStage_tail_le hH eps))

end ComplexLogarithmCompletedSecant
end ComputableAnalysis
