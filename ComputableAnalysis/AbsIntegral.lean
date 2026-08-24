import ComputableAnalysis.TurningPointIntegral

/-!
# A first completed finite-turn integral

The absolute value on `[-1,1]` is the smallest genuinely non-monotone
example in the project.  Its two monotone pieces are affine, so the public
piecewise integral can be checked all the way to the rational value `1`.
-/

namespace ComputableAnalysis

namespace Integral

def absRat (x : Rat) : Rat :=
  if x < 0 then -x else x

theorem absRat_eq_neg_of_nonpos {x : Rat} (hx : x <= 0) :
    absRat x = -x := by
  by_cases h : x < 0
  · simp [absRat, h]
  · simp [absRat, h]
    grind

theorem absRat_eq_self_of_nonneg {x : Rat} (hx : 0 <= x) :
    absRat x = x := by
  by_cases h : x < 0
  · exfalso
    grind
  · simp [absRat, h]

def absOnUnit : FunctionOnInterval :=
  FunctionOnInterval.exactRat absRat (-1) 1

theorem absRat_lipschitzOnIntervalNat :
    LipschitzOnIntervalNat absRat (-1) 1 1 := by
  refine ⟨by native_decide, ?_⟩
  intro s t hs hsb ht htb
  by_cases hsneg : s < 0 <;> by_cases htneg : t < 0
  all_goals simp [absRat, qabs, hsneg, htneg]
  all_goals grind

def absOnUnit_intervalRegular : IntervalRegularOn absOnUnit :=
  IntervalRegularOn.of_lipschitzOnIntervalNat absRat (-1) 1 1
    absRat_lipschitzOnIntervalNat

def absPartitionPoint : Nat -> Rat
  | 0 => -1
  | 1 => 0
  | _ => 1

theorem absOnUnit_left_nondecreasing :
    NonincreasingOnInterval
      (absOnUnit.restrict (-1) 0 (by native_decide) (by native_decide)
        (by native_decide)) := by
  intro x y hx hy hxy n
  change absRat y <= absRat x
  rw [absRat_eq_neg_of_nonpos hx.2, absRat_eq_neg_of_nonpos hy.2]
  exact Rat.neg_le_neg hxy

theorem absOnUnit_right_nondecreasing :
    NondecreasingOnInterval
      (absOnUnit.restrict 0 1 (by native_decide) (by native_decide)
        (by native_decide)) := by
  intro x y hx hy hxy n
  change absRat x <= absRat y
  rw [absRat_eq_self_of_nonneg hx.1, absRat_eq_self_of_nonneg hy.1]
  exact hxy

def absOnUnit_left : MonotoneConstructionFor
    (absOnUnit.restrict (-1) 0 (by native_decide) (by native_decide)
      (by native_decide)) where
  monotone := MonotoneOnInterval.ofNonincreasing absOnUnit_left_nondecreasing
  construction :=
    { compute := (RealRaw.ofRat (1 / 2)).compute
      certificate := RealRaw.ofRat_valid (1 / 2) }

def absOnUnit_right : MonotoneConstructionFor
    (absOnUnit.restrict 0 1 (by native_decide) (by native_decide)
      (by native_decide)) where
  monotone := MonotoneOnInterval.ofNondecreasing absOnUnit_right_nondecreasing
  construction :=
    { compute := (RealRaw.ofRat (1 / 2)).compute
      certificate := RealRaw.ofRat_valid (1 / 2) }

def absOnUnit_piecewise : PiecewiseMonotoneConstructionFor absOnUnit where
  pieces := 2
  positive := by native_decide
  point := absPartitionPoint
  left_endpoint := by rfl
  right_endpoint := by rfl
  point_mem := by
    intro i hi
    cases i with
    | zero =>
      change (-1 : Rat) <= -1 ∧ (-1 : Rat) <= 1
      native_decide
    | succ i =>
      cases i with
      | zero =>
        change (-1 : Rat) <= 0 ∧ (0 : Rat) <= 1
        native_decide
      | succ i =>
        change (-1 : Rat) <= 1 ∧ (1 : Rat) <= 1
        native_decide
  point_mono := by
    intro i j hij hj
    cases i with
    | zero =>
      cases j with
      | zero => native_decide
      | succ j =>
        cases j with
        | zero => native_decide
        | succ j => simp [absPartitionPoint] <;> native_decide
    | succ i =>
      cases i with
      | zero =>
        cases j with
        | zero => exfalso; omega
        | succ j =>
          cases j with
          | zero => native_decide
          | succ j => simp [absPartitionPoint] <;> native_decide
      | succ i =>
        cases j with
        | zero => exfalso; omega
        | succ j =>
          cases j with
          | zero => exfalso; omega
          | succ j => simp [absPartitionPoint] <;> native_decide
  construction := by
    intro k hk
    cases k with
    | zero => simpa [absPartitionPoint] using absOnUnit_left
    | succ k =>
      cases k with
      | zero => simpa [absPartitionPoint] using absOnUnit_right
      | succ k => exfalso; omega

theorem absOnUnit_piecewise_integral_valid :
    (generalIntegralFor absOnUnit absOnUnit_piecewise).Valid :=
  generalIntegralFor_valid absOnUnit absOnUnit_piecewise

theorem absOnUnit_piecewise_integral_equiv_one :
    (generalIntegralFor absOnUnit absOnUnit_piecewise).Equiv
      (RealRaw.ofRat 1) := by
  apply RealRaw.sameStageOverlap_equiv
  intro n
  have h0 : piecewiseMonotoneCellIntegral absOnUnit absOnUnit_piecewise
      0 (by native_decide) = RealRaw.ofRat (1 / 2) := by
    rfl
  have h1 : piecewiseMonotoneCellIntegral absOnUnit absOnUnit_piecewise
      1 (by native_decide) = RealRaw.ofRat (1 / 2) := by
    rfl
  unfold generalIntegralFor piecewiseMonotoneIntegralFor
  change
    (List.foldl
      (fun acc k =>
        if hk : k < 2 then
          acc + piecewiseMonotoneCellIntegral absOnUnit absOnUnit_piecewise k hk
        else acc)
      (RealRaw.ofRat 0) (List.range 2)).compareAt (RealRaw.ofRat 1) n =
      RealRaw.CompareAt.overlap
  have hrange : List.range 2 = [0, 1] := by native_decide
  rw [hrange]
  simp [h0, h1, RealRaw.compareAt, RealRaw.compareIntervals,
    HAdd.hAdd, RealRaw.add, RealRaw.addCompute,
    RealRaw.ofRat]
  native_decide

end Integral

end ComputableAnalysis
