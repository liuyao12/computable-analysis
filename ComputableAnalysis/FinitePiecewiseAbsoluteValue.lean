import ComputableAnalysis.Calculus

/-!
# A finite-turn integral: the absolute value

This is the smallest concrete client of the finite-piece integral interface.
The function is decreasing on `[-1,0]` and increasing on `[0,1]`; the two
pieces are integrated separately and then assembled by a finite raw sum.
-/

namespace ComputableAnalysis

namespace Integral

def absoluteValueOnUnit : FunctionOnInterval :=
  FunctionOnInterval.exactRat qabs (-1) 1

def absoluteValueLeft : FunctionOnInterval :=
  absoluteValueOnUnit.restrict (-1) 0 (by native_decide) (by native_decide)
    (by native_decide)

def absoluteValueRight : FunctionOnInterval :=
  absoluteValueOnUnit.restrict 0 1 (by native_decide) (by native_decide)
    (by native_decide)

theorem absoluteValueLeft_nonincreasing :
    NonincreasingOnInterval absoluteValueLeft := by
  intro x y hx hy hxy n
  change qabs y <= qabs x
  rw [qabs_eq_neg_of_nonpos hx.2, qabs_eq_neg_of_nonpos hy.2]
  grind

theorem absoluteValueRight_nondecreasing :
    NondecreasingOnInterval absoluteValueRight := by
  intro x y hx hy hxy n
  change qabs x <= qabs y
  rw [qabs_eq_self_of_nonneg hx.1, qabs_eq_self_of_nonneg hy.1]
  exact hxy

def absoluteValueLeftConstruction :
    MonotoneConstructionFor absoluteValueLeft where
  monotone := MonotoneOnInterval.ofNonincreasing
    absoluteValueLeft_nonincreasing
  construction :=
    { compute := (RealRaw.ofRat (1 / 2)).compute
      certificate := RealRaw.ofRat_valid (1 / 2) }

def absoluteValueRightConstruction :
    MonotoneConstructionFor absoluteValueRight where
  monotone := MonotoneOnInterval.ofNondecreasing
    absoluteValueRight_nondecreasing
  construction :=
    { compute := (RealRaw.ofRat (1 / 2)).compute
      certificate := RealRaw.ofRat_valid (1 / 2) }

def absoluteValuePiecewise :
    PiecewiseMonotoneConstructionFor absoluteValueOnUnit where
  pieces := 2
  positive := by native_decide
  point
    | 0 => -1
    | 1 => 0
    | _ + 2 => 1
  left_endpoint := by native_decide
  right_endpoint := by native_decide
  point_mem := by
    intro i hi
    have hi_cases : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases hi_cases with rfl | rfl | rfl
    · exact ⟨by native_decide, by native_decide⟩
    · exact ⟨by native_decide, by native_decide⟩
    · exact ⟨by native_decide, by native_decide⟩
  point_mono := by
    intro i j hij hj
    have hi_cases : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    have hj_cases : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases hi_cases with rfl | rfl | rfl <;>
      rcases hj_cases with rfl | rfl | rfl <;>
        simp at hij ⊢ <;> native_decide
  construction := fun k hk => by
    cases k with
    | zero =>
        simpa [absoluteValueLeft, absoluteValueOnUnit] using
          absoluteValueLeftConstruction
    | succ k =>
        cases k with
        | zero =>
            simpa [absoluteValueRight, absoluteValueOnUnit] using
              absoluteValueRightConstruction
        | succ k =>
            omega

theorem absoluteValuePiecewise_integral_equiv_one :
    (piecewiseMonotoneIntegralFor absoluteValueOnUnit
      absoluteValuePiecewise).Equiv (RealRaw.ofRat 1) := by
  have hleft :
      piecewiseMonotoneCellIntegral absoluteValueOnUnit
        absoluteValuePiecewise 0 (by native_decide) =
        RealRaw.ofRat (1 / 2) := by
    rfl
  have hright :
      piecewiseMonotoneCellIntegral absoluteValueOnUnit
        absoluteValuePiecewise 1 (by native_decide) =
        RealRaw.ofRat (1 / 2) := by
    rfl
  have hsum :
      (piecewiseMonotoneCellIntegral absoluteValueOnUnit
        absoluteValuePiecewise 0 (by native_decide) +
       piecewiseMonotoneCellIntegral absoluteValueOnUnit
        absoluteValuePiecewise 1 (by native_decide)).Equiv
        (RealRaw.ofRat 1) := by
    rw [hleft, hright]
    apply RealRaw.sameStageOverlap_equiv
    intro n
    apply (RealRaw.compareAt_overlap_iff _ _ n n).2
    simp [RealRaw.add, RealRaw.addCompute, RealRaw.ofRat]
    change QInterval.Overlaps
      (QInterval.addInterval { lo := 1 / 2, hi := 1 / 2 }
        { lo := 1 / 2, hi := 1 / 2 })
      { lo := 1, hi := 1 }
    simp [QInterval.addInterval, QInterval.Overlaps]
    exact ⟨by native_decide, by native_decide⟩
  have hpiece := piecewiseMonotoneIntegralFor_two_equiv
    absoluteValueOnUnit absoluteValuePiecewise (by native_decide)
  exact RealRaw.equiv_trans
    (piecewiseMonotoneIntegralFor_valid absoluteValueOnUnit
      absoluteValuePiecewise)
    (RealRaw.add_valid
      (piecewiseMonotoneCellIntegral_valid absoluteValueOnUnit
        absoluteValuePiecewise 0 (by native_decide))
      (piecewiseMonotoneCellIntegral_valid absoluteValueOnUnit
        absoluteValuePiecewise 1 (by native_decide)))
    (RealRaw.ofRat_valid 1)
    hpiece (by simpa using hsum)

end Integral

end ComputableAnalysis
