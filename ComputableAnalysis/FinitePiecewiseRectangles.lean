import ComputableAnalysis.Basic

/-!
# Equal-mesh rectangles for finitely piecewise-monotone functions

This is the finite local core of the project's computable integral strategy.
Each equal-mesh cell is classified as increasing, decreasing, or containing a
finitely bracketed turn.  The rectangle endpoints are then selected from the
two endpoint values, with the turn bracket added only in the third case.

No function-limit theorem, completed real, or Lebesgue object is used here.
-/

namespace ComputableAnalysis

inductive PieceCellKind
  | increasing
  | decreasing
  | turning
deriving Repr, DecidableEq

def pieceCellBounds (kind : PieceCellKind)
    (leftValue rightValue turnLower turnUpper : Rat) : QInterval :=
  match kind with
  | .increasing => { lo := leftValue, hi := rightValue }
  | .decreasing => { lo := rightValue, hi := leftValue }
  | .turning =>
      { lo := min leftValue (min rightValue turnLower)
        hi := max leftValue (max rightValue turnUpper) }

theorem pieceCellBounds_increasing_ordered
    {leftValue rightValue turnLower turnUpper : Rat}
    (h : leftValue ≤ rightValue) :
    (pieceCellBounds .increasing leftValue rightValue turnLower turnUpper).lo ≤
      (pieceCellBounds .increasing leftValue rightValue turnLower turnUpper).hi := by
  exact h

theorem pieceCellBounds_decreasing_ordered
    {leftValue rightValue turnLower turnUpper : Rat}
    (h : rightValue ≤ leftValue) :
    (pieceCellBounds .decreasing leftValue rightValue turnLower turnUpper).lo ≤
      (pieceCellBounds .decreasing leftValue rightValue turnLower turnUpper).hi := by
  exact h

theorem pieceCellBounds_turning_ordered
    {leftValue rightValue turnLower turnUpper : Rat}
    (h : turnLower ≤ turnUpper) :
    (pieceCellBounds .turning leftValue rightValue turnLower turnUpper).lo ≤
      (pieceCellBounds .turning leftValue rightValue turnLower turnUpper).hi := by
  unfold pieceCellBounds
  have hmin :
      min leftValue (min rightValue turnLower) ≤ turnLower := by
    rw [Rat.min_def, Rat.min_def]
    split <;> split <;> grind
  have hmax :
      turnUpper ≤ max leftValue (max rightValue turnUpper) := by
    rw [Rat.max_def, Rat.max_def]
    split <;> split <;> grind
  exact Rat.le_trans hmin (Rat.le_trans h hmax)

theorem pieceCellBounds_increasing_contains_endpoints
    {leftValue rightValue turnLower turnUpper : Rat}
    (_h : leftValue ≤ rightValue) :
    (pieceCellBounds .increasing leftValue rightValue turnLower turnUpper).lo =
        leftValue /\
      (pieceCellBounds .increasing leftValue rightValue turnLower turnUpper).hi =
        rightValue := by
  exact ⟨rfl, rfl⟩

theorem pieceCellBounds_decreasing_contains_endpoints
    {leftValue rightValue turnLower turnUpper : Rat}
    (_h : rightValue ≤ leftValue) :
    (pieceCellBounds .decreasing leftValue rightValue turnLower turnUpper).lo =
        rightValue /\
      (pieceCellBounds .decreasing leftValue rightValue turnLower turnUpper).hi =
        leftValue := by
  exact ⟨rfl, rfl⟩

theorem pieceCellBounds_turning_contains_range
    {leftValue rightValue turnLower turnUpper : Rat}
    (_h : turnLower ≤ turnUpper) :
    (pieceCellBounds .turning leftValue rightValue turnLower turnUpper).lo ≤
        leftValue /\
      (pieceCellBounds .turning leftValue rightValue turnLower turnUpper).lo ≤
        rightValue /\
      (pieceCellBounds .turning leftValue rightValue turnLower turnUpper).lo ≤
        turnLower /\
      (pieceCellBounds .turning leftValue rightValue turnLower turnUpper).hi ≥
        leftValue /\
      (pieceCellBounds .turning leftValue rightValue turnLower turnUpper).hi ≥
        rightValue /\
      (pieceCellBounds .turning leftValue rightValue turnLower turnUpper).hi ≥
        turnUpper := by
  unfold pieceCellBounds
  grind

theorem pieceCellBounds_turning_width_le
    {leftValue rightValue turnLower turnUpper rangeLower rangeUpper : Rat}
    (hleftLo : rangeLower ≤ leftValue)
    (hleftHi : leftValue ≤ rangeUpper)
    (hrightLo : rangeLower ≤ rightValue)
    (hrightHi : rightValue ≤ rangeUpper)
    (hturnLo : rangeLower ≤ turnLower)
    (_hturnHi : turnLower ≤ rangeUpper)
    (_hturnUpperLo : rangeLower ≤ turnUpper)
    (hturnUpperHi : turnUpper ≤ rangeUpper) :
    (pieceCellBounds .turning leftValue rightValue turnLower turnUpper).width ≤
      rangeUpper - rangeLower := by
  have hlo :
      rangeLower ≤ min leftValue (min rightValue turnLower) := by
    rw [Rat.min_def, Rat.min_def]
    split <;> split <;> grind
  have hhi :
      max leftValue (max rightValue turnUpper) ≤ rangeUpper := by
    rw [Rat.max_def, Rat.max_def]
    split <;> split <;> grind
  unfold pieceCellBounds QInterval.width
  grind [Rat.sub_eq_add_neg]

def pieceCellWidth (kind : PieceCellKind)
    (leftValue rightValue turnLower turnUpper : Rat) : Rat :=
  (pieceCellBounds kind leftValue rightValue turnLower turnUpper).width

theorem pieceCellWidth_increasing_eq
    {leftValue rightValue turnLower turnUpper : Rat} :
    pieceCellWidth .increasing leftValue rightValue turnLower turnUpper =
      rightValue - leftValue := by
  rfl

theorem pieceCellWidth_decreasing_eq
    {leftValue rightValue turnLower turnUpper : Rat} :
    pieceCellWidth .decreasing leftValue rightValue turnLower turnUpper =
      leftValue - rightValue := by
  rfl

theorem pieceCellWidth_turning_eq
    {leftValue rightValue turnLower turnUpper : Rat} :
    pieceCellWidth .turning leftValue rightValue turnLower turnUpper =
      max leftValue (max rightValue turnUpper) -
        min leftValue (min rightValue turnLower) := by
  rfl

def pieceCellLowerArea (domainWidth : Rat) (kind : PieceCellKind)
    (leftValue rightValue turnLower turnUpper : Rat) : Rat :=
  domainWidth *
    (pieceCellBounds kind leftValue rightValue turnLower turnUpper).lo

def pieceCellUpperArea (domainWidth : Rat) (kind : PieceCellKind)
    (leftValue rightValue turnLower turnUpper : Rat) : Rat :=
  domainWidth *
    (pieceCellBounds kind leftValue rightValue turnLower turnUpper).hi

theorem pieceCellLowerArea_le_upper
    {domainWidth leftValue rightValue turnLower turnUpper : Rat}
    {kind : PieceCellKind}
    (hdomain : 0 ≤ domainWidth)
    (hordered :
      (pieceCellBounds kind leftValue rightValue turnLower turnUpper).lo ≤
        (pieceCellBounds kind leftValue rightValue turnLower turnUpper).hi) :
    pieceCellLowerArea domainWidth kind leftValue rightValue turnLower turnUpper ≤
      pieceCellUpperArea domainWidth kind leftValue rightValue turnLower turnUpper := by
  unfold pieceCellLowerArea pieceCellUpperArea
  exact Rat.mul_le_mul_of_nonneg_left hordered hdomain

theorem pieceCellTurningAreaGap_le
    {domainWidth leftValue rightValue turnLower turnUpper rangeLower rangeUpper : Rat}
    (hdomain : 0 ≤ domainWidth)
    (hleftLo : rangeLower ≤ leftValue)
    (hleftHi : leftValue ≤ rangeUpper)
    (hrightLo : rangeLower ≤ rightValue)
    (hrightHi : rightValue ≤ rangeUpper)
    (hturnLo : rangeLower ≤ turnLower)
    (hturnHi : turnLower ≤ rangeUpper)
    (hturnUpperLo : rangeLower ≤ turnUpper)
    (hturnUpperHi : turnUpper ≤ rangeUpper) :
    pieceCellUpperArea domainWidth .turning leftValue rightValue turnLower turnUpper -
        pieceCellLowerArea domainWidth .turning leftValue rightValue turnLower turnUpper ≤
      domainWidth * (rangeUpper - rangeLower) := by
  unfold pieceCellUpperArea pieceCellLowerArea
  have hwidth := pieceCellBounds_turning_width_le
    hleftLo hleftHi hrightLo hrightHi hturnLo hturnHi hturnUpperLo hturnUpperHi
  have hmul := Rat.mul_le_mul_of_nonneg_left hwidth hdomain
  calc
    domainWidth *
          (pieceCellBounds .turning leftValue rightValue turnLower turnUpper).hi -
        domainWidth *
          (pieceCellBounds .turning leftValue rightValue turnLower turnUpper).lo =
      domainWidth *
        ((pieceCellBounds .turning leftValue rightValue turnLower turnUpper).hi -
          (pieceCellBounds .turning leftValue rightValue turnLower turnUpper).lo) := by
            grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul]
    _ ≤ domainWidth * (rangeUpper - rangeLower) := hmul

def piecewiseRectangleAreaSum : List Rat → Rat
  | [] => 0
  | area :: areas => area + piecewiseRectangleAreaSum areas

theorem piecewiseRectangleAreaSum_append (left right : List Rat) :
    piecewiseRectangleAreaSum (left ++ right) =
      piecewiseRectangleAreaSum left + piecewiseRectangleAreaSum right := by
  induction left with
  | nil =>
      grind [piecewiseRectangleAreaSum]
  | cons area left ih =>
      simp [piecewiseRectangleAreaSum, ih, Rat.add_assoc]

def piecewiseRectangleWidth : List Rat → Rat
  | [] => 0
  | width :: widths => width + piecewiseRectangleWidth widths

theorem piecewiseRectangleWidth_append (left right : List Rat) :
    piecewiseRectangleWidth (left ++ right) =
      piecewiseRectangleWidth left + piecewiseRectangleWidth right := by
  induction left with
  | nil =>
      grind [piecewiseRectangleWidth]
  | cons width left ih =>
      simp [piecewiseRectangleWidth, ih, Rat.add_assoc]

/-!
The next two lemmas lift the cellwise rectangle estimate to a whole finite
mesh.  They are the finite algebraic bridge needed by a constructive FTC:
the global upper-minus-lower gap is exactly the sum of the cell widths times
their value-range widths, and is nonnegative whenever every cell is ordered.
-/

theorem piecewiseRectangleAreaSum_gap_eq_width_sum
    (domainWidth : Rat) (cells : List QInterval) :
    piecewiseRectangleAreaSum
        (cells.map (fun I => domainWidth * I.hi)) -
        piecewiseRectangleAreaSum
          (cells.map (fun I => domainWidth * I.lo)) =
      piecewiseRectangleAreaSum
        (cells.map (fun I => domainWidth * I.width)) := by
  simp only [QInterval.width]
  induction cells with
  | nil =>
      simp [piecewiseRectangleAreaSum, Rat.sub_eq_add_neg]
      grind
  | cons cell cells ih =>
      simp only [List.map_cons, piecewiseRectangleAreaSum]
      calc
        domainWidth * cell.hi +
              piecewiseRectangleAreaSum (cells.map (fun I => domainWidth * I.hi)) -
            (domainWidth * cell.lo +
              piecewiseRectangleAreaSum (cells.map (fun I => domainWidth * I.lo))) =
            domainWidth * (cell.hi - cell.lo) +
              (piecewiseRectangleAreaSum (cells.map (fun I => domainWidth * I.hi)) -
                piecewiseRectangleAreaSum (cells.map (fun I => domainWidth * I.lo))) := by
                  grind [Rat.mul_add, Rat.add_mul, Rat.sub_eq_add_neg]
        _ = domainWidth * (cell.hi - cell.lo) +
              piecewiseRectangleAreaSum (cells.map (fun I => domainWidth * (I.hi - I.lo))) := by
                rw [ih]

theorem piecewiseRectangleAreaSum_gap_nonneg
    (domainWidth : Rat) (cells : List QInterval)
    (hdomain : 0 ≤ domainWidth)
    (hordered : ∀ I, I ∈ cells → I.lo ≤ I.hi) :
    0 ≤ piecewiseRectangleAreaSum
        (cells.map (fun I => domainWidth * I.hi)) -
      piecewiseRectangleAreaSum
        (cells.map (fun I => domainWidth * I.lo)) := by
  rw [piecewiseRectangleAreaSum_gap_eq_width_sum]
  induction cells with
  | nil =>
      simp [piecewiseRectangleAreaSum]
  | cons cell cells ih =>
      simp only [List.map_cons, piecewiseRectangleAreaSum]
      have hcell : 0 ≤ domainWidth * cell.width := by
        unfold QInterval.width
        have hwidth : 0 ≤ cell.hi - cell.lo := by
          grind [hordered cell (by simp)]
        exact Rat.mul_nonneg hdomain hwidth
      have htail : 0 ≤ piecewiseRectangleAreaSum
          (cells.map (fun I => domainWidth * I.width)) := by
        apply ih
        intro I hI
        exact hordered I (by simp [hI])
      exact Rat.add_nonneg hcell htail

theorem piecewiseRectangleAreaSum_gap_le_common_range_budget
    (domainWidth rangeWidth : Rat) (cells : List QInterval)
    (hdomain : 0 ≤ domainWidth)
    (hwidth : ∀ I, I ∈ cells → I.width ≤ rangeWidth) :
    piecewiseRectangleAreaSum
        (cells.map (fun I => domainWidth * I.hi)) -
      piecewiseRectangleAreaSum
        (cells.map (fun I => domainWidth * I.lo)) ≤
      piecewiseRectangleAreaSum
        (cells.map (fun _ => domainWidth * rangeWidth)) := by
  rw [piecewiseRectangleAreaSum_gap_eq_width_sum]
  induction cells with
  | nil =>
      simp [piecewiseRectangleAreaSum]
  | cons cell cells ih =>
      simp only [List.map_cons, piecewiseRectangleAreaSum]
      have hcell : domainWidth * cell.width ≤ domainWidth * rangeWidth :=
        Rat.mul_le_mul_of_nonneg_left (hwidth cell (by simp)) hdomain
      have htail : piecewiseRectangleAreaSum
          (cells.map (fun I => domainWidth * I.width)) ≤
          piecewiseRectangleAreaSum
            (cells.map (fun _ => domainWidth * rangeWidth)) := by
        apply ih
        intro I hI
        exact hwidth I (by simp [hI])
      exact rat_add_le_add hcell htail

theorem piecewiseRectangleAreaSum_constant (cells : List QInterval) (value : Rat) :
    piecewiseRectangleAreaSum (cells.map (fun _ => value)) =
      (cells.length : Rat) * value := by
  induction cells with
  | nil => simp [piecewiseRectangleAreaSum]
  | cons cell cells ih =>
      simp only [List.map_cons, piecewiseRectangleAreaSum, List.length_cons]
      rw [ih]
      rw [Rat.natCast_add]
      have hone : ((1 : Nat) : Rat) = 1 := by native_decide
      rw [hone]
      grind [Rat.add_assoc, Rat.mul_add, Rat.add_mul]

theorem piecewiseRectangleAreaSum_gap_le_common_range
    (domainWidth rangeWidth : Rat) (cells : List QInterval)
    (hdomain : 0 ≤ domainWidth)
    (hwidth : ∀ I, I ∈ cells → I.width ≤ rangeWidth) :
    piecewiseRectangleAreaSum
        (cells.map (fun I => domainWidth * I.hi)) -
      piecewiseRectangleAreaSum
        (cells.map (fun I => domainWidth * I.lo)) ≤
      (cells.length : Rat) * (domainWidth * rangeWidth) := by
  calc
    piecewiseRectangleAreaSum
          (cells.map (fun I => domainWidth * I.hi)) -
        piecewiseRectangleAreaSum
          (cells.map (fun I => domainWidth * I.lo)) ≤
        piecewiseRectangleAreaSum
          (cells.map (fun _ => domainWidth * rangeWidth)) :=
      piecewiseRectangleAreaSum_gap_le_common_range_budget
        domainWidth rangeWidth cells hdomain hwidth
    _ = (cells.length : Rat) * (domainWidth * rangeWidth) :=
      piecewiseRectangleAreaSum_constant cells (domainWidth * rangeWidth)

/-! A reusable finite certificate for the piecewise-monotone rectangle stage.
The certificate carries only rational data and the cell-order proof; later
FTC constructions may add a function representation and a refinement rule. -/

structure PiecewiseRectangleCertificate where
  domainWidth : Rat
  cells : List QInterval
  domain_nonneg : 0 ≤ domainWidth
  cells_ordered : ∀ I, I ∈ cells → I.lo ≤ I.hi

def PiecewiseRectangleCertificate.lowerSum
    (certificate : PiecewiseRectangleCertificate) : Rat :=
  piecewiseRectangleAreaSum
    (certificate.cells.map (fun I => certificate.domainWidth * I.lo))

def PiecewiseRectangleCertificate.upperSum
    (certificate : PiecewiseRectangleCertificate) : Rat :=
  piecewiseRectangleAreaSum
    (certificate.cells.map (fun I => certificate.domainWidth * I.hi))

theorem PiecewiseRectangleCertificate.gap_eq_width_sum
    (certificate : PiecewiseRectangleCertificate) :
    certificate.upperSum - certificate.lowerSum =
      piecewiseRectangleAreaSum
        (certificate.cells.map
          (fun I => certificate.domainWidth * I.width)) := by
  unfold PiecewiseRectangleCertificate.upperSum
    PiecewiseRectangleCertificate.lowerSum
  exact piecewiseRectangleAreaSum_gap_eq_width_sum
    certificate.domainWidth certificate.cells

theorem PiecewiseRectangleCertificate.gap_nonneg
    (certificate : PiecewiseRectangleCertificate) :
    0 ≤ certificate.upperSum - certificate.lowerSum := by
  unfold PiecewiseRectangleCertificate.upperSum
    PiecewiseRectangleCertificate.lowerSum
  exact piecewiseRectangleAreaSum_gap_nonneg certificate.domainWidth
    certificate.cells certificate.domain_nonneg certificate.cells_ordered

theorem PiecewiseRectangleCertificate.lower_le_upper
    (certificate : PiecewiseRectangleCertificate) :
    certificate.lowerSum ≤ certificate.upperSum := by
  have hgap := certificate.gap_nonneg
  grind [Rat.sub_eq_add_neg]

def quadraticTurnExample : List QInterval :=
  [ pieceCellBounds .increasing 0 1 0 0
  , pieceCellBounds .decreasing 1 0 0 0 ]

theorem quadraticTurnExample_cells_ordered :
    (quadraticTurnExample.all fun I => I.lo ≤ I.hi) := by
  native_decide

theorem quadraticTurnExample_widths :
    piecewiseRectangleWidth
        (quadraticTurnExample.map QInterval.width) = 2 := by
  native_decide

def quadraticTurnLowerAreas : List Rat := [0, 0]

def quadraticTurnUpperAreas : List Rat := [1, 1]

theorem quadraticTurnExample_area_enclosure :
    piecewiseRectangleAreaSum quadraticTurnLowerAreas = 0 /\
      piecewiseRectangleAreaSum quadraticTurnUpperAreas = 2 := by
  native_decide

def quadraticTurnContainingCell : QInterval :=
  pieceCellBounds .turning 0 0 1 1

theorem quadraticTurnContainingCell_certificate :
    quadraticTurnContainingCell.lo = 0 /\
      quadraticTurnContainingCell.hi = 1 /\
      quadraticTurnContainingCell.width = 1 := by
  native_decide

end ComputableAnalysis
