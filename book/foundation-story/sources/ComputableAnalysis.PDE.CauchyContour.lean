import ComputableAnalysis.CauchyPi
import ComputableAnalysis.HolomorphicJet

/-!
# The Cauchy pole on a rational square contour

The square is split into eight oriented affine half-edges. Their literal
`(1/z) dz` pullbacks combine to `8 i / (1+u²)` on `[0,1]`.
Finite rational rectangle sums then normalize the contour against geometric
pi. This is an independent pole normalization, not a definition of Dirac as
the result of applying a PDE operator to a candidate kernel.
-/

namespace ComputableAnalysis.PDE.CauchyContour

open QComplex ArctanGeometry

inductive Quarter where
  | east | north | west | south
deriving DecidableEq, Repr

def rotation : Quarter → QComplex
  | .east => ⟨1, 0⟩
  | .north => ⟨0, 1⟩
  | .west => ⟨-1, 0⟩
  | .south => ⟨0, -1⟩

structure HalfEdge where
  quarter : Quarter
  upper : Bool
deriving Repr

def orientation (edge : HalfEdge) : Rat := if edge.upper then 1 else -1

def point (edge : HalfEdge) (u : Rat) : QComplex :=
  mul (rotation edge.quarter) ⟨1, orientation edge * u⟩

def velocity (edge : HalfEdge) : QComplex :=
  mul (rotation edge.quarter) ⟨0, orientation edge⟩

def startPoint (edge : HalfEdge) : QComplex := point edge (if edge.upper then 0 else 1)
def stopPoint (edge : HalfEdge) : QComplex := point edge (if edge.upper then 1 else 0)

/-- Listed in counterclockwise order; negative orientations reverse the
lower half of each rotated right-hand side. -/
def square : List HalfEdge :=
  [⟨.east, true⟩, ⟨.north, false⟩, ⟨.north, true⟩, ⟨.west, false⟩,
   ⟨.west, true⟩, ⟨.south, false⟩, ⟨.south, true⟩, ⟨.east, false⟩]

theorem point_affine_increment (edge : HalfEdge) (u h : Rat) :
    sub (point edge (u + h)) (point edge u) = scaleRat h (velocity edge) := by
  cases edge with
  | mk q b =>
    cases q <;> cases b <;>
      simp only [point, velocity, orientation, rotation, mul, sub, add, neg,
        scaleRat, Bool.false_eq_true, ↓reduceIte, QComplex.mk.injEq] <;>
      constructor <;> grind

theorem point_normSq (edge : HalfEdge) (u : Rat) : normSq (point edge u) = 1 + u * u := by
  cases edge with
  | mk q b =>
    cases q <;> cases b <;>
      simp only [point, orientation, rotation, mul, normSq,
        Bool.false_eq_true, ↓reduceIte] <;> grind

theorem point_avoids_pole (edge : HalfEdge) (u : Rat) : normSq (point edge u) ≠ 0 := by
  rw [point_normSq]
  have h := rat_square_nonneg_basic u
  grind

private theorem inverse_scale (r : Rat) (hr : r ≠ 0) (z : QComplex) :
    inverse (scaleRat r z) = scaleRat r⁻¹ (inverse z) := by
  unfold inverse
  rw [normSq_scaleRat]
  simp only [scaleRat, Rat.div_def, Rat.inv_mul_rev, QComplex.mk.injEq]
  have hi := Rat.mul_inv_cancel r hr
  constructor <;> grind

def pullback (edge : HalfEdge) (u : Rat) : QComplex :=
  scaleRat (orientation edge) (mul (inverse (point edge u)) (velocity edge))

/-- Pull back `1/(z-center)` on the translated, dilated square. -/
def scaledPullback (center : QComplex) (r : Rat) (edge : HalfEdge) (u : Rat) : QComplex :=
  scaleRat (orientation edge)
    (mul (inverse (sub (add center (scaleRat r (point edge u))) center))
      (scaleRat r (velocity edge)))

/-- Exact invariance on arbitrarily small rational squares, without an
appeal to a general contour deformation or residue theorem. -/
theorem scaledPullback_eq (center : QComplex) (r : Rat) (hr : r ≠ 0)
    (edge : HalfEdge) (u : Rat) : scaledPullback center r edge u = pullback edge u := by
  have hsub : sub (add center (scaleRat r (point edge u))) center = scaleRat r (point edge u) := by
    cases center; cases point edge u
    simp only [sub, add, neg, scaleRat, QComplex.mk.injEq]
    constructor <;> grind
  unfold scaledPullback
  rw [hsub, inverse_scale r hr]
  unfold pullback
  congr 1
  cases inverse (point edge u); cases velocity edge
  simp only [scaleRat, mul, QComplex.mk.injEq]
  have hi := Rat.mul_inv_cancel r hr
  constructor <;> grind

theorem pullback_exact (edge : HalfEdge) (u : Rat) :
    pullback edge u = ⟨orientation edge * u / (1 + u * u), 1 / (1 + u * u)⟩ := by
  unfold pullback inverse
  rw [point_normSq]
  cases edge with
  | mk q b =>
    cases q <;> cases b <;>
      simp only [point, velocity, orientation, rotation, mul, scaleRat,
        Bool.false_eq_true, ↓reduceIte, QComplex.mk.injEq] <;>
      constructor <;> grind [Rat.div_def]

def density (u : Rat) : QComplex :=
  (square.map fun edge => pullback edge u).foldr add zero

/-- Exact cancellation occurs before any limiting or integration operation. -/
theorem density_exact (u : Rat) : density u = ⟨0, 8 * integralKernel u⟩ := by
  simp only [density, square, List.map_cons, List.map_nil, List.foldr_cons,
    List.foldr_nil, pullback_exact, orientation, Bool.false_eq_true, ↓reduceIte,
    add, zero, integralKernel, QComplex.mk.injEq]
  constructor <;> grind [Rat.div_def]

theorem square_endpoints :
    square.map (fun e => (startPoint e, stopPoint e)) =
    [(⟨1, 0⟩, ⟨1, 1⟩), (⟨1, 1⟩, ⟨0, 1⟩),
     (⟨0, 1⟩, ⟨-1, 1⟩), (⟨-1, 1⟩, ⟨-1, 0⟩),
     (⟨-1, 0⟩, ⟨-1, -1⟩), (⟨-1, -1⟩, ⟨0, -1⟩),
     (⟨0, -1⟩, ⟨1, -1⟩), (⟨1, -1⟩, ⟨1, 0⟩)] := by
  simp only [square, List.map_cons, List.map_nil, startPoint, stopPoint, point,
    orientation, rotation, mul, Bool.false_eq_true, ↓reduceIte,
    List.cons.injEq, Prod.mk.injEq, QComplex.mk.injEq]
  grind (splits := 64)

structure TaggedCell where
  left : Rat
  right : Rat
  tag : Rat

def TaggedCell.Good (cell : TaggedCell) : Prop :=
  0 ≤ cell.left ∧ cell.left ≤ cell.tag ∧ cell.tag ≤ cell.right ∧ cell.right ≤ 1

def GoodCells : List TaggedCell → Prop
  | [] => True
  | c :: cs => c.Good ∧ GoodCells cs

def intervals (cells : List TaggedCell) : List (Rat × Rat) :=
  cells.map fun c => (c.left, c.right)

def taggedSum : List TaggedCell → QComplex
  | [] => zero
  | c :: cs => add (scaleRat (c.right - c.left) (density c.tag)) (taggedSum cs)

def rectangleBox (cells : List (Rat × Rat)) : QBox :=
  ⟨⟨0, 8 * integralLowerSum cells⟩, ⟨0, 8 * integralUpperSum cells⟩⟩

private theorem kernel_antitone {x y : Rat} (hx : 0 ≤ x) (hxy : x ≤ y) :
    integralKernel y ≤ integralKernel x := by
  have hprod := Rat.mul_nonneg (show 0 ≤ y - x by grind) (show 0 ≤ y + x by grind)
  have hs := rat_square_nonneg_basic x
  unfold integralKernel
  simp only [Rat.div_def, Rat.one_mul]
  have ht := rat_square_nonneg_basic y
  have hxpos : 0 < 1 + x * x := by grind
  have hypos : 0 < 1 + y * y := by grind
  have hix := Rat.le_of_lt ((Rat.inv_pos).2 hxpos)
  have hiy := Rat.le_of_lt ((Rat.inv_pos).2 hypos)
  have horder : 1 + x * x ≤ 1 + y * y := by grind
  have hmul := Rat.mul_le_mul_of_nonneg_right
    (Rat.mul_le_mul_of_nonneg_right horder hix) hiy
  have hcx := Rat.mul_inv_cancel (1 + x * x) (by grind)
  have hcy := Rat.mul_inv_cancel (1 + y * y) (by grind)
  rw [hcx, Rat.one_mul] at hmul
  have he : (1 + y * y) * (1 + x * x)⁻¹ * (1 + y * y)⁻¹ =
      ((1 + y * y) * (1 + y * y)⁻¹) * (1 + x * x)⁻¹ := by grind
  rw [he, hcy, Rat.one_mul] at hmul
  exact hmul

private theorem taggedCell_bounds (c : TaggedCell) (hc : c.Good) :
    integralLowerStep c.left c.right ≤ (c.right - c.left) * integralKernel c.tag ∧
    (c.right - c.left) * integralKernel c.tag ≤ integralUpperStep c.left c.right := by
  have htag : 0 ≤ c.tag := by have := hc.1; have := hc.2.1; grind
  have hlen : 0 ≤ c.right - c.left := by have := hc.2.1; have := hc.2.2.1; grind
  exact ⟨Rat.mul_le_mul_of_nonneg_left (kernel_antitone htag hc.2.2.1) hlen,
    Rat.mul_le_mul_of_nonneg_left (kernel_antitone hc.1 hc.2.1) hlen⟩

/-- Enclosure of the literal oriented contour sums for every choice of tags
on a common finite parameter partition. -/
theorem taggedSum_enclosed (cells : List TaggedCell) (hc : GoodCells cells) :
    (rectangleBox (intervals cells)).lo ≤ taggedSum cells ∧
      taggedSum cells ≤ (rectangleBox (intervals cells)).hi := by
  induction cells with
  | nil =>
    simp only [intervals, List.map_nil, taggedSum, rectangleBox,
      integralLowerSum, integralUpperSum, QComplex.le_def, zero]
    grind
  | cons c cs ih =>
    have hcell := taggedCell_bounds c hc.1
    have htail := ih hc.2
    simp only [intervals, List.map_cons, rectangleBox, integralLowerSum,
      integralUpperSum, taggedSum, density_exact, scaleRat, add, QComplex.le_def] at htail ⊢
    grind

def raw : ComplexRaw where
  compute n := rectangleBox (arctanAreaLoopState 1 n).intervals

theorem stage_partition_covers (n : Nat) :
    CoversInterval 0 1 (arctanAreaLoopState 1 n).intervals :=
  arctanAreaLoopState_intervals_covers (by grind) n

theorem raw_encloses_taggedSum (n : Nat) (cells : List TaggedCell) (hc : GoodCells cells)
    (hp : intervals cells = (arctanAreaLoopState 1 n).intervals) :
    (raw.compute n).lo ≤ taggedSum cells ∧ taggedSum cells ≤ (raw.compute n).hi := by
  change (rectangleBox _).lo ≤ _ ∧ _ ≤ (rectangleBox _).hi
  rw [← hp]
  exact taggedSum_enclosed cells hc

def midpointCells (pieces : List (Rat × Rat)) : List TaggedCell :=
  pieces.map fun (p, r) => ⟨p, r, (p + r) / 2⟩

theorem midpointCells_intervals (pieces : List (Rat × Rat)) :
    intervals (midpointCells pieces) = pieces := by
  induction pieces with
  | nil => rfl
  | cons p ps ih => simp only [midpointCells, intervals, List.map_cons] at ih ⊢; rw [ih]

theorem midpointCells_good (pieces : List (Rat × Rat)) (hp : UnitIntervals pieces) :
    GoodCells (midpointCells pieces) := by
  induction pieces with
  | nil => exact True.intro
  | cons p ps ih =>
    have htail := ih hp.2.2.2
    have hleft := hp.1
    have horder := hp.2.1
    have hright := hp.2.2.1
    simp only [midpointCells, List.map_cons, GoodCells, TaggedCell.Good]
    exact ⟨⟨hleft, by grind [Rat.div_def, Rat.mul_inv_cancel],
      by grind [Rat.div_def, Rat.mul_inv_cancel], hright⟩, htail⟩

def stageCells (n : Nat) : List TaggedCell := midpointCells (arctanAreaLoopState 1 n).intervals

/-- A concrete executable sequence of contour sample sums, with no supplied
tag-selection or partition oracle. -/
theorem raw_encloses_stageSum (n : Nat) :
    (raw.compute n).lo ≤ taggedSum (stageCells n) ∧
      taggedSum (stageCells n) ≤ (raw.compute n).hi :=
  raw_encloses_taggedSum n (stageCells n)
    (midpointCells_good _ (arctanAreaLoopState_intervals_unit (by grind) (by grind) n))
    (midpointCells_intervals _)

/-- The contour algorithm is related to the independently certified real
quadrature by literal equality of its rational boxes, not by naming it pi. -/
theorem raw_eq_embedded_rectangle : raw =
    ComplexRaw.imaginaryAxis (RealRaw.scaleRat 2 CauchyPi.rectangleRaw) := by
  apply congrArg (fun f : Nat → QBox => ComplexRaw.mk f .unknown)
  funext n
  change rectangleBox (arctanAreaLoopState 1 n).intervals =
    (ComplexRaw.imaginaryAxis (RealRaw.scaleRat 2 CauchyPi.rectangleRaw)).compute n
  rw [ComplexRaw.imaginaryAxis_compute]
  simp only [RealRaw.scaleRat, RealRaw.scaleRatCompute, CauchyPi.rectangleRaw,
    IntegralIdentities.PiFromArctanIntegral, if_pos (show (0 : Rat) ≤ 2 by grind),
    if_pos (show (0 : Rat) ≤ 4 by grind),
    IntegralIdentities.arctanIntegralRectangleForAtOne_compute_eq,
    arctanIntegralRectangleComputeAtOne, integralSumInterval, rectangleBox,
    QBox.mk.injEq, QComplex.mk.injEq]
  grind

theorem raw_valid : raw.Valid := by
  rw [raw_eq_embedded_rectangle]
  exact ComplexRaw.imaginaryAxis_valid
    (RealRaw.scaleRat_valid_of_nonneg (by grind) CauchyPi.rectangleRaw_valid)

theorem raw_width_zero (n : Nat) : (raw.compute n).width = 0 := by
  simp only [raw, rectangleBox, QBox.width]
  grind

theorem raw_height_le (n : Nat) :
    (raw.compute n).height ≤ (32 : Rat) / (((n + 1 : Nat) : Rat)) := by
  have h := arctanIntegralRectangleComputeAtOne_width_le_four_div_succ n
  have h8 := Rat.mul_le_mul_of_nonneg_left h (show (0 : Rat) ≤ 8 by grind)
  simp only [arctanIntegralRectangleComputeAtOne, integralSumInterval, QInterval.width] at h8
  simp only [raw, rectangleBox, QBox.height]
  grind [Rat.div_def]

/-- The actual partition doubles at every stage. Preserve its sharper
geometric rate when selecting precision for nested computations. -/
theorem raw_height_geometric (n : Nat) :
    (raw.compute n).height ≤ 16 / (((2 ^ n : Nat) : Rat)) := by
  have h := integralSumInterval_width_le_two_squareSum (arctanAreaLoopState 1 n).intervals
    (arctanAreaLoopState_intervals_unit (by grind) (by grind) n)
  rw [arctanAreaLoopState_squareSum 1 n] at h
  have h8 := Rat.mul_le_mul_of_nonneg_left h (show (0 : Rat) ≤ 8 by grind)
  simp only [integralSumInterval, QInterval.width] at h8
  simp only [raw, rectangleBox, QBox.height]
  grind [Rat.div_def]

theorem raw_stage_zero : raw.compute 0 = ⟨⟨0, 4⟩, ⟨0, 8⟩⟩ := by
  simp only [raw, rectangleBox, arctanAreaLoopState, iterateAreaLoopState,
    arctanAreaLoopInitial, integralLowerSum, integralUpperSum, integralLowerStep,
    integralUpperStep, integralKernel, QBox.mk.injEq, QComplex.mk.injEq]
  grind [Rat.div_def, Rat.mul_inv_cancel]

/-- Uniform separation data for subsequently computing the reciprocal
normalization constant. -/
theorem raw_im_bounds (n : Nat) : 4 ≤ (raw.compute n).lo.im ∧ (raw.compute n).hi.im ≤ 8 := by
  have h := raw_valid.2.1 0 n (Nat.zero_le n)
  rw [raw_stage_zero] at h
  exact ⟨h.2.2.1, h.2.2.2⟩

/-- A concrete rational separation from zero, independent of any PDE. -/
theorem raw_not_equiv_zero : ¬ raw.Equiv (ComplexRaw.ofQComplex zero) := by
  intro h
  have ho := (ComplexRaw.compareAt_overlap_iff raw (ComplexRaw.ofQComplex zero) 0 0).1 (h 0)
  rw [raw_stage_zero] at ho
  have hi := ho.1.2
  change (4 : Rat) ≤ 0 at hi
  grind

def twoPiI : ComplexRaw := ComplexRaw.imaginaryAxis (RealRaw.scaleRat 2 piCircleArea)

theorem twoPiI_valid : twoPiI.Valid :=
  ComplexRaw.imaginaryAxis_valid
    (RealRaw.scaleRat_valid_of_nonneg (by grind) CauchyPi.piCircleArea_valid)

/-- Independent Cauchy-pole normalization for this counterclockwise square:
the certified contour computation agrees with `2πi`, where pi is the
repository's geometric circle-area computation. -/
theorem raw_equiv_twoPiI : raw.Equiv twoPiI := by
  rw [raw_eq_embedded_rectangle]
  exact ComplexRaw.imaginaryAxis_equiv
    (RealRaw.scaleRat_valid_of_nonneg (by grind) CauchyPi.rectangleRaw_valid)
    (RealRaw.scaleRat_valid_of_nonneg (by grind) CauchyPi.piCircleArea_valid)
    (RealRaw.scaleRat_equiv_of_nonneg (by grind) CauchyPi.rectangleRaw_equiv_piCircleArea)

theorem twoPiI_not_equiv_zero : ¬ twoPiI.Equiv (ComplexRaw.ofQComplex zero) := by
  intro h
  exact raw_not_equiv_zero (ComplexRaw.equiv_trans raw_valid twoPiI_valid
    (ComplexRaw.ofQComplex_valid zero) raw_equiv_twoPiI h)

end ComputableAnalysis.PDE.CauchyContour
