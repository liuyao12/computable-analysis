import ComputableAnalysis.Elementary
import ComputableAnalysis.Pi

/-!
# Rational circle stages

`Pi.lean` keeps the four public algorithms compact and readable.  This file
names the internal pieces of the rational circle algorithms so proofs can talk
about one finite stage: the rational points, the inscribed polygon, the tangent
polygon, the area bounds, and the circumference bounds.

The bridge theorems at the end say that these structured stages are exactly the
computations used by `piCircleArea` and `piCircumference`.
-/

namespace ComputableAnalysis

namespace RationalCircle

def dyadicSubdivisions (n : Nat) : Nat :=
  2 ^ n

theorem dyadicSubdivisions_pos (n : Nat) : 0 < dyadicSubdivisions n := by
  unfold dyadicSubdivisions
  exact Nat.pow_pos (by omega : 0 < 2)

theorem dyadicSubdivisions_succ (n : Nat) :
    dyadicSubdivisions (n + 1) = 2 * dyadicSubdivisions n := by
  unfold dyadicSubdivisions
  simpa [Nat.mul_comm] using (Nat.pow_succ 2 n)

/-- One finite rational approximation stage for the quarter circle. -/
structure Stage where
  subdivisions : Nat

namespace Stage

def RefinesByDoubling (coarse fine : Stage) : Prop :=
  fine.subdivisions = 2 * coarse.subdivisions

def refineIndex (k : Nat) : Nat :=
  2 * k

def insertedIndex (k : Nat) : Nat :=
  2 * k + 1

def parameter (S : Stage) (k : Nat) : Rat :=
  (k : Rat) / (S.subdivisions : Rat)

def point (u : Rat) : PiCirclePoint :=
  let d := 1 + u * u
  { x := (1 - u * u) / d,
    y := (2 * u) / d }

def samplePoint (S : Stage) (k : Nat) : PiCirclePoint :=
  point (S.parameter k)

def origin : PiCirclePoint :=
  { x := 0, y := 0 }

def cross (p q : PiCirclePoint) : Rat :=
  p.x * q.y - p.y * q.x

def dot (p q : PiCirclePoint) : Rat :=
  p.x * q.x + p.y * q.y

def normSq (p : PiCirclePoint) : Rat :=
  p.x * p.x + p.y * p.y

def segmentNormSq (p q : PiCirclePoint) : Rat :=
  let dx := q.x - p.x
  let dy := q.y - p.y
  dx * dx + dy * dy

def tangentIntersection (p q : PiCirclePoint) : PiCirclePoint :=
  { x := (q.y - p.y) / cross p q,
    y := (p.x - q.x) / cross p q }

def tangentPoint (S : Stage) (k : Nat) : PiCirclePoint :=
  tangentIntersection (S.samplePoint k) (S.samplePoint (k + 1))

def innerBoundaryFrom (S : Stage) (k count : Nat) : List PiCirclePoint :=
  piCircleArea.innerBoundaryFrom S.samplePoint k count

def innerBoundary (S : Stage) : List PiCirclePoint :=
  S.innerBoundaryFrom 0 (S.subdivisions + 1)

def outerBoundaryFrom (S : Stage) (k count : Nat) : List PiCirclePoint :=
  piCircleArea.outerBoundaryFrom S.samplePoint S.tangentPoint k count

def outerBoundary (S : Stage) : List PiCirclePoint :=
  S.samplePoint 0 :: S.outerBoundaryFrom 0 S.subdivisions

def twiceSignedAreaAux
    (first prev : PiCirclePoint) : List PiCirclePoint -> Rat
  | vertices => piCircleArea.twiceSignedAreaAux cross first prev vertices

def twiceSignedArea : List PiCirclePoint -> Rat
  | [] => 0
  | first :: rest => twiceSignedAreaAux first first rest

def polygonArea (vertices : List PiCirclePoint) : Rat :=
  qabs (twiceSignedArea vertices / 2)

def innerQuarterArea (S : Stage) : Rat :=
  polygonArea (origin :: S.innerBoundary)

def outerQuarterArea (S : Stage) : Rat :=
  polygonArea (origin :: S.outerBoundary)

def areaInterval (S : Stage) : QInterval :=
  { lo := 4 * S.innerQuarterArea,
    hi := 4 * S.outerQuarterArea }

def circumferenceInnerBoundaryFrom
    (S : Stage) (k count : Nat) : List PiCirclePoint :=
  piCircumference.innerBoundaryFrom S.samplePoint k count

def circumferenceInnerBoundary (S : Stage) : List PiCirclePoint :=
  S.circumferenceInnerBoundaryFrom 0 (S.subdivisions + 1)

def circumferenceOuterBoundaryFrom
    (S : Stage) (k count : Nat) : List PiCirclePoint :=
  piCircumference.outerBoundaryFrom S.samplePoint S.tangentPoint k count

def circumferenceOuterBoundary (S : Stage) : List PiCirclePoint :=
  S.samplePoint 0 :: S.circumferenceOuterBoundaryFrom 0 S.subdivisions

def innerQuarterLength (S : Stage) : QInterval :=
  rationalPointPathLength S.innerBoundary S.subdivisions

def outerQuarterLength (S : Stage) : QInterval :=
  rationalPointPathLength S.outerBoundary S.subdivisions

def circumferenceInterval (S : Stage) : QInterval :=
  let innerQuarter :=
    rationalPointPathLength S.circumferenceInnerBoundary S.subdivisions
  let outerQuarter :=
    rationalPointPathLength S.circumferenceOuterBoundary S.subdivisions
  { lo := (4 * innerQuarter.lo) / 2,
    hi := (4 * outerQuarter.hi) / 2 }

def commonCircumferenceInterval (S : Stage) : QInterval :=
  { lo := (4 * S.innerQuarterLength.lo) / 2,
    hi := (4 * S.outerQuarterLength.hi) / 2 }

theorem parameter_zero (S : Stage) :
    S.parameter 0 = 0 := by
  grind [parameter, Rat.div_def]

theorem parameter_last (S : Stage) (hS : 0 < S.subdivisions) :
    S.parameter S.subdivisions = 1 := by
  rw [parameter, Rat.div_def]
  have hne : (S.subdivisions : Rat) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hS
  exact Rat.mul_inv_cancel (S.subdivisions : Rat) hne

theorem parameter_nonneg (S : Stage)
    (hS : 0 < S.subdivisions) (k : Nat) :
    0 <= S.parameter k := by
  unfold parameter
  rw [Rat.div_def]
  have hdenpos : 0 < (S.subdivisions : Rat) :=
    (Rat.natCast_pos).2 hS
  exact Rat.mul_nonneg (Rat.natCast_nonneg : 0 <= (k : Rat))
    (Rat.le_of_lt ((Rat.inv_pos).2 hdenpos))

theorem parameter_mono (S : Stage)
    (hS : 0 < S.subdivisions) {i j : Nat} (hij : i <= j) :
    S.parameter i <= S.parameter j := by
  unfold parameter
  rw [Rat.div_def, Rat.div_def]
  have hdenpos : 0 < (S.subdivisions : Rat) :=
    (Rat.natCast_pos).2 hS
  have hijRat : (i : Rat) <= (j : Rat) :=
    Rat.natCast_le_natCast.2 hij
  exact Rat.mul_le_mul_of_nonneg_right hijRat
    (Rat.le_of_lt ((Rat.inv_pos).2 hdenpos))

theorem parameter_succ_sub (S : Stage) (k : Nat) :
    S.parameter (k + 1) - S.parameter k =
      1 / (S.subdivisions : Rat) := by
  unfold parameter
  rw [Rat.div_def, Rat.div_def, Rat.div_def]
  grind [Rat.sub_eq_add_neg, Rat.add_mul, Rat.mul_add, Rat.add_assoc,
    Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]

theorem parameter_refineIndex_of_refinement
    {coarse fine : Stage}
    (href : RefinesByDoubling coarse fine) (k : Nat) :
    fine.parameter (refineIndex k) = coarse.parameter k := by
  unfold parameter refineIndex RefinesByDoubling at *
  rw [href]
  rw [Rat.div_def, Rat.div_def]
  have htwo : (2 : Rat) ≠ 0 := by native_decide
  grind [Rat.inv_mul_rev, Rat.mul_assoc, Rat.mul_comm,
    Rat.mul_inv_cancel]

theorem point_zero :
    point 0 = ({ x := 1, y := 0 } : PiCirclePoint) := by
  native_decide

theorem point_one :
    point 1 = ({ x := 0, y := 1 } : PiCirclePoint) := by
  native_decide

theorem samplePoint_zero (S : Stage) :
    S.samplePoint 0 = ({ x := 1, y := 0 } : PiCirclePoint) := by
  rw [samplePoint, parameter_zero, point_zero]

theorem samplePoint_last (S : Stage) (hS : 0 < S.subdivisions) :
    S.samplePoint S.subdivisions =
      ({ x := 0, y := 1 } : PiCirclePoint) := by
  rw [samplePoint, parameter_last S hS, point_one]

theorem samplePoint_refineIndex_of_refinement
    {coarse fine : Stage}
    (href : RefinesByDoubling coarse fine) (k : Nat) :
    fine.samplePoint (refineIndex k) = coarse.samplePoint k := by
  unfold samplePoint
  rw [parameter_refineIndex_of_refinement href k]

theorem cross_origin_left (p : PiCirclePoint) :
    cross origin p = 0 := by
  grind [cross, origin, Rat.sub_eq_add_neg]

theorem cross_origin_right (p : PiCirclePoint) :
    cross p origin = 0 := by
  grind [cross, origin, Rat.sub_eq_add_neg]

theorem ratSquare_nonneg (x : Rat) : 0 <= x * x := by
  by_cases hx : 0 <= x
  · exact Rat.mul_nonneg hx hx
  · have hneg : 0 <= -x := by grind
    have hsq : 0 <= (-x) * (-x) := Rat.mul_nonneg hneg hneg
    grind [Rat.mul_neg, Rat.neg_mul, Rat.neg_neg]

theorem one_add_square_pos (u : Rat) : 0 < 1 + u * u := by
  have hs : 0 <= u * u := ratSquare_nonneg u
  grind

theorem one_add_mul_pos_of_nonneg {u v : Rat}
    (hu : 0 <= u) (hv : 0 <= v) : 0 < 1 + u * v := by
  have huv : 0 <= u * v := Rat.mul_nonneg hu hv
  grind

theorem point_cross_formula (u v : Rat) :
    cross (point u) (point v) =
      (2 * (v - u) * (1 + u * v)) /
        ((1 + u * u) * (1 + v * v)) := by
  unfold cross point
  simp
  rw [Rat.div_def, Rat.div_def, Rat.div_def]
  have hdupos : 0 < 1 + u * u := one_add_square_pos u
  have hdvpos : 0 < 1 + v * v := one_add_square_pos v
  have hdune : 1 + u * u ≠ 0 := Rat.ne_of_gt hdupos
  have hdvne : 1 + v * v ≠ 0 := Rat.ne_of_gt hdvpos
  have hmulne : (1 + u * u) * (1 + v * v) ≠ 0 :=
    Rat.ne_of_gt (Rat.mul_pos hdupos hdvpos)
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_assoc, Rat.add_comm,
    Rat.mul_assoc, Rat.mul_comm]

theorem point_cross_nonneg_of_nonneg_of_le
    {u v : Rat} (hu : 0 <= u) (hv : 0 <= v) (huv : u <= v) :
    0 <= cross (point u) (point v) := by
  rw [point_cross_formula]
  have hdiff : 0 <= v - u := by grind [Rat.sub_eq_add_neg]
  have hfactor : 0 <= 1 + u * v :=
    Rat.le_of_lt (one_add_mul_pos_of_nonneg hu hv)
  have hnum : 0 <= 2 * (v - u) * (1 + u * v) := by
    exact Rat.mul_nonneg
      (Rat.mul_nonneg (by native_decide : (0 : Rat) <= 2) hdiff)
      hfactor
  have hden : 0 < (1 + u * u) * (1 + v * v) :=
    Rat.mul_pos (one_add_square_pos u) (one_add_square_pos v)
  rw [Rat.div_def]
  exact Rat.mul_nonneg hnum (Rat.le_of_lt ((Rat.inv_pos).2 hden))

private theorem rat_sq_nonneg (x : Rat) : 0 <= sq x := by
  unfold sq
  by_cases hx : 0 <= x
  · exact Rat.mul_nonneg hx hx
  · have hneg : 0 <= -x := by grind
    have hsq : 0 <= (-x) * (-x) := Rat.mul_nonneg hneg hneg
    grind [Rat.neg_mul, Rat.mul_neg, Rat.neg_neg]

theorem dot_self_eq_normSq (p : PiCirclePoint) :
    dot p p = normSq p := by
  unfold dot normSq
  grind [Rat.add_assoc, Rat.add_comm, Rat.mul_comm]

theorem one_sub_point_dot_formula (u v : Rat) :
    1 - dot (point u) (point v) =
      (2 * (v - u) * (v - u)) /
        ((1 + u * u) * (1 + v * v)) := by
  unfold dot point
  simp
  rw [Rat.div_def, Rat.div_def, Rat.div_def, Rat.div_def, Rat.div_def]
  have hdupos : 0 < 1 + u * u := one_add_square_pos u
  have hdvpos : 0 < 1 + v * v := one_add_square_pos v
  have hdune : 1 + u * u ≠ 0 := Rat.ne_of_gt hdupos
  have hdvne : 1 + v * v ≠ 0 := Rat.ne_of_gt hdvpos
  have hmulne : (1 + u * u) * (1 + v * v) ≠ 0 :=
    Rat.ne_of_gt (Rat.mul_pos hdupos hdvpos)
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_assoc, Rat.add_comm,
    Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

theorem one_sub_point_dot_nonneg (u v : Rat) :
    0 <= 1 - dot (point u) (point v) := by
  rw [one_sub_point_dot_formula]
  have hsq : 0 <= (v - u) * (v - u) := by
    by_cases h : 0 <= v - u
    · exact Rat.mul_nonneg h h
    · have hneg : 0 <= -(v - u) := by grind
      have hsqneg : 0 <= (-(v - u)) * (-(v - u)) :=
        Rat.mul_nonneg hneg hneg
      grind [Rat.neg_mul, Rat.mul_neg, Rat.neg_neg]
  have hnum : 0 <= 2 * ((v - u) * (v - u)) :=
    Rat.mul_nonneg (by native_decide : (0 : Rat) <= 2) hsq
  have hnum' : 0 <= 2 * (v - u) * (v - u) := by
    simpa [Rat.mul_assoc] using hnum
  have hdenpos : 0 < (1 + u * u) * (1 + v * v) :=
    Rat.mul_pos (one_add_square_pos u) (one_add_square_pos v)
  rw [Rat.div_def]
  exact Rat.mul_nonneg hnum'
    (Rat.le_of_lt ((Rat.inv_pos).2 hdenpos))

theorem cross_sq_le_segmentNormSq_of_unit
    {p q : PiCirclePoint}
    (hp : normSq p = 1) (_hq : normSq q = 1) :
    sq (cross p q) <= segmentNormSq p q := by
  have hdiff :
      segmentNormSq p q - sq (cross p q) =
        sq (1 - dot p q) := by
    unfold segmentNormSq normSq cross dot sq at *
    grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_assoc, Rat.add_comm,
      Rat.mul_assoc, Rat.mul_comm]
  have hnonneg :
      0 <= segmentNormSq p q - sq (cross p q) := by
    rw [hdiff]
    exact rat_sq_nonneg (1 - dot p q)
  grind [Rat.sub_eq_add_neg]

theorem cross_sq_le_two_one_sub_dot_of_unit
    {p q : PiCirclePoint}
    (hp : normSq p = 1) (hq : normSq q = 1)
    (honedot : 0 <= 1 - dot p q) :
    sq (cross p q) <= 2 * (1 - dot p q) := by
  have hid :
      sq (cross p q) = (1 - dot p q) * (1 + dot p q) := by
    unfold sq cross dot normSq at *
    grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_assoc, Rat.add_comm,
      Rat.mul_assoc, Rat.mul_comm]
  have hdotle : dot p q <= 1 := by
    grind [Rat.sub_eq_add_neg]
  have hfactor : 1 + dot p q <= 2 := by
    grind
  rw [hid]
  simpa [Rat.mul_comm, Rat.mul_assoc] using
    Rat.mul_le_mul_of_nonneg_left hfactor honedot

theorem segmentNormSq_eq_two_one_sub_dot_of_unit
    {p q : PiCirclePoint}
    (hp : normSq p = 1) (hq : normSq q = 1) :
    segmentNormSq p q = 2 * (1 - dot p q) := by
  unfold segmentNormSq normSq dot at *
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_assoc, Rat.add_comm,
    Rat.mul_assoc, Rat.mul_comm]

theorem cross_left_tangentIntersection
    {p q : PiCirclePoint} (hp : normSq p = 1) :
    cross p (tangentIntersection p q) =
      (1 - dot p q) / cross p q := by
  unfold cross tangentIntersection
  simp
  rw [Rat.div_def, Rat.div_def]
  calc
    p.x * ((p.x - q.x) * (cross p q)⁻¹) -
        p.y * ((q.y - p.y) * (cross p q)⁻¹)
        =
      (p.x * (p.x - q.x) - p.y * (q.y - p.y)) *
        (cross p q)⁻¹ := by
        grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_assoc,
          Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
    _ = (1 - dot p q) * (cross p q)⁻¹ := by
        have hnum :
            p.x * (p.x - q.x) - p.y * (q.y - p.y) =
              1 - dot p q := by
          unfold dot normSq at *
          grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_assoc,
            Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
        rw [hnum]

theorem cross_tangentIntersection_right
    {p q : PiCirclePoint} (hq : normSq q = 1) :
    cross (tangentIntersection p q) q =
      (1 - dot p q) / cross p q := by
  unfold cross tangentIntersection
  simp
  rw [Rat.div_def, Rat.div_def]
  calc
    (q.y - p.y) * (cross p q)⁻¹ * q.y -
        (p.x - q.x) * (cross p q)⁻¹ * q.x
        =
      ((q.y - p.y) * q.y - (p.x - q.x) * q.x) *
        (cross p q)⁻¹ := by
        grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_assoc,
          Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
    _ = (1 - dot p q) * (cross p q)⁻¹ := by
        have hnum :
            (q.y - p.y) * q.y - (p.x - q.x) * q.x =
              1 - dot p q := by
          unfold dot normSq at *
          grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_assoc,
            Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
        rw [hnum]

theorem chordCross_le_tangentCrossSum
    {p q : PiCirclePoint}
    (hp : normSq p = 1) (hq : normSq q = 1)
    (hcross_pos : 0 < cross p q)
    (honedot : 0 <= 1 - dot p q) :
    cross p q <=
      cross p (tangentIntersection p q) +
        cross (tangentIntersection p q) q := by
  let c := cross p q
  have hsq : sq c <= 2 * (1 - dot p q) := by
    dsimp [c]
    exact cross_sq_le_two_one_sub_dot_of_unit hp hq honedot
  have hprod :
      c * c <=
        (cross p (tangentIntersection p q) +
          cross (tangentIntersection p q) q) * c := by
    rw [cross_left_tangentIntersection hp]
    rw [cross_tangentIntersection_right hq]
    dsimp [c]
    have hcne : cross p q ≠ 0 := Rat.ne_of_gt hcross_pos
    calc
      cross p q * cross p q = sq (cross p q) := by
        rfl
      _ <= 2 * (1 - dot p q) := by
        simpa [c] using hsq
      _ = ((1 - dot p q) * (cross p q)⁻¹ +
            (1 - dot p q) * (cross p q)⁻¹) *
            cross p q := by
        grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
  exact Rat.le_of_mul_le_mul_right hprod hcross_pos

theorem chordSegmentNormSq_le_tangentCrossSum_sq
    {p q : PiCirclePoint}
    (hp : normSq p = 1) (hq : normSq q = 1)
    (hcross_pos : 0 < cross p q)
    (hentry_nonneg : 0 <= cross p (tangentIntersection p q))
    (hexit_nonneg : 0 <= cross (tangentIntersection p q) q)
    (honedot : 0 <= 1 - dot p q) :
    segmentNormSq p q <=
      sq (cross p (tangentIntersection p q) +
        cross (tangentIntersection p q) q) := by
  let s := cross p (tangentIntersection p q) +
    cross (tangentIntersection p q) q
  let c := cross p q
  have hs_nonneg : 0 <= s := by
    dsimp [s]
    exact Rat.add_nonneg hentry_nonneg hexit_nonneg
  have hcross_le : c <= s := by
    dsimp [c, s]
    exact chordCross_le_tangentCrossSum hp hq hcross_pos honedot
  have hseg : segmentNormSq p q = 2 * (1 - dot p q) :=
    segmentNormSq_eq_two_one_sub_dot_of_unit hp hq
  have hprod_eq : s * c = 2 * (1 - dot p q) := by
    dsimp [s, c]
    rw [cross_left_tangentIntersection hp]
    rw [cross_tangentIntersection_right hq]
    have hcne : cross p q ≠ 0 := Rat.ne_of_gt hcross_pos
    grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
  rw [hseg]
  rw [←hprod_eq]
  unfold sq
  exact Rat.mul_le_mul_of_nonneg_left hcross_le hs_nonneg

theorem tangentIntersection_on_tangents
    {p q : PiCirclePoint} (hdet : cross p q ≠ 0) :
    dot p (tangentIntersection p q) = 1 /\
      dot q (tangentIntersection p q) = 1 := by
  constructor
  · unfold dot tangentIntersection
    rw [Rat.div_def, Rat.div_def]
    have hnum :
        p.x * (q.y - p.y) + p.y * (p.x - q.x) =
          cross p q := by
      unfold cross
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_assoc,
        Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
    calc
      p.x * ((q.y - p.y) * (cross p q)⁻¹) +
          p.y * ((p.x - q.x) * (cross p q)⁻¹)
          =
        (p.x * (q.y - p.y) + p.y * (p.x - q.x)) *
          (cross p q)⁻¹ := by
          grind [Rat.mul_add, Rat.add_assoc, Rat.add_comm,
            Rat.mul_assoc, Rat.mul_comm]
      _ = cross p q * (cross p q)⁻¹ := by rw [hnum]
      _ = 1 := Rat.mul_inv_cancel _ hdet
  · unfold dot tangentIntersection
    rw [Rat.div_def, Rat.div_def]
    have hnum :
        q.x * (q.y - p.y) + q.y * (p.x - q.x) =
          cross p q := by
      unfold cross
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_assoc,
        Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
    calc
      q.x * ((q.y - p.y) * (cross p q)⁻¹) +
          q.y * ((p.x - q.x) * (cross p q)⁻¹)
          =
        (q.x * (q.y - p.y) + q.y * (p.x - q.x)) *
          (cross p q)⁻¹ := by
          grind [Rat.mul_add, Rat.add_assoc, Rat.add_comm,
            Rat.mul_assoc, Rat.mul_comm]
      _ = cross p q * (cross p q)⁻¹ := by rw [hnum]
      _ = 1 := Rat.mul_inv_cancel _ hdet

theorem tangent_segmentNormSq_eq_cross_sq
    {p a b : PiCirclePoint}
    (hp : normSq p = 1)
    (ha : dot p a = 1)
    (hb : dot p b = 1) :
    segmentNormSq a b = sq (cross a b) := by
  unfold segmentNormSq normSq cross dot sq at *
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_assoc, Rat.add_comm,
    Rat.mul_assoc, Rat.mul_comm]

theorem point_normSq (u : Rat) :
    (point u).x * (point u).x + (point u).y * (point u).y = 1 := by
  unfold point
  simp
  have hdpos : 0 < 1 + u * u := by
    have hs : 0 <= u * u := ratSquare_nonneg u
    grind
  have hdne : 1 + u * u ≠ 0 := Rat.ne_of_gt hdpos
  rw [Rat.div_def, Rat.div_def]
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_assoc, Rat.add_comm,
    Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

theorem samplePoint_normSq (S : Stage) (k : Nat) :
    (S.samplePoint k).x * (S.samplePoint k).x +
      (S.samplePoint k).y * (S.samplePoint k).y = 1 := by
  unfold samplePoint
  exact point_normSq (S.parameter k)

theorem point_normSq_unit (u : Rat) :
    normSq (point u) = 1 := by
  simpa [normSq] using point_normSq u

theorem samplePoint_normSq_unit (S : Stage) (k : Nat) :
    normSq (S.samplePoint k) = 1 := by
  simpa [samplePoint] using point_normSq_unit (S.parameter k)

theorem samplePoint_cross_nonneg_of_order
    (S : Stage) (hS : 0 < S.subdivisions)
    {i j : Nat} (hij : i <= j) :
    0 <= cross (S.samplePoint i) (S.samplePoint j) := by
  unfold samplePoint
  exact point_cross_nonneg_of_nonneg_of_le
    (parameter_nonneg S hS i)
    (parameter_nonneg S hS j)
    (parameter_mono S hS hij)

theorem samplePoint_cross_pos_adjacent
    (S : Stage) (hS : 0 < S.subdivisions) (k : Nat) :
    0 < cross (S.samplePoint k) (S.samplePoint (k + 1)) := by
  unfold samplePoint
  rw [point_cross_formula]
  let u := S.parameter k
  let v := S.parameter (k + 1)
  have hu0 : 0 <= u := by
    dsimp [u]
    exact parameter_nonneg S hS k
  have huv : u <= v := by
    dsimp [u, v]
    exact parameter_mono S hS (Nat.le_succ k)
  have hv0 : 0 <= v := Rat.le_trans hu0 huv
  have hgap : 0 < v - u := by
    dsimp [u, v]
    rw [parameter_succ_sub]
    rw [Rat.div_def, Rat.one_mul]
    exact (Rat.inv_pos).2 ((Rat.natCast_pos).2 hS)
  have honeuv : 0 < 1 + u * v :=
    one_add_mul_pos_of_nonneg hu0 hv0
  have hnum : 0 < 2 * (v - u) * (1 + u * v) :=
    Rat.mul_pos (Rat.mul_pos (by native_decide) hgap) honeuv
  have hden :
      0 < (1 + u * u) * (1 + v * v) :=
    Rat.mul_pos (one_add_square_pos u) (one_add_square_pos v)
  rw [Rat.div_def]
  exact Rat.mul_pos hnum ((Rat.inv_pos).2 hden)

theorem adjacentChordCross_le_tangentCrossSum
    (S : Stage) (hS : 0 < S.subdivisions) (k : Nat) :
    cross (S.samplePoint k) (S.samplePoint (k + 1)) <=
      cross (S.samplePoint k) (S.tangentPoint k) +
        cross (S.tangentPoint k) (S.samplePoint (k + 1)) := by
  unfold tangentPoint
  exact chordCross_le_tangentCrossSum
    (samplePoint_normSq_unit S k)
    (samplePoint_normSq_unit S (k + 1))
    (samplePoint_cross_pos_adjacent S hS k)
    (by
      unfold samplePoint
      exact one_sub_point_dot_nonneg
        (S.parameter k) (S.parameter (k + 1)))

theorem adjacentEntryTangentCross_nonneg
    (S : Stage) (hS : 0 < S.subdivisions) (k : Nat) :
    0 <= cross (S.samplePoint k) (S.tangentPoint k) := by
  unfold tangentPoint
  rw [cross_left_tangentIntersection (samplePoint_normSq_unit S k)]
  rw [Rat.div_def]
  have hnum :
      0 <= 1 - dot (S.samplePoint k) (S.samplePoint (k + 1)) := by
    unfold samplePoint
    exact one_sub_point_dot_nonneg
      (S.parameter k) (S.parameter (k + 1))
  exact Rat.mul_nonneg hnum
    (Rat.le_of_lt ((Rat.inv_pos).2
      (samplePoint_cross_pos_adjacent S hS k)))

theorem adjacentExitTangentCross_nonneg
    (S : Stage) (hS : 0 < S.subdivisions) (k : Nat) :
    0 <= cross (S.tangentPoint k) (S.samplePoint (k + 1)) := by
  unfold tangentPoint
  rw [cross_tangentIntersection_right
    (samplePoint_normSq_unit S (k + 1))]
  rw [Rat.div_def]
  have hnum :
      0 <= 1 - dot (S.samplePoint k) (S.samplePoint (k + 1)) := by
    unfold samplePoint
    exact one_sub_point_dot_nonneg
      (S.parameter k) (S.parameter (k + 1))
  exact Rat.mul_nonneg hnum
    (Rat.le_of_lt ((Rat.inv_pos).2
      (samplePoint_cross_pos_adjacent S hS k)))

theorem adjacentTangentCrossSum_nonneg
    (S : Stage) (hS : 0 < S.subdivisions) (k : Nat) :
    0 <=
      cross (S.samplePoint k) (S.tangentPoint k) +
        cross (S.tangentPoint k) (S.samplePoint (k + 1)) :=
  Rat.add_nonneg
    (adjacentEntryTangentCross_nonneg S hS k)
    (adjacentExitTangentCross_nonneg S hS k)

theorem adjacentChordSegmentNormSq_le_tangentCrossSum_sq
    (S : Stage) (hS : 0 < S.subdivisions) (k : Nat) :
    segmentNormSq (S.samplePoint k) (S.samplePoint (k + 1)) <=
      sq (cross (S.samplePoint k) (S.tangentPoint k) +
        cross (S.tangentPoint k) (S.samplePoint (k + 1))) := by
  unfold tangentPoint
  exact chordSegmentNormSq_le_tangentCrossSum_sq
    (samplePoint_normSq_unit S k)
    (samplePoint_normSq_unit S (k + 1))
    (samplePoint_cross_pos_adjacent S hS k)
    (by
      simpa [tangentPoint] using
        adjacentEntryTangentCross_nonneg S hS k)
    (by
      simpa [tangentPoint] using
        adjacentExitTangentCross_nonneg S hS k)
    (by
      unfold samplePoint
      exact one_sub_point_dot_nonneg
        (S.parameter k) (S.parameter (k + 1)))

theorem samplePoint_dot_self (S : Stage) (k : Nat) :
    dot (S.samplePoint k) (S.samplePoint k) = 1 := by
  rw [dot_self_eq_normSq]
  exact samplePoint_normSq_unit S k

theorem tangentPoint_on_tangents
    (S : Stage) (hS : 0 < S.subdivisions) (k : Nat) :
    dot (S.samplePoint k) (S.tangentPoint k) = 1 /\
      dot (S.samplePoint (k + 1)) (S.tangentPoint k) = 1 := by
  unfold tangentPoint
  exact tangentIntersection_on_tangents
    (Rat.ne_of_gt (samplePoint_cross_pos_adjacent S hS k))

theorem tangentPoint_on_left_tangent
    (S : Stage) (hS : 0 < S.subdivisions) (k : Nat) :
    dot (S.samplePoint k) (S.tangentPoint k) = 1 :=
  (tangentPoint_on_tangents S hS k).1

theorem tangentPoint_on_right_tangent
    (S : Stage) (hS : 0 < S.subdivisions) (k : Nat) :
    dot (S.samplePoint (k + 1)) (S.tangentPoint k) = 1 :=
  (tangentPoint_on_tangents S hS k).2

theorem adjacentEntryTangentSegmentNormSq_eq_cross_sq
    (S : Stage) (hS : 0 < S.subdivisions) (k : Nat) :
    segmentNormSq (S.samplePoint k) (S.tangentPoint k) =
      sq (cross (S.samplePoint k) (S.tangentPoint k)) :=
  tangent_segmentNormSq_eq_cross_sq
    (samplePoint_normSq_unit S k)
    (samplePoint_dot_self S k)
    (tangentPoint_on_left_tangent S hS k)

theorem adjacentExitTangentSegmentNormSq_eq_cross_sq
    (S : Stage) (hS : 0 < S.subdivisions) (k : Nat) :
    segmentNormSq (S.tangentPoint k) (S.samplePoint (k + 1)) =
      sq (cross (S.tangentPoint k) (S.samplePoint (k + 1))) :=
  tangent_segmentNormSq_eq_cross_sq
    (samplePoint_normSq_unit S (k + 1))
    (tangentPoint_on_right_tangent S hS k)
    (samplePoint_dot_self S (k + 1))

theorem innerBoundaryFrom_length (S : Stage) (k count : Nat) :
    (S.innerBoundaryFrom k count).length = count := by
  induction count generalizing k with
  | zero => rfl
  | succ count ih =>
      unfold innerBoundaryFrom
      simp [piCircleArea.innerBoundaryFrom]
      exact ih (k + 1)

theorem innerBoundary_length (S : Stage) :
    S.innerBoundary.length = S.subdivisions + 1 := by
  simp [innerBoundary, innerBoundaryFrom_length]

theorem outerBoundaryFrom_length (S : Stage) (k count : Nat) :
    (S.outerBoundaryFrom k count).length = 2 * count := by
  induction count generalizing k with
  | zero => rfl
  | succ count ih =>
      unfold outerBoundaryFrom
      simp [piCircleArea.outerBoundaryFrom]
      change (S.outerBoundaryFrom (k + 1) count).length + 1 + 1 =
        2 * (count + 1)
      rw [ih (k + 1)]
      omega

theorem outerBoundary_length (S : Stage) :
    S.outerBoundary.length = 2 * S.subdivisions + 1 := by
  simp [outerBoundary, outerBoundaryFrom_length]

theorem circumferenceInnerBoundaryFrom_eq
    (S : Stage) (k count : Nat) :
    S.circumferenceInnerBoundaryFrom k count =
      S.innerBoundaryFrom k count := by
  induction count generalizing k with
  | zero => rfl
  | succ count ih =>
      simp [circumferenceInnerBoundaryFrom, innerBoundaryFrom,
        piCircumference.innerBoundaryFrom, piCircleArea.innerBoundaryFrom]
      exact ih (k + 1)

theorem circumferenceOuterBoundaryFrom_eq
    (S : Stage) (k count : Nat) :
    S.circumferenceOuterBoundaryFrom k count =
      S.outerBoundaryFrom k count := by
  induction count generalizing k with
  | zero => rfl
  | succ count ih =>
      simp [circumferenceOuterBoundaryFrom, outerBoundaryFrom,
        piCircumference.outerBoundaryFrom, piCircleArea.outerBoundaryFrom]
      exact ih (k + 1)

theorem circumferenceInnerBoundary_eq (S : Stage) :
    S.circumferenceInnerBoundary = S.innerBoundary := by
  simp [circumferenceInnerBoundary, innerBoundary,
    circumferenceInnerBoundaryFrom_eq]

theorem circumferenceOuterBoundary_eq (S : Stage) :
    S.circumferenceOuterBoundary = S.outerBoundary := by
  simp [circumferenceOuterBoundary, outerBoundary,
    circumferenceOuterBoundaryFrom_eq]

theorem circumferenceInterval_eq_common (S : Stage) :
    S.circumferenceInterval = S.commonCircumferenceInterval := by
  simp [circumferenceInterval, commonCircumferenceInterval,
    innerQuarterLength, outerQuarterLength, circumferenceInnerBoundary_eq,
    circumferenceOuterBoundary_eq]

end Stage

def dyadicStage (n : Nat) : Stage :=
  { subdivisions := dyadicSubdivisions n }

theorem dyadicStage_positive (n : Nat) :
    0 < (dyadicStage n).subdivisions :=
  dyadicSubdivisions_pos n

theorem dyadicStage_refinesByDoubling (n : Nat) :
    Stage.RefinesByDoubling (dyadicStage n) (dyadicStage (n + 1)) := by
  unfold Stage.RefinesByDoubling dyadicStage
  exact dyadicSubdivisions_succ n

theorem dyadicStage_parameter_refineIndex (n k : Nat) :
    (dyadicStage (n + 1)).parameter (Stage.refineIndex k) =
      (dyadicStage n).parameter k :=
  Stage.parameter_refineIndex_of_refinement
    (dyadicStage_refinesByDoubling n) k

theorem dyadicStage_samplePoint_refineIndex (n k : Nat) :
    (dyadicStage (n + 1)).samplePoint (Stage.refineIndex k) =
      (dyadicStage n).samplePoint k :=
  Stage.samplePoint_refineIndex_of_refinement
    (dyadicStage_refinesByDoubling n) k

def areaIntervalAt (n : Nat) : QInterval :=
  (dyadicStage n).areaInterval

def circumferenceIntervalAt (n : Nat) : QInterval :=
  (dyadicStage n).circumferenceInterval

theorem piCircleArea_compute_eq_stage (n : Nat) :
    piCircleArea.compute n = areaIntervalAt n := by
  rfl

theorem piCircumference_compute_eq_stage (n : Nat) :
    piCircumference.compute n = circumferenceIntervalAt n := by
  rfl

theorem piCircumference_compute_eq_commonStage (n : Nat) :
    piCircumference.compute n =
      (dyadicStage n).commonCircumferenceInterval := by
  rw [piCircumference_compute_eq_stage]
  exact Stage.circumferenceInterval_eq_common (dyadicStage n)

end RationalCircle

namespace ArctanGeometry

/-!
Geometric arctangent.

For rational `x`, the point
`((1 - x^2) / (1 + x^2), 2x / (1 + x^2))` lies on the unit circle at angle
`2 * arctan x`, so the unit-sector area from `0` to this parameter is
`arctan x`.
-/

def stage (n : Nat) : Nat :=
  2 ^ n

theorem stage_pos (n : Nat) : 0 < stage n := by
  unfold stage
  exact Nat.pow_pos (by omega : 0 < 2)

def parameter (y : Rat) (stage k : Nat) : Rat :=
  y * (k : Rat) / (stage : Rat)

def circlePoint (u : Rat) : PiCirclePoint :=
  let d := 1 + u * u
  { x := (1 - u * u) / d,
    y := (2 * u) / d }

def samplePoint (y : Rat) (stage k : Nat) : PiCirclePoint :=
  circlePoint (parameter y stage k)

def originPoint : PiCirclePoint :=
  { x := 0, y := 0 }

def pointCross (p q : PiCirclePoint) : Rat :=
  p.x * q.y - p.y * q.x

def tangentIntersection (p q : PiCirclePoint) : PiCirclePoint :=
  let det := pointCross p q
  { x := (q.y - p.y) / det,
    y := (p.x - q.x) / det }

def outerTangentPoint (y : Rat) (stage k : Nat) : PiCirclePoint :=
  tangentIntersection
    (samplePoint y stage k) (samplePoint y stage (k + 1))

def innerBoundaryFrom (y : Rat) (stage k count : Nat) :
    List PiCirclePoint :=
  piCircleArea.innerBoundaryFrom (samplePoint y stage) k count

def innerBoundary (y : Rat) (stage : Nat) : List PiCirclePoint :=
  innerBoundaryFrom y stage 0 (stage + 1)

def outerBoundaryFrom (y : Rat) (stage k count : Nat) :
    List PiCirclePoint :=
  piCircleArea.outerBoundaryFrom
    (samplePoint y stage) (outerTangentPoint y stage) k count

def outerBoundary (y : Rat) (stage : Nat) : List PiCirclePoint :=
  samplePoint y stage 0 :: outerBoundaryFrom y stage 0 stage

def twiceSignedAreaAux
    (first prev : PiCirclePoint) : List PiCirclePoint -> Rat
  | vertices => piCircleArea.twiceSignedAreaAux pointCross first prev vertices

def twiceSignedArea : List PiCirclePoint -> Rat
  | [] => 0
  | first :: rest => twiceSignedAreaAux first first rest

def polygonArea (vertices : List PiCirclePoint) : Rat :=
  qabs (twiceSignedArea vertices / 2)

def innerSectorArea (y : Rat) (stage : Nat) : Rat :=
  polygonArea (originPoint :: innerBoundary y stage)

def outerSectorArea (y : Rat) (stage : Nat) : Rat :=
  polygonArea (originPoint :: outerBoundary y stage)

def positiveComputeAtStage (y : Rat) (stage : Nat) : QInterval :=
  if stage = 0 then
    { lo := 0, hi := 0 }
  else
    { lo := innerSectorArea y stage,
      hi := outerSectorArea y stage }

def positiveRaw (y : Rat) : RealRaw :=
  if y = 0 then
    RealRaw.ofRat 0
  else
    { compute := fun n => positiveComputeAtStage y (stage n) }

/-- Geometric arctangent on rational slopes. Positive inputs are sector
areas; negative inputs use oddness. -/
def arctanGeom (x : Rat) : RealRaw :=
  if x = 0 then
    RealRaw.ofRat 0
  else if 0 <= x then
    positiveRaw x
  else
    -positiveRaw (-x)

theorem circlePoint_zero :
    circlePoint 0 = ({ x := 1, y := 0 } : PiCirclePoint) := by
  native_decide

theorem samplePoint_zero (y : Rat) (stage : Nat) :
    samplePoint y stage 0 = ({ x := 1, y := 0 } : PiCirclePoint) := by
  unfold samplePoint parameter
  have hparam : y * ((0 : Nat) : Rat) / (stage : Rat) = 0 := by
    rw [show ((0 : Nat) : Rat) = 0 by rfl]
    rw [Rat.div_def]
    simp
  rw [hparam]
  exact circlePoint_zero

theorem samplePoint_self (y : Rat) (stage : Nat) (hstage : 0 < stage) :
    samplePoint y stage stage = circlePoint y := by
  unfold samplePoint parameter
  rw [show y * (stage : Rat) / (stage : Rat) = y by
    rw [Rat.div_def]
    have hne : (stage : Rat) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt hstage
    grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]]

theorem positiveRaw_zero :
    positiveRaw 0 = RealRaw.ofRat 0 := by
  simp [positiveRaw]

theorem arctanGeom_zero :
    arctanGeom 0 = RealRaw.ofRat 0 := by
  simp [arctanGeom]

def functionRaw : PartialRealFunRaw where
  definedAt := fun _ => True
  compute := fun x _ => (arctanGeom x).compute

def representation : Elementary.Arctan.FunctionRepresentation where
  name := "arctan.geom"
  raw := functionRaw

def Valid : Prop :=
  forall x h, RealRaw.ValidCompute (functionRaw.compute x h)

def PowerSeriesAgreesOnUnit : Prop :=
  Elementary.Arctan.Equivalent Elementary.Arctan.powerSeries representation

theorem powerSeries_equiv_geometric_of_agreement
    (h : PowerSeriesAgreesOnUnit) {x : Rat}
    (hx : Elementary.Arctan.powerSeriesDomain x) :
    (arctan x).Equiv (arctanGeom x) := by
  have hgeom : representation.raw.definedAt x := by
    simp [representation, functionRaw]
  simpa [Elementary.Arctan.powerSeries, representation, functionRaw,
    Elementary.Arctan.powerSeriesFunctionRaw, PartialRealFunRaw.AgreeOnOverlap,
    RealRaw.Equiv] using h x hx hgeom

end ArctanGeometry

end ComputableAnalysis
