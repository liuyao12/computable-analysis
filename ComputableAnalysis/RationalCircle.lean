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
  piCircleAreaPolygon.innerBoundaryFrom S.samplePoint k count

def innerBoundary (S : Stage) : List PiCirclePoint :=
  S.innerBoundaryFrom 0 (S.subdivisions + 1)

def outerBoundaryFrom (S : Stage) (k count : Nat) : List PiCirclePoint :=
  piCircleAreaPolygon.outerBoundaryFrom S.samplePoint S.tangentPoint k count

def outerBoundary (S : Stage) : List PiCirclePoint :=
  S.samplePoint 0 :: S.outerBoundaryFrom 0 S.subdivisions

def twiceSignedAreaAux
    (first prev : PiCirclePoint) : List PiCirclePoint -> Rat
  | vertices => piCircleAreaPolygon.twiceSignedAreaAux cross first prev vertices

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

/-- Derivative of the rational circle parametrization
`u ↦ ((1-u^2)/(1+u^2), 2u/(1+u^2))`.  This is an exact rational function,
not a limiting construction. -/
def pointDerivative (u : Rat) : PiCirclePoint :=
  let d := 1 + u * u
  { x := (-4 * u) / (d * d),
    y := (2 * (1 - u * u)) / (d * d) }

/-- The signed area speed of the parametrized unit-circle sector. -/
def sectorAreaSpeed (u : Rat) : Rat :=
  cross (point u) (pointDerivative u)

/-- The unit-sector area density: half of the signed area speed. -/
def sectorAreaDensity (u : Rat) : Rat :=
  sectorAreaSpeed u / 2

theorem sectorAreaSpeed_eq_two_over_one_plus_square (u : Rat) :
    sectorAreaSpeed u = 2 / (1 + u * u) := by
  unfold sectorAreaSpeed pointDerivative cross point
  simp
  rw [Rat.div_def, Rat.div_def, Rat.div_def, Rat.div_def]
  have hdpos : 0 < 1 + u * u := one_add_square_pos u
  have hdne : 1 + u * u ≠ 0 := Rat.ne_of_gt hdpos
  have htwo : (2 : Rat) ≠ 0 := by native_decide
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.add_assoc,
    Rat.add_comm, Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

theorem sectorAreaDensity_eq_one_over_one_plus_square (u : Rat) :
    sectorAreaDensity u = 1 / (1 + u * u) := by
  unfold sectorAreaDensity
  rw [sectorAreaSpeed_eq_two_over_one_plus_square]
  rw [Rat.div_def, Rat.div_def]
  have htwo : (2 : Rat) ≠ 0 := by native_decide
  grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

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

/-- Coordinate law of cosines, in squared-length form.

This is the rational analytic-geometry identity behind the usual formula
`|q - p|^2 = |p|^2 + |q|^2 - 2 p dot q`. -/
theorem segmentNormSq_law_of_cosines (p q : PiCirclePoint) :
    segmentNormSq p q = normSq p + normSq q - 2 * dot p q := by
  unfold segmentNormSq normSq dot
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.add_assoc,
    Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]

/-- If two unit vectors and the chord between them all have squared length
`1`, then their dot product is `1/2`.

Geometrically, the origin together with the two endpoints forms an equilateral
triangle; the included angle is therefore sixty degrees. -/
theorem dot_eq_half_of_unit_equilateral
    {p q : PiCirclePoint}
    (hp : normSq p = 1) (hq : normSq q = 1)
    (hseg : segmentNormSq p q = 1) :
    dot p q = (1 : Rat) / 2 := by
  have h := segmentNormSq_law_of_cosines p q
  rw [hp, hq, hseg] at h
  grind [Rat.div_def, Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
    Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm,
    Rat.mul_inv_cancel]

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
  rw [← hprod_eq]
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

theorem point_segmentNormSq_formula (u v : Rat) :
    segmentNormSq (point u) (point v) =
      (4 * (v - u) * (v - u)) /
        ((1 + u * u) * (1 + v * v)) := by
  rw [segmentNormSq_eq_two_one_sub_dot_of_unit
    (point_normSq_unit u) (point_normSq_unit v)]
  rw [one_sub_point_dot_formula]
  rw [Rat.div_def]
  grind [Rat.mul_assoc, Rat.mul_comm]

private theorem tangent_cross_ratio_formula
    {d s D : Rat} (hd : 0 < d) (hs : 0 < s) (hD : 0 < D) :
    ((2 * d * d) / D) / ((2 * d * s) / D) = d / s := by
  rw [Rat.div_def, Rat.div_def, Rat.div_def]
  have h2 : (0 : Rat) < 2 := by native_decide
  have hDne : D ≠ 0 := Rat.ne_of_gt hD
  have hsne : s ≠ 0 := Rat.ne_of_gt hs
  have hdne : d ≠ 0 := Rat.ne_of_gt hd
  have hfracne : 2 * d * s * D⁻¹ ≠ 0 := by
    exact Rat.ne_of_gt
      (Rat.mul_pos (Rat.mul_pos (Rat.mul_pos h2 hd) hs)
        ((Rat.inv_pos).2 hD))
  rw [Rat.inv_mul_rev]
  grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

theorem point_entry_tangent_cross_formula
    {u v : Rat} (hu0 : 0 <= u) (hv0 : 0 <= v) (huv : u < v) :
    cross (point u) (tangentIntersection (point u) (point v)) =
      (v - u) / (1 + u * v) := by
  rw [cross_left_tangentIntersection (point_normSq_unit u)]
  rw [one_sub_point_dot_formula]
  rw [point_cross_formula]
  have hd : 0 < v - u := by grind [Rat.sub_eq_add_neg]
  have hs : 0 < 1 + u * v := one_add_mul_pos_of_nonneg hu0 hv0
  have hD : 0 < (1 + u * u) * (1 + v * v) :=
    Rat.mul_pos (one_add_square_pos u) (one_add_square_pos v)
  exact tangent_cross_ratio_formula hd hs hD

theorem point_exit_tangent_cross_formula
    {u v : Rat} (hu0 : 0 <= u) (hv0 : 0 <= v) (huv : u < v) :
    cross (tangentIntersection (point u) (point v)) (point v) =
      (v - u) / (1 + u * v) := by
  rw [cross_tangentIntersection_right (point_normSq_unit v)]
  rw [one_sub_point_dot_formula]
  rw [point_cross_formula]
  have hd : 0 < v - u := by grind [Rat.sub_eq_add_neg]
  have hs : 0 < 1 + u * v := one_add_mul_pos_of_nonneg hu0 hv0
  have hD : 0 < (1 + u * u) * (1 + v * v) :=
    Rat.mul_pos (one_add_square_pos u) (one_add_square_pos v)
  exact tangent_cross_ratio_formula hd hs hD

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
      simp [piCircleAreaPolygon.innerBoundaryFrom]
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
      simp [piCircleAreaPolygon.outerBoundaryFrom]
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
        piCircumference.innerBoundaryFrom, piCircleAreaPolygon.innerBoundaryFrom]
      exact ih (k + 1)

theorem circumferenceOuterBoundaryFrom_eq
    (S : Stage) (k count : Nat) :
    S.circumferenceOuterBoundaryFrom k count =
      S.outerBoundaryFrom k count := by
  induction count generalizing k with
  | zero => rfl
  | succ count ih =>
      simp [circumferenceOuterBoundaryFrom, outerBoundaryFrom,
        piCircumference.outerBoundaryFrom, piCircleAreaPolygon.outerBoundaryFrom]
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

/-- A rational number together with one formal point at infinity.

This is deliberately small: for now it is only the codomain of slope-like
quantities such as tangent, where the vertical direction should be a genuine
formal value instead of the rational expression `1 / 0`. -/
inductive ProjectiveRat where
  | finite : Rat -> ProjectiveRat
  | infinity : ProjectiveRat
deriving DecidableEq

namespace ProjectiveRat

def ofOption : Option Rat -> ProjectiveRat
  | some q => finite q
  | none => infinity

def ofHom (n d : Rat) : ProjectiveRat :=
  if _hd : d = 0 then infinity else finite (n / d)

def num : ProjectiveRat -> Rat
  | finite q => q
  | infinity => 1

def den : ProjectiveRat -> Rat
  | finite _ => 1
  | infinity => 0

def neg : ProjectiveRat -> ProjectiveRat
  | finite q => finite (-q)
  | infinity => infinity

def inv : ProjectiveRat -> ProjectiveRat
  | finite q => if _hq : q = 0 then infinity else finite (1 / q)
  | infinity => finite 0

def tanAdd (x y : ProjectiveRat) : ProjectiveRat :=
  ofHom (x.num * y.den + x.den * y.num) (x.den * y.den - x.num * y.num)

def tanSub (x y : ProjectiveRat) : ProjectiveRat :=
  tanAdd x y.neg

def tanDouble (x : ProjectiveRat) : ProjectiveRat :=
  tanAdd x x

theorem ofOption_some (q : Rat) :
    ofOption (some q) = finite q := rfl

theorem ofOption_none :
    ofOption none = infinity := rfl

theorem ofHom_den_zero {n d : Rat} (hd : d = 0) :
    ofHom n d = infinity := by
  unfold ofHom
  simp [hd]

theorem ofHom_den_ne_zero {n d : Rat} (hd : d ≠ 0) :
    ofHom n d = finite (n / d) := by
  unfold ofHom
  simp [hd]

theorem neg_finite (q : Rat) :
    neg (finite q) = finite (-q) := rfl

theorem neg_infinity :
    neg infinity = infinity := rfl

theorem inv_zero :
    inv (finite 0) = infinity := by
  native_decide

theorem inv_finite_ne_zero {q : Rat} (hq : q ≠ 0) :
    inv (finite q) = finite (1 / q) := by
  unfold inv
  simp [hq]

theorem inv_infinity :
    inv infinity = finite 0 := rfl

theorem tanAdd_finite_finite (x y : Rat) :
    tanAdd (finite x) (finite y) = ofHom (x + y) (1 - x * y) := by
  unfold tanAdd num den
  grind [Rat.add_comm]

theorem tanAdd_finite_infinity (x : Rat) :
    tanAdd (finite x) infinity = ofHom 1 (-x) := by
  unfold tanAdd num den
  change ofHom (x * 0 + 1 * 1) (1 * 0 - x * 1) = ofHom 1 (-x)
  have hnum : x * 0 + 1 * 1 = 1 := by grind
  have hden : 1 * 0 - x * 1 = -x := by grind [Rat.sub_eq_add_neg]
  rw [hnum, hden]

theorem tanAdd_infinity_finite (x : Rat) :
    tanAdd infinity (finite x) = ofHom 1 (-x) := by
  unfold tanAdd num den
  change ofHom (1 * 1 + 0 * x) (0 * 1 - 1 * x) = ofHom 1 (-x)
  have hnum : 1 * 1 + 0 * x = 1 := by grind
  have hden : 0 * 1 - 1 * x = -x := by grind [Rat.sub_eq_add_neg]
  rw [hnum, hden]

theorem tanAdd_infinity_infinity :
    tanAdd infinity infinity = finite 0 := by
  native_decide

theorem tanDouble_finite (x : Rat) :
    tanDouble (finite x) = ofHom (2 * x) (1 - x * x) := by
  unfold tanDouble
  rw [tanAdd_finite_finite]
  have htwo : x + x = 2 * x := by
    calc
      x + x = (1 : Rat) * x + (1 : Rat) * x := by grind
      _ = ((1 : Rat) + 1) * x := by rw [Rat.add_mul]
      _ = 2 * x := by
        have h2 : (1 : Rat) + 1 = 2 := by native_decide
        rw [h2]
  rw [htwo]

theorem tanDouble_infinity :
    tanDouble infinity = finite 0 := by
  native_decide

theorem ofHom_neg_num (n d : Rat) :
    ofHom (-n) d = (ofHom n d).neg := by
  unfold ofHom neg
  by_cases hd : d = 0
  · simp [hd]
  · simp [hd]
    rw [Rat.div_def, Rat.div_def]
    grind [Rat.neg_mul]

theorem ofHom_swap_eq_inv {n d : Rat} (hnd : n ≠ 0 ∨ d ≠ 0) :
    ofHom d n = (ofHom n d).inv := by
  unfold ofHom inv
  by_cases hn : n = 0
  · by_cases hd : d = 0
    · exfalso
      cases hnd with
      | inl hn' => exact hn' hn
      | inr hd' => exact hd' hd
    · simp [hn, hd]
      rw [Rat.div_def]
      grind
  · by_cases hd : d = 0
    · simp [hn, hd]
      rw [Rat.div_def]
      grind
    · simp [hn, hd]
      rw [Rat.div_def, Rat.div_def, Rat.div_def]
      grind [Rat.inv_mul_rev, Rat.mul_assoc, Rat.mul_comm,
        Rat.mul_inv_cancel]

end ProjectiveRat

/-- The projective slope of a point: `y / x` when `x ≠ 0`, and infinity when the
point is vertical. -/
def projectiveSlope (p : PiCirclePoint) : ProjectiveRat :=
  ProjectiveRat.ofHom p.y p.x

theorem projectiveSlope_x_zero {p : PiCirclePoint} (hx : p.x = 0) :
    projectiveSlope p = ProjectiveRat.infinity := by
  unfold projectiveSlope
  exact ProjectiveRat.ofHom_den_zero hx

theorem projectiveSlope_x_ne_zero {p : PiCirclePoint} (hx : p.x ≠ 0) :
    projectiveSlope p = ProjectiveRat.finite (p.y / p.x) := by
  unfold projectiveSlope
  exact ProjectiveRat.ofHom_den_ne_zero hx

/-- A homogeneous rational parameter for the extended rational line.

The finite parameter `a / b` is represented by `(a : b)`, while `b = 0`
represents the point at infinity.  This is the natural setting for Farey
subdivision and for using the rational circle parametrization on the full
projective parameter line. -/
structure ProjectiveParameter where
  a : Int
  b : Int
  nonzero : a ≠ 0 ∨ b ≠ 0

namespace ProjectiveParameter

def denom (p : ProjectiveParameter) : Rat :=
  (p.a : Rat) * (p.a : Rat) + (p.b : Rat) * (p.b : Rat)

private theorem rat_intCast_ne_zero_of_ne_zero {z : Int} (hz : z ≠ 0) :
    (z : Rat) ≠ 0 := by
  exact_mod_cast hz

private theorem rat_square_pos_of_ne_zero {x : Rat} (hx : x ≠ 0) :
    0 < x * x := by
  by_cases hxpos : 0 < x
  · exact Rat.mul_pos hxpos hxpos
  · have hxneg : x < 0 := by grind
    have hnegpos : 0 < -x := by grind
    have hsq : 0 < (-x) * (-x) := Rat.mul_pos hnegpos hnegpos
    grind [Rat.neg_mul, Rat.mul_neg, Rat.neg_neg]

theorem denom_pos (p : ProjectiveParameter) : 0 < p.denom := by
  unfold denom
  cases p.nonzero with
  | inl ha =>
      have hsqa : 0 < (p.a : Rat) * (p.a : Rat) :=
        rat_square_pos_of_ne_zero (rat_intCast_ne_zero_of_ne_zero ha)
      have hsqb : 0 <= (p.b : Rat) * (p.b : Rat) :=
        Stage.ratSquare_nonneg (p.b : Rat)
      grind
  | inr hb =>
      have hsqa : 0 <= (p.a : Rat) * (p.a : Rat) :=
        Stage.ratSquare_nonneg (p.a : Rat)
      have hsqb : 0 < (p.b : Rat) * (p.b : Rat) :=
        rat_square_pos_of_ne_zero (rat_intCast_ne_zero_of_ne_zero hb)
      grind

def toRat? (p : ProjectiveParameter) : Option Rat :=
  if _hb : p.b = 0 then none else some ((p.a : Rat) / (p.b : Rat))

def point (p : ProjectiveParameter) : PiCirclePoint :=
  let a : Rat := p.a
  let b : Rat := p.b
  let d := p.denom
  { x := (b * b - a * a) / d,
    y := (2 * a * b) / d }

def zero : ProjectiveParameter := { a := 0, b := 1, nonzero := by omega }
def one : ProjectiveParameter := { a := 1, b := 1, nonzero := by omega }
def infinity : ProjectiveParameter := { a := 1, b := 0, nonzero := by omega }
def negOne : ProjectiveParameter := { a := -1, b := 1, nonzero := by omega }

def finitePair (a b : Int) (hb : b ≠ 0) : ProjectiveParameter :=
  { a := a, b := b, nonzero := Or.inr hb }

theorem toRat?_infinity : infinity.toRat? = none := by
  native_decide

theorem toRat?_finitePair (a b : Int) (hb : b ≠ 0) :
    (finitePair a b hb).toRat? = some ((a : Rat) / (b : Rat)) := by
  unfold toRat? finitePair
  simp [hb]

theorem point_zero :
    zero.point = ({ x := 1, y := 0 } : PiCirclePoint) := by
  native_decide

theorem point_one :
    one.point = ({ x := 0, y := 1 } : PiCirclePoint) := by
  native_decide

theorem point_infinity :
    infinity.point = ({ x := -1, y := 0 } : PiCirclePoint) := by
  native_decide

theorem point_negOne :
    negOne.point = ({ x := 0, y := -1 } : PiCirclePoint) := by
  native_decide

theorem point_normSq (p : ProjectiveParameter) :
    (point p).x * (point p).x + (point p).y * (point p).y = 1 := by
  unfold point denom
  simp
  have hdenpos :
      0 < (p.a : Rat) * (p.a : Rat) + (p.b : Rat) * (p.b : Rat) :=
    denom_pos p
  have hdenne :
      (p.a : Rat) * (p.a : Rat) + (p.b : Rat) * (p.b : Rat) ≠ 0 :=
    Rat.ne_of_gt hdenpos
  rw [Rat.div_def, Rat.div_def]
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.add_assoc,
    Rat.add_comm, Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

theorem point_finitePair_eq_stagePoint (a b : Int) (hb : b ≠ 0) :
    (finitePair a b hb).point = Stage.point ((a : Rat) / (b : Rat)) := by
  unfold finitePair point Stage.point denom
  simp
  have hbRat : (b : Rat) ≠ 0 := rat_intCast_ne_zero_of_ne_zero hb
  rw [Rat.div_def]
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.add_assoc,
    Rat.add_comm, Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

def tan (p : ProjectiveParameter) : ProjectiveRat :=
  projectiveSlope p.point

theorem tan_zero :
    zero.tan = ProjectiveRat.finite 0 := by
  native_decide

theorem tan_one :
    one.tan = ProjectiveRat.infinity := by
  native_decide

theorem tan_infinity :
    infinity.tan = ProjectiveRat.finite 0 := by
  native_decide

def det (p q : ProjectiveParameter) : Int :=
  p.a * q.b - p.b * q.a

theorem det_zero_one : det zero one = -1 := by
  native_decide

theorem det_one_infinity : det one infinity = -1 := by
  native_decide

theorem det_infinity_negOne : det infinity negOne = 1 := by
  native_decide

theorem det_negOne_zero : det negOne zero = -1 := by
  native_decide

theorem mediant_nonzero_of_det_ne
    (p q : ProjectiveParameter) (hdet : det p q ≠ 0) :
    p.a + q.a ≠ 0 ∨ p.b + q.b ≠ 0 := by
  by_cases ha : p.a + q.a = 0
  · by_cases hb : p.b + q.b = 0
    · exfalso
      apply hdet
      have hqa : q.a = -p.a := by omega
      have hqb : q.b = -p.b := by omega
      unfold det
      rw [hqa, hqb]
      grind [Int.mul_comm, Int.mul_neg, Int.neg_mul, Int.sub_eq_add_neg]
    · exact Or.inr hb
  · exact Or.inl ha

def mediantOfDetNe (p q : ProjectiveParameter)
    (hdet : det p q ≠ 0) : ProjectiveParameter :=
  { a := p.a + q.a,
    b := p.b + q.b,
    nonzero := mediant_nonzero_of_det_ne p q hdet }

theorem det_left_mediantOfDetNe
    (p q : ProjectiveParameter) (hdet : det p q ≠ 0) :
    det p (mediantOfDetNe p q hdet) = det p q := by
  unfold det mediantOfDetNe
  grind [Int.mul_add, Int.add_mul, Int.add_assoc, Int.add_comm,
    Int.mul_assoc, Int.mul_comm, Int.sub_eq_add_neg]

theorem det_mediantOfDetNe_right
    (p q : ProjectiveParameter) (hdet : det p q ≠ 0) :
    det (mediantOfDetNe p q hdet) q = det p q := by
  unfold det mediantOfDetNe
  grind [Int.mul_add, Int.add_mul, Int.add_assoc, Int.add_comm,
    Int.mul_assoc, Int.mul_comm, Int.sub_eq_add_neg]

end ProjectiveParameter

structure ProjectiveEdge where
  left : ProjectiveParameter
  right : ProjectiveParameter
  det_ne : ProjectiveParameter.det left right ≠ 0

namespace ProjectiveEdge

def mediant (E : ProjectiveEdge) : ProjectiveParameter :=
  ProjectiveParameter.mediantOfDetNe E.left E.right E.det_ne

theorem det_left_mediant (E : ProjectiveEdge) :
    ProjectiveParameter.det E.left E.mediant =
      ProjectiveParameter.det E.left E.right := by
  simpa [mediant] using
    ProjectiveParameter.det_left_mediantOfDetNe E.left E.right E.det_ne

theorem det_mediant_right (E : ProjectiveEdge) :
    ProjectiveParameter.det E.mediant E.right =
      ProjectiveParameter.det E.left E.right := by
  simpa [mediant] using
    ProjectiveParameter.det_mediantOfDetNe_right E.left E.right E.det_ne

def leftChild (E : ProjectiveEdge) : ProjectiveEdge where
  left := E.left
  right := E.mediant
  det_ne := by
    rw [det_left_mediant]
    exact E.det_ne

def rightChild (E : ProjectiveEdge) : ProjectiveEdge where
  left := E.mediant
  right := E.right
  det_ne := by
    rw [det_mediant_right]
    exact E.det_ne

def subdivideList : List ProjectiveEdge -> List ProjectiveEdge
  | [] => []
  | E :: rest => E.leftChild :: E.rightChild :: subdivideList rest

theorem subdivideList_length (edges : List ProjectiveEdge) :
    (subdivideList edges).length = 2 * edges.length := by
  induction edges with
  | nil => simp [subdivideList]
  | cons E rest ih =>
      simp [subdivideList, ih]
      omega

end ProjectiveEdge

def fullCircleFareySeed : List ProjectiveEdge :=
  [ { left := ProjectiveParameter.zero,
      right := ProjectiveParameter.one,
      det_ne := by native_decide },
    { left := ProjectiveParameter.one,
      right := ProjectiveParameter.infinity,
      det_ne := by native_decide },
    { left := ProjectiveParameter.infinity,
      right := ProjectiveParameter.negOne,
      det_ne := by native_decide },
    { left := ProjectiveParameter.negOne,
      right := ProjectiveParameter.zero,
      det_ne := by native_decide } ]

def fareySubdivide : List ProjectiveEdge -> List ProjectiveEdge :=
  ProjectiveEdge.subdivideList

def fareyStages : Nat -> List ProjectiveEdge -> List ProjectiveEdge
  | 0, edges => edges
  | n + 1, edges => fareyStages n (fareySubdivide edges)

def fullCircleFareyStage (n : Nat) : List ProjectiveEdge :=
  fareyStages n fullCircleFareySeed

theorem fullCircleFareySeed_length : fullCircleFareySeed.length = 4 := by
  native_decide

theorem fareySubdivide_length (edges : List ProjectiveEdge) :
    (fareySubdivide edges).length = 2 * edges.length :=
  ProjectiveEdge.subdivideList_length edges

theorem fareyStages_length (n : Nat) (edges : List ProjectiveEdge) :
    (fareyStages n edges).length = (2 ^ n) * edges.length := by
  induction n generalizing edges with
  | zero => simp [fareyStages]
  | succ n ih =>
      calc
        (fareyStages (n + 1) edges).length =
            (fareyStages n (fareySubdivide edges)).length := by rfl
        _ = (2 ^ n) * (fareySubdivide edges).length := ih _
        _ = (2 ^ n) * (2 * edges.length) := by rw [fareySubdivide_length]
        _ = (2 ^ n * 2) * edges.length := by rw [← Nat.mul_assoc]
        _ = (2 ^ (n + 1)) * edges.length := by rw [Nat.pow_succ]

theorem fullCircleFareyStage_length (n : Nat) :
    (fullCircleFareyStage n).length = 4 * 2 ^ n := by
  unfold fullCircleFareyStage
  rw [fareyStages_length, fullCircleFareySeed_length]
  rw [Nat.mul_comm]

/-- A finite Farey fraction.  We keep numerator and denominator explicit so
mediants remain a primitive operation rather than a disguised arithmetic
average of rationals. -/
structure FareyFraction where
  num : Nat
  den : Nat
  den_pos : 0 < den
deriving Repr, DecidableEq

namespace FareyFraction

def value (q : FareyFraction) : Rat :=
  (q.num : Rat) / (q.den : Rat)

def zero : FareyFraction :=
  { num := 0, den := 1, den_pos := by omega }

def one : FareyFraction :=
  { num := 1, den := 1, den_pos := by omega }

def mediant (p q : FareyFraction) : FareyFraction :=
  { num := p.num + q.num,
    den := p.den + q.den,
    den_pos := Nat.add_pos_left p.den_pos q.den }

theorem value_zero : zero.value = 0 := by
  native_decide

theorem value_one : one.value = 1 := by
  native_decide

theorem value_nonneg (q : FareyFraction) : 0 <= q.value := by
  unfold value
  rw [Rat.div_def]
  exact Rat.mul_nonneg Rat.natCast_nonneg
    (Rat.le_of_lt ((Rat.inv_pos).2 ((Rat.natCast_pos).2 q.den_pos)))

theorem value_le_one_of_num_le_den {q : FareyFraction} (h : q.num <= q.den) :
    q.value <= 1 := by
  unfold value
  have hden_pos : (0 : Rat) < q.den := (Rat.natCast_pos).2 q.den_pos
  apply Rat.le_of_mul_le_mul_right (c := (q.den : Rat))
  · calc
      ((q.num : Rat) / (q.den : Rat)) * (q.den : Rat) =
          (q.num : Rat) := by
            rw [Rat.div_def]
            grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
      _ <= (q.den : Rat) := Rat.natCast_le_natCast.2 h
      _ = (1 : Rat) * (q.den : Rat) := by grind
  · exact hden_pos

private theorem value_le_value_cross {p q : FareyFraction}
    (h : p.value <= q.value) :
    (p.num : Rat) * (q.den : Rat) <=
      (q.num : Rat) * (p.den : Rat) := by
  unfold value at h
  have hpden : (0 : Rat) < p.den := (Rat.natCast_pos).2 p.den_pos
  have hqden : (0 : Rat) < q.den := (Rat.natCast_pos).2 q.den_pos
  have hprod_nonneg : 0 <= (p.den : Rat) * (q.den : Rat) :=
    Rat.le_of_lt (Rat.mul_pos hpden hqden)
  have hmul := Rat.mul_le_mul_of_nonneg_right h hprod_nonneg
  calc
    (p.num : Rat) * (q.den : Rat) =
        ((p.num : Rat) / (p.den : Rat)) *
          ((p.den : Rat) * (q.den : Rat)) := by
          rw [Rat.div_def]
          grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
    _ <= ((q.num : Rat) / (q.den : Rat)) *
          ((p.den : Rat) * (q.den : Rat)) := hmul
    _ = (q.num : Rat) * (p.den : Rat) := by
          rw [Rat.div_def]
          grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

theorem value_le_mediant_of_le {p q : FareyFraction}
    (h : p.value <= q.value) : p.value <= (p.mediant q).value := by
  unfold value mediant at *
  have hpden : (0 : Rat) < p.den := (Rat.natCast_pos).2 p.den_pos
  have hden : (0 : Rat) < ((p.den + q.den : Nat) : Rat) :=
    (Rat.natCast_pos).2 (Nat.add_pos_left p.den_pos q.den)
  have hcross := value_le_value_cross h
  apply Rat.le_of_mul_le_mul_right
    (c := (p.den : Rat) * ((p.den + q.den : Nat) : Rat))
  · calc
      ((p.num : Rat) * (p.den : Rat)⁻¹) *
          ((p.den : Rat) * ((p.den + q.den : Nat) : Rat)) =
          (p.num : Rat) * ((p.den + q.den : Nat) : Rat) := by
            grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
      _ = (p.num : Rat) * (p.den : Rat) +
            (p.num : Rat) * (q.den : Rat) := by
            grind [Rat.mul_add]
      _ <= (p.num : Rat) * (p.den : Rat) +
            (q.num : Rat) * (p.den : Rat) := by
            grind
      _ = (((p.num + q.num : Nat) : Rat) *
              (((p.den + q.den : Nat) : Rat))⁻¹) *
          ((p.den : Rat) * ((p.den + q.den : Nat) : Rat)) := by
            grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_add,
              Rat.mul_inv_cancel]
  · exact Rat.mul_pos hpden hden

theorem mediant_le_value_of_le {p q : FareyFraction}
    (h : p.value <= q.value) : (p.mediant q).value <= q.value := by
  unfold value mediant at *
  have hqden : (0 : Rat) < q.den := (Rat.natCast_pos).2 q.den_pos
  have hden : (0 : Rat) < ((p.den + q.den : Nat) : Rat) :=
    (Rat.natCast_pos).2 (Nat.add_pos_left p.den_pos q.den)
  have hcross := value_le_value_cross h
  apply Rat.le_of_mul_le_mul_right
    (c := ((p.den + q.den : Nat) : Rat) * (q.den : Rat))
  · calc
      (((p.num + q.num : Nat) : Rat) *
          (((p.den + q.den : Nat) : Rat))⁻¹) *
          (((p.den + q.den : Nat) : Rat) * (q.den : Rat)) =
          ((p.num : Rat) + (q.num : Rat)) * (q.den : Rat) := by
            grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
      _ = (p.num : Rat) * (q.den : Rat) +
            (q.num : Rat) * (q.den : Rat) := by
            grind [Rat.add_mul]
      _ <= (q.num : Rat) * (p.den : Rat) +
            (q.num : Rat) * (q.den : Rat) := by
            grind
      _ = ((q.num : Rat) * (q.den : Rat)⁻¹) *
          (((p.den + q.den : Nat) : Rat) * (q.den : Rat)) := by
            grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_add,
              Rat.mul_inv_cancel]
  · exact Rat.mul_pos hden hqden

end FareyFraction

private theorem rat_one_div_le_one_div_of_pos_of_le {a b : Rat}
    (ha : 0 < a) (hab : a <= b) :
    1 / b <= 1 / a := by
  have hb : 0 < b := by grind
  have hane : a ≠ 0 := Rat.ne_of_gt ha
  have hbne : b ≠ 0 := Rat.ne_of_gt hb
  have habpos : 0 < a * b := Rat.mul_pos ha hb
  refine Rat.le_of_mul_le_mul_right (c := a * b) ?_ habpos
  calc
    (1 / b) * (a * b) = a := by
      rw [Rat.div_def]
      grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
    _ <= b := hab
    _ = (1 / a) * (a * b) := by
      rw [Rat.div_def]
      grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

private theorem rat_add_le_add {a b c d : Rat}
    (hab : a <= b) (hcd : c <= d) :
    a + c <= b + d := by
  grind

/-- One cell in the global Farey subdivision of `[0,1]`. -/
structure FareyCell where
  left : FareyFraction
  right : FareyFraction
deriving Repr, DecidableEq

namespace FareyCell

def det (cell : FareyCell) : Int :=
  (cell.right.num : Int) * (cell.left.den : Int) -
    (cell.left.num : Int) * (cell.right.den : Int)

def Adjacent (cell : FareyCell) : Prop :=
  cell.det = 1

def Unit (cell : FareyCell) : Prop :=
  0 <= cell.left.value /\ cell.left.value <= cell.right.value /\
    cell.right.value <= 1

def denSum (cell : FareyCell) : Nat :=
  cell.left.den + cell.right.den

def DenSumAtLeast (n : Nat) (cell : FareyCell) : Prop :=
  n <= cell.denSum

def width (cell : FareyCell) : Rat :=
  cell.right.value - cell.left.value

def toRatInterval (cell : FareyCell) : Rat × Rat :=
  (cell.left.value, cell.right.value)

def mediant (cell : FareyCell) : FareyFraction :=
  cell.left.mediant cell.right

def leftChild (cell : FareyCell) : FareyCell :=
  { left := cell.left, right := cell.mediant }

def rightChild (cell : FareyCell) : FareyCell :=
  { left := cell.mediant, right := cell.right }

theorem det_leftChild (cell : FareyCell) :
    cell.leftChild.det = cell.det := by
  unfold det leftChild mediant FareyFraction.mediant
  simp [Int.natCast_add, Int.mul_add, Int.add_mul]
  grind [Int.sub_eq_add_neg, Int.add_assoc, Int.add_comm,
    Int.mul_assoc, Int.mul_comm]

theorem det_rightChild (cell : FareyCell) :
    cell.rightChild.det = cell.det := by
  unfold det rightChild mediant FareyFraction.mediant
  simp [Int.natCast_add, Int.mul_add, Int.add_mul]
  grind [Int.sub_eq_add_neg, Int.add_assoc, Int.add_comm,
    Int.mul_assoc, Int.mul_comm]

theorem crossDetRat_eq_one_of_adjacent {cell : FareyCell}
    (hadj : cell.Adjacent) :
    (cell.right.num : Rat) * (cell.left.den : Rat) -
      (cell.left.num : Rat) * (cell.right.den : Rat) = 1 := by
  have hrat := congrArg (fun z : Int => (z : Rat)) hadj
  unfold Adjacent det at hrat
  grind [Rat.intCast_natCast, Rat.sub_eq_add_neg, Rat.add_assoc,
    Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]

theorem width_eq_inv_den_mul_den_of_adjacent {cell : FareyCell}
    (hadj : cell.Adjacent) :
    cell.width = 1 / ((cell.left.den : Rat) * (cell.right.den : Rat)) := by
  have hdet := crossDetRat_eq_one_of_adjacent hadj
  have hldpos : (0 : Rat) < cell.left.den :=
    (Rat.natCast_pos).2 cell.left.den_pos
  have hrdpos : (0 : Rat) < cell.right.den :=
    (Rat.natCast_pos).2 cell.right.den_pos
  have hldne : (cell.left.den : Rat) ≠ 0 := Rat.ne_of_gt hldpos
  have hrdne : (cell.right.den : Rat) ≠ 0 := Rat.ne_of_gt hrdpos
  have hldcancel :
      (cell.left.den : Rat) * (cell.left.den : Rat)⁻¹ = 1 :=
    Rat.mul_inv_cancel _ hldne
  have hrdcancel :
      (cell.right.den : Rat) * (cell.right.den : Rat)⁻¹ = 1 :=
    Rat.mul_inv_cancel _ hrdne
  unfold width FareyFraction.value
  calc
    (cell.right.num : Rat) / (cell.right.den : Rat) -
        (cell.left.num : Rat) / (cell.left.den : Rat)
        = (((cell.right.num : Rat) * (cell.left.den : Rat) -
            (cell.left.num : Rat) * (cell.right.den : Rat)) /
            ((cell.left.den : Rat) * (cell.right.den : Rat))) := by
          rw [Rat.div_def, Rat.div_def, Rat.div_def]
          grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
            Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
    _ = 1 / ((cell.left.den : Rat) * (cell.right.den : Rat)) := by
          rw [hdet]

theorem unit_leftChild {cell : FareyCell} (hcell : cell.Unit) :
    cell.leftChild.Unit := by
  rcases hcell with ⟨hl0, hlr, hr1⟩
  unfold Unit leftChild mediant
  exact ⟨hl0, FareyFraction.value_le_mediant_of_le hlr,
    Rat.le_trans (FareyFraction.mediant_le_value_of_le hlr) hr1⟩

theorem unit_rightChild {cell : FareyCell} (hcell : cell.Unit) :
    cell.rightChild.Unit := by
  rcases hcell with ⟨hl0, hlr, hr1⟩
  unfold Unit rightChild mediant
  exact ⟨Rat.le_trans hl0 (FareyFraction.value_le_mediant_of_le hlr),
    FareyFraction.mediant_le_value_of_le hlr, hr1⟩

def subdivideList : List FareyCell -> List FareyCell
  | [] => []
  | cell :: rest => cell.leftChild :: cell.rightChild :: subdivideList rest

def AdjacentList : List FareyCell -> Prop
  | [] => True
  | cell :: rest => cell.Adjacent /\ AdjacentList rest

def UnitList : List FareyCell -> Prop
  | [] => True
  | cell :: rest => cell.Unit /\ UnitList rest

def DenSumListAtLeast (n : Nat) : List FareyCell -> Prop
  | [] => True
  | cell :: rest => cell.DenSumAtLeast n /\ DenSumListAtLeast n rest

def Connects (left right : FareyFraction) : List FareyCell -> Prop
  | [] => left = right
  | cell :: rest => cell.left = left /\ Connects cell.right right rest

def WidthListAtMost (M : Rat) : List FareyCell -> Prop
  | [] => True
  | cell :: rest => cell.width <= M /\ WidthListAtMost M rest

def widthSum : List FareyCell -> Rat
  | [] => 0
  | cell :: rest => cell.width + widthSum rest

def widthSquareSum : List FareyCell -> Rat
  | [] => 0
  | cell :: rest => cell.width * cell.width + widthSquareSum rest

theorem widthSquareSum_nonneg (cells : List FareyCell) :
    0 <= widthSquareSum cells := by
  induction cells with
  | nil =>
      simp [widthSquareSum]
  | cons cell rest ih =>
      exact Rat.add_nonneg (Stage.ratSquare_nonneg cell.width) ih

theorem subdivideList_length (cells : List FareyCell) :
    (subdivideList cells).length = 2 * cells.length := by
  induction cells with
  | nil => simp [subdivideList]
  | cons cell rest ih =>
      simp [subdivideList, ih]
      omega

theorem subdivideList_adjacent {cells : List FareyCell}
    (hcells : AdjacentList cells) : AdjacentList (subdivideList cells) := by
  induction cells with
  | nil =>
      simp [subdivideList, AdjacentList]
  | cons cell rest ih =>
      rcases hcells with ⟨hcell, hrest⟩
      simp [subdivideList, AdjacentList]
      exact ⟨by simpa [Adjacent, det_leftChild] using hcell,
        by simpa [Adjacent, det_rightChild] using hcell, ih hrest⟩

theorem subdivideList_unit {cells : List FareyCell}
    (hcells : UnitList cells) : UnitList (subdivideList cells) := by
  induction cells with
  | nil =>
      simp [subdivideList, UnitList]
  | cons cell rest ih =>
      rcases hcells with ⟨hcell, hrest⟩
      simp [subdivideList, UnitList]
      exact ⟨unit_leftChild hcell, unit_rightChild hcell, ih hrest⟩

theorem leftChild_denSum_ge_succ {cell : FareyCell} {n : Nat}
    (h : cell.DenSumAtLeast n) :
    cell.leftChild.DenSumAtLeast (n + 1) := by
  have hleftpos : 0 < cell.left.den := cell.left.den_pos
  unfold DenSumAtLeast denSum at h ⊢
  simp [leftChild, mediant, FareyFraction.mediant]
  omega

theorem rightChild_denSum_ge_succ {cell : FareyCell} {n : Nat}
    (h : cell.DenSumAtLeast n) :
    cell.rightChild.DenSumAtLeast (n + 1) := by
  have hrightpos : 0 < cell.right.den := cell.right.den_pos
  unfold DenSumAtLeast denSum at h ⊢
  simp [rightChild, mediant, FareyFraction.mediant]
  omega

theorem subdivideList_denSum_ge_succ {cells : List FareyCell} {n : Nat}
    (hcells : DenSumListAtLeast n cells) :
    DenSumListAtLeast (n + 1) (subdivideList cells) := by
  induction cells with
  | nil =>
      simp [subdivideList, DenSumListAtLeast]
  | cons cell rest ih =>
      rcases hcells with ⟨hcell, hrest⟩
      simp [subdivideList, DenSumListAtLeast]
      exact ⟨leftChild_denSum_ge_succ hcell,
        rightChild_denSum_ge_succ hcell, ih hrest⟩

theorem subdivideList_connects {left right : FareyFraction}
    {cells : List FareyCell}
    (hcells : Connects left right cells) :
    Connects left right (subdivideList cells) := by
  induction cells generalizing left with
  | nil =>
      simpa [subdivideList, Connects] using hcells
  | cons cell rest ih =>
      rcases hcells with ⟨hleft, hrest⟩
      simp [subdivideList, Connects, leftChild, rightChild]
      exact ⟨hleft, ih hrest⟩

theorem width_nonneg_of_unit {cell : FareyCell} (hcell : cell.Unit) :
    0 <= cell.width := by
  rcases hcell with ⟨_hl0, hlr, _hr1⟩
  unfold width
  grind [Rat.sub_eq_add_neg]

theorem child_width_sum (cell : FareyCell) :
    cell.leftChild.width + cell.rightChild.width = cell.width := by
  unfold leftChild rightChild width mediant
  grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]

theorem subdivideList_widthSum (cells : List FareyCell) :
    widthSum (subdivideList cells) = widthSum cells := by
  induction cells with
  | nil =>
      simp [subdivideList, widthSum]
  | cons cell rest ih =>
      simp [subdivideList, widthSum]
      rw [ih]
      have hchild := child_width_sum cell
      grind [Rat.add_assoc, Rat.add_comm]

theorem widthSum_eq_value_sub_of_connects
    {left right : FareyFraction} {cells : List FareyCell}
    (hcells : Connects left right cells) :
    widthSum cells = right.value - left.value := by
  induction cells generalizing left with
  | nil =>
      simp [Connects, widthSum] at hcells ⊢
      grind [Rat.sub_eq_add_neg]
  | cons cell rest ih =>
      rcases hcells with ⟨hleft, hrest⟩
      have htail := ih hrest
      unfold widthSum width
      rw [htail]
      rw [hleft]
      grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]

theorem widthSquare_le_bound_mul_width
    {cell : FareyCell} {M : Rat}
    (hunit : cell.Unit) (hbound : cell.width <= M) :
    cell.width * cell.width <= M * cell.width := by
  exact Rat.mul_le_mul_of_nonneg_right hbound
    (width_nonneg_of_unit hunit)

theorem widthSquareSum_le_bound_mul_widthSum
    {cells : List FareyCell} {M : Rat}
    (hunit : UnitList cells) (hbound : WidthListAtMost M cells) :
    widthSquareSum cells <= M * widthSum cells := by
  induction cells with
  | nil =>
      simp [widthSquareSum, widthSum]
  | cons cell rest ih =>
      rcases hunit with ⟨hcellUnit, hrestUnit⟩
      rcases hbound with ⟨hcellBound, hrestBound⟩
      have hhead := widthSquare_le_bound_mul_width hcellUnit hcellBound
      have htail := ih hrestUnit hrestBound
      simp [widthSquareSum, widthSum]
      calc
        cell.width * cell.width + widthSquareSum rest
            <= M * cell.width + M * widthSum rest :=
              rat_add_le_add hhead htail
        _ = M * (cell.width + widthSum rest) := by
              grind [Rat.mul_add, Rat.add_assoc, Rat.add_comm,
                Rat.mul_assoc, Rat.mul_comm]

theorem den_product_ge_denSum_sub_one (cell : FareyCell) :
    cell.left.den + cell.right.den - 1 <=
      cell.left.den * cell.right.den := by
  have hb1 : 1 <= cell.right.den :=
    Nat.succ_le_of_lt cell.right.den_pos
  have hbpred : cell.right.den - 1 + 1 = cell.right.den :=
    Nat.sub_add_cancel hb1
  calc
    cell.left.den + cell.right.den - 1 =
        cell.left.den + (cell.right.den - 1) := by omega
    _ <= cell.left.den + cell.left.den * (cell.right.den - 1) := by
        exact Nat.add_le_add_left
          (Nat.le_mul_of_pos_left (cell.right.den - 1)
            cell.left.den_pos)
          cell.left.den
    _ = cell.left.den * ((cell.right.den - 1) + 1) := by
        rw [Nat.mul_add, Nat.mul_one]
        omega
    _ = cell.left.den * cell.right.den := by rw [hbpred]

theorem den_product_ge_succ_of_denSumAtLeast
    {cell : FareyCell} {n : Nat}
    (h : cell.DenSumAtLeast (n + 2)) :
    n + 1 <= cell.left.den * cell.right.den := by
  have hprod := den_product_ge_denSum_sub_one cell
  unfold DenSumAtLeast denSum at h
  omega

theorem width_le_one_div_succ_of_adjacent_denSumAtLeast
    {cell : FareyCell} {n : Nat}
    (hadj : cell.Adjacent) (hden : cell.DenSumAtLeast (n + 2)) :
    cell.width <= 1 / (((n + 1 : Nat) : Rat)) := by
  rw [width_eq_inv_den_mul_den_of_adjacent hadj]
  have hprodNat := den_product_ge_succ_of_denSumAtLeast hden
  have hprodRat :
      (((n + 1 : Nat) : Rat)) <=
        (cell.left.den : Rat) * (cell.right.den : Rat) := by
    rw [← Rat.natCast_mul]
    exact (Rat.natCast_le_natCast).2 hprodNat
  exact rat_one_div_le_one_div_of_pos_of_le
    ((Rat.natCast_pos).2 (Nat.succ_pos n)) hprodRat

theorem widthListAtMost_one_div_succ_of_adjacent_denSum
    {cells : List FareyCell} {n : Nat}
    (hadj : AdjacentList cells)
    (hden : DenSumListAtLeast (n + 2) cells) :
    WidthListAtMost (1 / (((n + 1 : Nat) : Rat))) cells := by
  induction cells with
  | nil =>
      simp [WidthListAtMost]
  | cons cell rest ih =>
      rcases hadj with ⟨hcellAdj, hrestAdj⟩
      rcases hden with ⟨hcellDen, hrestDen⟩
      change cell.width <= 1 / (((n + 1 : Nat) : Rat)) /\
        WidthListAtMost (1 / (((n + 1 : Nat) : Rat))) rest
      exact ⟨width_le_one_div_succ_of_adjacent_denSumAtLeast
          hcellAdj hcellDen,
        ih hrestAdj hrestDen⟩

end FareyCell

/-- The shared Farey mesh on `[0,1]`, used for prefix-style computations. -/
def fareyUnitSeed : List FareyCell :=
  [ { left := FareyFraction.zero, right := FareyFraction.one } ]

def fareyUnitSubdivide : List FareyCell -> List FareyCell :=
  FareyCell.subdivideList

def fareyUnitStage : Nat -> List FareyCell
  | 0 => fareyUnitSeed
  | n + 1 => fareyUnitSubdivide (fareyUnitStage n)

theorem fareyUnitSeed_length : fareyUnitSeed.length = 1 := by
  native_decide

theorem fareyUnitSubdivide_length (cells : List FareyCell) :
    (fareyUnitSubdivide cells).length = 2 * cells.length :=
  FareyCell.subdivideList_length cells

theorem fareyUnitStage_length (n : Nat) :
    (fareyUnitStage n).length = 2 ^ n := by
  induction n with
  | zero =>
      simp [fareyUnitStage, fareyUnitSeed_length]
  | succ n ih =>
      calc
        (fareyUnitStage (n + 1)).length =
            (fareyUnitSubdivide (fareyUnitStage n)).length := by rfl
        _ = 2 * (fareyUnitStage n).length := fareyUnitSubdivide_length _
        _ = 2 * 2 ^ n := by rw [ih]
        _ = 2 ^ (n + 1) := by rw [Nat.pow_succ, Nat.mul_comm]

theorem fareyUnitSeed_adjacent :
    FareyCell.AdjacentList fareyUnitSeed := by
  simp [fareyUnitSeed, FareyCell.AdjacentList, FareyCell.Adjacent,
    FareyCell.det, FareyFraction.zero, FareyFraction.one]

theorem fareyUnitSubdivide_adjacent {cells : List FareyCell}
    (hcells : FareyCell.AdjacentList cells) :
    FareyCell.AdjacentList (fareyUnitSubdivide cells) :=
  FareyCell.subdivideList_adjacent hcells

theorem fareyUnitStage_adjacent (n : Nat) :
    FareyCell.AdjacentList (fareyUnitStage n) := by
  induction n with
  | zero =>
      exact fareyUnitSeed_adjacent
  | succ _ ih =>
      exact fareyUnitSubdivide_adjacent ih

theorem fareyUnitSeed_unit : FareyCell.UnitList fareyUnitSeed := by
  simp [fareyUnitSeed, FareyCell.UnitList, FareyCell.Unit,
    FareyFraction.value_zero, FareyFraction.value_one]
  native_decide

theorem fareyUnitSubdivide_unit {cells : List FareyCell}
    (hcells : FareyCell.UnitList cells) :
    FareyCell.UnitList (fareyUnitSubdivide cells) :=
  FareyCell.subdivideList_unit hcells

theorem fareyUnitStage_unit (n : Nat) :
    FareyCell.UnitList (fareyUnitStage n) := by
  induction n with
  | zero =>
      exact fareyUnitSeed_unit
  | succ n ih =>
      exact fareyUnitSubdivide_unit ih

theorem fareyUnitSeed_connects :
    FareyCell.Connects FareyFraction.zero FareyFraction.one
      fareyUnitSeed := by
  simp [fareyUnitSeed, FareyCell.Connects]

theorem fareyUnitSubdivide_connects
    {left right : FareyFraction} {cells : List FareyCell}
    (hcells : FareyCell.Connects left right cells) :
    FareyCell.Connects left right (fareyUnitSubdivide cells) :=
  FareyCell.subdivideList_connects hcells

theorem fareyUnitStage_connects (n : Nat) :
    FareyCell.Connects FareyFraction.zero FareyFraction.one
      (fareyUnitStage n) := by
  induction n with
  | zero =>
      exact fareyUnitSeed_connects
  | succ n ih =>
      exact fareyUnitSubdivide_connects ih

theorem fareyUnitSeed_denSum_ge_two :
    FareyCell.DenSumListAtLeast 2 fareyUnitSeed := by
  simp [fareyUnitSeed, FareyCell.DenSumListAtLeast,
    FareyCell.DenSumAtLeast, FareyCell.denSum,
    FareyFraction.zero, FareyFraction.one]

theorem fareyUnitSubdivide_denSum_ge_succ
    {cells : List FareyCell} {n : Nat}
    (hcells : FareyCell.DenSumListAtLeast n cells) :
    FareyCell.DenSumListAtLeast (n + 1) (fareyUnitSubdivide cells) :=
  FareyCell.subdivideList_denSum_ge_succ hcells

theorem fareyUnitStage_denSum_ge (n : Nat) :
    FareyCell.DenSumListAtLeast (n + 2) (fareyUnitStage n) := by
  induction n with
  | zero =>
      exact fareyUnitSeed_denSum_ge_two
  | succ _ ih =>
      exact fareyUnitSubdivide_denSum_ge_succ ih

theorem fareyUnitSeed_widthSum :
    FareyCell.widthSum fareyUnitSeed = 1 := by
  native_decide

theorem fareyUnitSubdivide_widthSum (cells : List FareyCell) :
    FareyCell.widthSum (fareyUnitSubdivide cells) =
      FareyCell.widthSum cells :=
  FareyCell.subdivideList_widthSum cells

theorem fareyUnitStage_widthSum (n : Nat) :
    FareyCell.widthSum (fareyUnitStage n) = 1 := by
  have hconnect := FareyCell.widthSum_eq_value_sub_of_connects
    (fareyUnitStage_connects n)
  rw [hconnect]
  native_decide

theorem fareyUnitStage_widthSquareSum_le_one_div_succ (n : Nat) :
    FareyCell.widthSquareSum (fareyUnitStage n) <=
      1 / (((n + 1 : Nat) : Rat)) := by
  have hbound :
      FareyCell.WidthListAtMost
        (1 / (((n + 1 : Nat) : Rat))) (fareyUnitStage n) :=
    FareyCell.widthListAtMost_one_div_succ_of_adjacent_denSum
      (fareyUnitStage_adjacent n) (fareyUnitStage_denSum_ge n)
  have hsquares :=
    FareyCell.widthSquareSum_le_bound_mul_widthSum
      (fareyUnitStage_unit n) hbound
  rw [fareyUnitStage_widthSum n] at hsquares
  simpa using hsquares

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

theorem piCircleAreaPolygon_compute_eq_stage (n : Nat) :
    piCircleAreaPolygon.compute n = areaIntervalAt n := by
  rfl

theorem piCircumference_compute_eq_stage (n : Nat) :
    piCircumference.compute n = circumferenceIntervalAt n := by
  rfl

theorem piCircumference_compute_eq_commonStage (n : Nat) :
    piCircumference.compute n =
      (dyadicStage n).commonCircumferenceInterval := by
  rw [piCircumference_compute_eq_stage]
  exact Stage.circumferenceInterval_eq_common (dyadicStage n)

namespace Trigonometry

/-!
Exact trigonometry on the rational circle.

The parameter `u` is the rational slope coordinate for the stereographic
circle chart.  This gives a first, fully rational layer of circle-coordinate
identities before the later angle-to-point algorithm turns arbitrary raw
angles into circle points.
-/

def point (u : Rat) : PiCirclePoint :=
  Stage.point u

def cos (u : Rat) : Rat :=
  (point u).x

def sin (u : Rat) : Rat :=
  (point u).y

def finiteTan (u : Rat) : Rat :=
  sin u / cos u

def tan (u : Rat) : ProjectiveRat :=
  projectiveSlope (point u)

def cot (u : Rat) : Rat :=
  cos u / sin u

def sec (u : Rat) : Rat :=
  1 / cos u

def csc (u : Rat) : Rat :=
  1 / sin u

def cosRaw (u : Rat) : RealRaw :=
  RealRaw.ofRat (cos u)

def sinRaw (u : Rat) : RealRaw :=
  RealRaw.ofRat (sin u)

def tanRaw (u : Rat) : RealRaw :=
  RealRaw.ofRat (finiteTan u)

def cotRaw (u : Rat) : RealRaw :=
  RealRaw.ofRat (cot u)

def secRaw (u : Rat) : RealRaw :=
  RealRaw.ofRat (sec u)

def cscRaw (u : Rat) : RealRaw :=
  RealRaw.ofRat (csc u)

def dyadicPoint (n k : Nat) : PiCirclePoint :=
  (dyadicStage n).samplePoint k

def dyadicCos (n k : Nat) : Rat :=
  (dyadicPoint n k).x

def dyadicSin (n k : Nat) : Rat :=
  (dyadicPoint n k).y

def pointMul (p q : PiCirclePoint) : PiCirclePoint :=
  { x := p.x * q.x - p.y * q.y,
    y := p.x * q.y + p.y * q.x }

def circleOne : PiCirclePoint :=
  { x := 1, y := 0 }

def pointConj (p : PiCirclePoint) : PiCirclePoint :=
  { x := p.x, y := -p.y }

def composedPoint (u v : Rat) : PiCirclePoint :=
  pointMul (point u) (point v)

def composedCos (u v : Rat) : Rat :=
  (composedPoint u v).x

def composedSin (u v : Rat) : Rat :=
  (composedPoint u v).y

def doublePoint (u : Rat) : PiCirclePoint :=
  composedPoint u u

def doubleCos (u : Rat) : Rat :=
  (doublePoint u).x

def doubleSin (u : Rat) : Rat :=
  (doublePoint u).y

def quarterComplementParameter (u : Rat) : Rat :=
  (1 - u) / (1 + u)

def chartAddNum (u v : Rat) : Rat :=
  u + v

def chartAddDen (u v : Rat) : Rat :=
  1 - u * v

def chartAddParameter (u v : Rat) : Rat :=
  chartAddNum u v / chartAddDen u v

def chartAddNormDen (u v : Rat) : Rat :=
  sq (chartAddDen u v) + sq (chartAddNum u v)

def chartAddCosNum (u v : Rat) : Rat :=
  sq (chartAddDen u v) - sq (chartAddNum u v)

def chartAddSinNum (u v : Rat) : Rat :=
  2 * chartAddNum u v * chartAddDen u v

theorem cos_eq (u : Rat) :
    cos u = (1 - u * u) / (1 + u * u) := rfl

theorem sin_eq (u : Rat) :
    sin u = (2 * u) / (1 + u * u) := rfl

theorem point_eq (u : Rat) :
    point u = ({ x := cos u, y := sin u } : PiCirclePoint) := by
  rfl

theorem cos_sq_add_sin_sq (u : Rat) :
    sq (cos u) + sq (sin u) = 1 := by
  simpa [point, cos, sin, sq] using Stage.point_normSq u

theorem pointMul_normSq_of_unit
    {p q : PiCirclePoint}
    (hp : Stage.normSq p = 1) (hq : Stage.normSq q = 1) :
    Stage.normSq (pointMul p q) = 1 := by
  unfold pointMul Stage.normSq at *
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.add_assoc,
    Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]

theorem pointMul_normSq (p q : PiCirclePoint) :
    Stage.normSq (pointMul p q) = Stage.normSq p * Stage.normSq q := by
  cases p; cases q
  simp [pointMul, Stage.normSq]
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.add_assoc,
    Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]

theorem pointMul_comm (p q : PiCirclePoint) :
    pointMul p q = pointMul q p := by
  cases p; cases q
  simp [pointMul]
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.add_assoc,
    Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]

theorem pointMul_assoc (p q r : PiCirclePoint) :
    pointMul (pointMul p q) r = pointMul p (pointMul q r) := by
  cases p; cases q; cases r
  simp [pointMul]
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.add_assoc,
    Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]

theorem pointMul_one_left (p : PiCirclePoint) :
    pointMul circleOne p = p := by
  cases p
  simp [pointMul, circleOne]
  grind [Rat.sub_eq_add_neg]

theorem pointMul_one_right (p : PiCirclePoint) :
    pointMul p circleOne = p := by
  cases p
  simp [pointMul, circleOne]
  grind [Rat.sub_eq_add_neg]

theorem pointMul_conj_of_unit {p : PiCirclePoint}
    (hp : Stage.normSq p = 1) :
    pointMul p (pointConj p) = circleOne := by
  cases p
  simp [pointMul, pointConj, circleOne, Stage.normSq] at *
  constructor
  · grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.add_assoc,
      Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
  · grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.add_assoc,
      Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]

theorem composedPoint_normSq (u v : Rat) :
    Stage.normSq (composedPoint u v) = 1 :=
  pointMul_normSq_of_unit (Stage.point_normSq_unit u)
    (Stage.point_normSq_unit v)

theorem composed_cos_eq (u v : Rat) :
    composedCos u v = cos u * cos v - sin u * sin v := by
  rfl

theorem composed_sin_eq (u v : Rat) :
    composedSin u v = cos u * sin v + sin u * cos v := by
  rfl

theorem chartAdd_normDen_eq (u v : Rat) :
    chartAddNormDen u v = (1 + u * u) * (1 + v * v) := by
  unfold chartAddNormDen chartAddDen chartAddNum sq
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.add_assoc,
    Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]

theorem chartAdd_normDen_pos (u v : Rat) :
    0 < chartAddNormDen u v := by
  rw [chartAdd_normDen_eq]
  exact Rat.mul_pos (Stage.one_add_square_pos u) (Stage.one_add_square_pos v)

theorem ratSquare_pos_of_ne_zero {x : Rat} (hx : x ≠ 0) :
    0 < x * x := by
  by_cases hpos : 0 < x
  · exact Rat.mul_pos hpos hpos
  · have hneg : 0 < -x := by grind
    have hs : 0 < (-x) * (-x) := Rat.mul_pos hneg hneg
    grind [Rat.neg_mul, Rat.mul_neg, Rat.neg_neg]

theorem chartAdd_cosNum_eq (u v : Rat) :
    chartAddCosNum u v =
      (1 - u * u) * (1 - v * v) - (2 * u) * (2 * v) := by
  unfold chartAddCosNum chartAddDen chartAddNum sq
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.add_assoc,
    Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]

theorem chartAdd_sinNum_eq (u v : Rat) :
    chartAddSinNum u v =
      (1 - u * u) * (2 * v) + (2 * u) * (1 - v * v) := by
  unfold chartAddSinNum chartAddDen chartAddNum
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.add_assoc,
    Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]

theorem composedCos_chartAdd_denominator_cleared (u v : Rat) :
    ((1 + u * u) * (1 + v * v)) * composedCos u v =
      chartAddCosNum u v := by
  rw [composed_cos_eq, chartAdd_cosNum_eq]
  unfold cos sin point Stage.point
  simp [Rat.div_def]
  have hdupos : 0 < 1 + u * u := Stage.one_add_square_pos u
  have hdvpos : 0 < 1 + v * v := Stage.one_add_square_pos v
  have hdune : 1 + u * u ≠ 0 := Rat.ne_of_gt hdupos
  have hdvne : 1 + v * v ≠ 0 := Rat.ne_of_gt hdvpos
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.add_assoc,
    Rat.add_comm, Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

theorem composedSin_chartAdd_denominator_cleared (u v : Rat) :
    ((1 + u * u) * (1 + v * v)) * composedSin u v =
      chartAddSinNum u v := by
  rw [composed_sin_eq, chartAdd_sinNum_eq]
  unfold cos sin point Stage.point
  simp [Rat.div_def]
  have hdupos : 0 < 1 + u * u := Stage.one_add_square_pos u
  have hdvpos : 0 < 1 + v * v := Stage.one_add_square_pos v
  have hdune : 1 + u * u ≠ 0 := Rat.ne_of_gt hdupos
  have hdvne : 1 + v * v ≠ 0 := Rat.ne_of_gt hdvpos
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.add_assoc,
    Rat.add_comm, Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

theorem chartPair_cos_denominator_cleared {a b : Rat} (ha : a ≠ 0) :
    (a * a + b * b) *
      ((1 - (b / a) * (b / a)) / (1 + (b / a) * (b / a))) =
      a * a - b * b := by
  simp [Rat.div_def]
  have haa : a * a ≠ 0 := Rat.ne_of_gt (ratSquare_pos_of_ne_zero ha)
  have hzpos :
      0 < 1 + (b * a⁻¹) * (b * a⁻¹) :=
    Stage.one_add_square_pos (b * a⁻¹)
  have hzne : 1 + (b * a⁻¹) * (b * a⁻¹) ≠ 0 :=
    Rat.ne_of_gt hzpos
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.add_assoc,
    Rat.add_comm, Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

theorem chartPair_sin_denominator_cleared {a b : Rat} (ha : a ≠ 0) :
    (a * a + b * b) *
      ((2 * (b / a)) / (1 + (b / a) * (b / a))) =
      2 * b * a := by
  simp [Rat.div_def]
  have haa : a * a ≠ 0 := Rat.ne_of_gt (ratSquare_pos_of_ne_zero ha)
  have hzpos :
      0 < 1 + (b * a⁻¹) * (b * a⁻¹) :=
    Stage.one_add_square_pos (b * a⁻¹)
  have hzne : 1 + (b * a⁻¹) * (b * a⁻¹) ≠ 0 :=
    Rat.ne_of_gt hzpos
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.add_assoc,
    Rat.add_comm, Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

theorem cos_chartAdd_denominator_cleared {u v : Rat}
    (hden : Ne (chartAddDen u v) 0) :
    chartAddNormDen u v * cos (chartAddParameter u v) =
      chartAddCosNum u v := by
  simpa [chartAddNormDen, chartAddCosNum, chartAddParameter, sq, cos,
    point, Stage.point] using
    (chartPair_cos_denominator_cleared
      (a := chartAddDen u v) (b := chartAddNum u v) hden)

theorem sin_chartAdd_denominator_cleared {u v : Rat}
    (hden : Ne (chartAddDen u v) 0) :
    chartAddNormDen u v * sin (chartAddParameter u v) =
      chartAddSinNum u v := by
  simpa [chartAddNormDen, chartAddSinNum, chartAddParameter, sq, sin,
    point, Stage.point, Rat.mul_assoc] using
    (chartPair_sin_denominator_cleared
      (a := chartAddDen u v) (b := chartAddNum u v) hden)

theorem rat_eq_of_pos_mul_eq_mul {a b c : Rat} (hc : 0 < c)
    (h : c * a = c * b) : a = b := by
  have hcne : c ≠ 0 := Rat.ne_of_gt hc
  calc
    a = c⁻¹ * (c * a) := by
      have hcancel : c⁻¹ * c = 1 := Rat.inv_mul_cancel c hcne
      grind [Rat.mul_assoc, Rat.mul_comm]
    _ = c⁻¹ * (c * b) := by rw [h]
    _ = b := by
      have hcancel : c⁻¹ * c = 1 := Rat.inv_mul_cancel c hcne
      grind [Rat.mul_assoc, Rat.mul_comm]

theorem composedCos_eq_cos_chartAdd {u v : Rat}
    (hden : Ne (chartAddDen u v) 0) :
    composedCos u v = cos (chartAddParameter u v) := by
  apply rat_eq_of_pos_mul_eq_mul
    (c := chartAddNormDen u v) (chartAdd_normDen_pos u v)
  calc
    chartAddNormDen u v * composedCos u v =
        ((1 + u * u) * (1 + v * v)) * composedCos u v := by
      rw [chartAdd_normDen_eq]
    _ = chartAddCosNum u v :=
      composedCos_chartAdd_denominator_cleared u v
    _ = chartAddNormDen u v * cos (chartAddParameter u v) := by
      rw [cos_chartAdd_denominator_cleared hden]

theorem composedSin_eq_sin_chartAdd {u v : Rat}
    (hden : Ne (chartAddDen u v) 0) :
    composedSin u v = sin (chartAddParameter u v) := by
  apply rat_eq_of_pos_mul_eq_mul
    (c := chartAddNormDen u v) (chartAdd_normDen_pos u v)
  calc
    chartAddNormDen u v * composedSin u v =
        ((1 + u * u) * (1 + v * v)) * composedSin u v := by
      rw [chartAdd_normDen_eq]
    _ = chartAddSinNum u v :=
      composedSin_chartAdd_denominator_cleared u v
    _ = chartAddNormDen u v * sin (chartAddParameter u v) := by
      rw [sin_chartAdd_denominator_cleared hden]

theorem composedPoint_eq_point_chartAdd {u v : Rat}
    (hden : Ne (chartAddDen u v) 0) :
    composedPoint u v = point (chartAddParameter u v) := by
  cases hcp : composedPoint u v
  simp [point_eq] at *
  constructor
  · simpa [composedCos, hcp] using composedCos_eq_cos_chartAdd hden
  · simpa [composedSin, hcp] using composedSin_eq_sin_chartAdd hden

theorem composed_cos_sq_add_sin_sq (u v : Rat) :
    sq (composedCos u v) + sq (composedSin u v) = 1 := by
  simpa [composedCos, composedSin, sq] using composedPoint_normSq u v

theorem double_cos_eq_sq_sub_sq (u : Rat) :
    doubleCos u = sq (cos u) - sq (sin u) := by
  unfold doubleCos doublePoint composedPoint pointMul sq
  rfl

theorem double_sin_eq_two_mul (u : Rat) :
    doubleSin u = 2 * cos u * sin u := by
  unfold doubleSin doublePoint composedPoint pointMul cos sin
  grind [Rat.mul_assoc, Rat.mul_comm]

theorem double_cos_eq_one_sub_two_sin_sq (u : Rat) :
    doubleCos u = 1 - 2 * sq (sin u) := by
  rw [double_cos_eq_sq_sub_sq]
  have hcircle := cos_sq_add_sin_sq u
  unfold sq at *
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.add_assoc,
    Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]

theorem double_cos_eq_two_cos_sq_sub_one (u : Rat) :
    doubleCos u = 2 * sq (cos u) - 1 := by
  rw [double_cos_eq_sq_sub_sq]
  have hcircle := cos_sq_add_sin_sq u
  unfold sq at *
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.add_assoc,
    Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]

theorem cos_zero : cos 0 = 1 := by
  native_decide

theorem sin_zero : sin 0 = 0 := by
  native_decide

theorem cos_one : cos 1 = 0 := by
  native_decide

theorem sin_one : sin 1 = 1 := by
  native_decide

theorem tan_zero :
    tan 0 = ProjectiveRat.finite 0 := by
  native_decide

theorem tan_one :
    tan 1 = ProjectiveRat.infinity := by
  native_decide

theorem tan_finite_of_cos_ne_zero {u : Rat} (hcos : cos u ≠ 0) :
    tan u = ProjectiveRat.finite (finiteTan u) := by
  have hx : (point u).x ≠ 0 := by
    simpa [cos] using hcos
  simpa [tan, finiteTan, sin, cos] using
    projectiveSlope_x_ne_zero (p := point u) hx

theorem sin_ne_zero_or_cos_ne_zero (u : Rat) :
    sin u ≠ 0 ∨ cos u ≠ 0 := by
  by_cases hsin : sin u = 0
  · right
    intro hcos
    have hcircle := cos_sq_add_sin_sq u
    rw [hcos, hsin] at hcircle
    have hzero : (0 : Rat) + 0 = 0 := by native_decide
    simp [sq, hzero] at hcircle
  · exact Or.inl hsin

theorem finiteTan_eq_sin_div_cos (u : Rat) :
    finiteTan u = sin u / cos u := rfl

theorem cot_eq_cos_div_sin (u : Rat) :
    cot u = cos u / sin u := rfl

theorem sec_eq_one_div_cos (u : Rat) :
    sec u = 1 / cos u := rfl

theorem csc_eq_one_div_sin (u : Rat) :
    csc u = 1 / sin u := rfl

theorem finiteTan_mul_cos {u : Rat} (hcos : Ne (cos u) 0) :
    finiteTan u * cos u = sin u := by
  unfold finiteTan
  rw [Rat.div_def]
  grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

theorem cot_mul_sin {u : Rat} (hsin : Ne (sin u) 0) :
    cot u * sin u = cos u := by
  unfold cot
  rw [Rat.div_def]
  grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

theorem sec_mul_cos {u : Rat} (hcos : Ne (cos u) 0) :
    sec u * cos u = 1 := by
  unfold sec
  rw [Rat.div_def]
  grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

theorem csc_mul_sin {u : Rat} (hsin : Ne (sin u) 0) :
    csc u * sin u = 1 := by
  unfold csc
  rw [Rat.div_def]
  grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

theorem cos_mul_sec {u : Rat} (hcos : Ne (cos u) 0) :
    cos u * sec u = 1 := by
  rw [Rat.mul_comm]
  exact sec_mul_cos hcos

theorem sin_mul_csc {u : Rat} (hsin : Ne (sin u) 0) :
    sin u * csc u = 1 := by
  rw [Rat.mul_comm]
  exact csc_mul_sin hsin

theorem finiteTan_eq_sin_mul_sec (u : Rat) :
    finiteTan u = sin u * sec u := by
  unfold finiteTan sec
  rw [Rat.div_def, Rat.div_def]
  grind [Rat.mul_assoc, Rat.mul_comm]

theorem cot_eq_cos_mul_csc (u : Rat) :
    cot u = cos u * csc u := by
  unfold cot csc
  rw [Rat.div_def, Rat.div_def]
  grind [Rat.mul_assoc, Rat.mul_comm]

theorem finiteTan_mul_cot {u : Rat}
    (hcos : Ne (cos u) 0) (hsin : Ne (sin u) 0) :
    finiteTan u * cot u = 1 := by
  unfold finiteTan cot
  rw [Rat.div_def, Rat.div_def]
  grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

theorem one_add_tan_sq_eq_sec_sq {u : Rat} (hcos : Ne (cos u) 0) :
    1 + sq (finiteTan u) = sq (sec u) := by
  unfold finiteTan sec sq
  rw [Rat.div_def, Rat.div_def]
  have hcircle := cos_sq_add_sin_sq u
  unfold sq at hcircle
  grind [Rat.mul_add, Rat.add_mul, Rat.add_assoc, Rat.add_comm,
    Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

theorem sec_sq_sub_tan_sq_eq_one {u : Rat} (hcos : Ne (cos u) 0) :
    sq (sec u) - sq (finiteTan u) = 1 := by
  have h := one_add_tan_sq_eq_sec_sq (u := u) hcos
  grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]

theorem one_add_cot_sq_eq_csc_sq {u : Rat} (hsin : Ne (sin u) 0) :
    1 + sq (cot u) = sq (csc u) := by
  unfold cot csc sq
  rw [Rat.div_def, Rat.div_def]
  have hcircle := cos_sq_add_sin_sq u
  unfold sq at hcircle
  grind [Rat.mul_add, Rat.add_mul, Rat.add_assoc, Rat.add_comm,
    Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

theorem csc_sq_sub_cot_sq_eq_one {u : Rat} (hsin : Ne (sin u) 0) :
    sq (csc u) - sq (cot u) = 1 := by
  have h := one_add_cot_sq_eq_csc_sq (u := u) hsin
  grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]

theorem sin_sq_add_cos_sq (u : Rat) :
    sq (sin u) + sq (cos u) = 1 := by
  have h := cos_sq_add_sin_sq u
  grind [Rat.add_comm]

theorem sin_sq_eq_one_sub_cos_sq (u : Rat) :
    sq (sin u) = 1 - sq (cos u) := by
  have h := cos_sq_add_sin_sq u
  grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]

theorem cos_sq_eq_one_sub_sin_sq (u : Rat) :
    sq (cos u) = 1 - sq (sin u) := by
  have h := cos_sq_add_sin_sq u
  grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]

theorem double_sin_eq_two_sin_mul_cos (u : Rat) :
    doubleSin u = 2 * sin u * cos u := by
  rw [double_sin_eq_two_mul]
  grind [Rat.mul_assoc, Rat.mul_comm]

theorem composedCos_comm (u v : Rat) :
    composedCos u v = composedCos v u := by
  rw [composed_cos_eq, composed_cos_eq]
  grind [Rat.sub_eq_add_neg, Rat.mul_comm]

theorem composedSin_comm (u v : Rat) :
    composedSin u v = composedSin v u := by
  rw [composed_sin_eq, composed_sin_eq]
  grind [Rat.add_comm, Rat.mul_comm]

theorem composedCos_zero_left (u : Rat) :
    composedCos 0 u = cos u := by
  rw [composed_cos_eq, cos_zero, sin_zero]
  grind

theorem composedSin_zero_left (u : Rat) :
    composedSin 0 u = sin u := by
  rw [composed_sin_eq, cos_zero, sin_zero]
  grind

theorem composedCos_zero_right (u : Rat) :
    composedCos u 0 = cos u := by
  rw [composedCos_comm, composedCos_zero_left]

theorem composedSin_zero_right (u : Rat) :
    composedSin u 0 = sin u := by
  rw [composedSin_comm, composedSin_zero_left]

theorem composedCos_one_left (u : Rat) :
    composedCos 1 u = -sin u := by
  rw [composed_cos_eq, cos_one, sin_one]
  grind

theorem composedSin_one_left (u : Rat) :
    composedSin 1 u = cos u := by
  rw [composed_sin_eq, cos_one, sin_one]
  grind

theorem composedCos_one_right (u : Rat) :
    composedCos u 1 = -sin u := by
  rw [composedCos_comm, composedCos_one_left]

theorem composedSin_one_right (u : Rat) :
    composedSin u 1 = cos u := by
  rw [composedSin_comm, composedSin_one_left]

theorem cos_neg (u : Rat) :
    cos (-u) = cos u := by
  unfold cos point Stage.point
  simp
  grind [Rat.neg_mul, Rat.mul_neg, Rat.neg_neg]

theorem sin_neg (u : Rat) :
    sin (-u) = -sin u := by
  unfold sin point Stage.point
  simp
  rw [Rat.div_def, Rat.div_def]
  grind [Rat.neg_mul, Rat.mul_neg, Rat.neg_neg, Rat.mul_assoc, Rat.mul_comm]

theorem finiteTan_neg (u : Rat) :
    finiteTan (-u) = -finiteTan u := by
  unfold finiteTan
  rw [sin_neg, cos_neg]
  rw [Rat.div_def, Rat.div_def]
  grind [Rat.neg_mul, Rat.mul_neg, Rat.mul_assoc, Rat.mul_comm]

theorem tan_neg (u : Rat) :
    tan (-u) = (tan u).neg := by
  unfold tan projectiveSlope
  change ProjectiveRat.ofHom (sin (-u)) (cos (-u)) =
    (ProjectiveRat.ofHom (sin u) (cos u)).neg
  rw [sin_neg, cos_neg]
  exact ProjectiveRat.ofHom_neg_num (sin u) (cos u)

theorem cot_neg (u : Rat) :
    cot (-u) = -cot u := by
  unfold cot
  rw [cos_neg, sin_neg]
  rw [Rat.div_def, Rat.div_def]
  grind [Rat.neg_mul, Rat.mul_neg, Rat.mul_assoc, Rat.mul_comm]

theorem sec_neg (u : Rat) :
    sec (-u) = sec u := by
  unfold sec
  rw [cos_neg]

theorem csc_neg (u : Rat) :
    csc (-u) = -csc u := by
  unfold csc
  rw [sin_neg]
  rw [Rat.div_def, Rat.div_def]
  grind [Rat.neg_mul, Rat.mul_neg, Rat.mul_assoc, Rat.mul_comm]

theorem composed_cos_sub (u v : Rat) :
    composedCos u (-v) = cos u * cos v + sin u * sin v := by
  rw [composed_cos_eq, cos_neg, sin_neg]
  grind [Rat.sub_eq_add_neg, Rat.mul_neg, Rat.neg_mul, Rat.add_assoc,
    Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]

theorem composed_sin_sub (u v : Rat) :
    composedSin u (-v) = sin u * cos v - cos u * sin v := by
  rw [composed_sin_eq, cos_neg, sin_neg]
  grind [Rat.sub_eq_add_neg, Rat.mul_neg, Rat.neg_mul, Rat.add_assoc,
    Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]

theorem composed_cos_neg_left (u v : Rat) :
    composedCos (-u) v = cos u * cos v + sin u * sin v := by
  rw [composed_cos_eq, cos_neg, sin_neg]
  grind [Rat.sub_eq_add_neg, Rat.mul_neg, Rat.neg_mul, Rat.add_assoc,
    Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]

theorem composed_sin_neg_left (u v : Rat) :
    composedSin (-u) v = cos u * sin v - sin u * cos v := by
  rw [composed_sin_eq, cos_neg, sin_neg]
  grind [Rat.sub_eq_add_neg, Rat.mul_neg, Rat.neg_mul, Rat.add_assoc,
    Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]

theorem composedCos_neg_one_left (u : Rat) :
    composedCos (-1) u = sin u := by
  rw [composed_cos_eq, cos_neg, sin_neg, cos_one, sin_one]
  grind [Rat.neg_mul, Rat.mul_neg]

theorem composedSin_neg_one_left (u : Rat) :
    composedSin (-1) u = -cos u := by
  rw [composed_sin_eq, cos_neg, sin_neg, cos_one, sin_one]
  grind [Rat.neg_mul, Rat.mul_neg]

theorem composedCos_neg_one_right (u : Rat) :
    composedCos u (-1) = sin u := by
  rw [composedCos_comm, composedCos_neg_one_left]

theorem composedSin_neg_one_right (u : Rat) :
    composedSin u (-1) = -cos u := by
  rw [composedSin_comm, composedSin_neg_one_left]

theorem composedCos_self_neg (u : Rat) :
    composedCos u (-u) = 1 := by
  rw [composed_cos_eq, cos_neg, sin_neg]
  have hcircle := cos_sq_add_sin_sq u
  unfold sq at hcircle
  grind [Rat.sub_eq_add_neg, Rat.mul_neg, Rat.neg_mul,
    Rat.add_assoc, Rat.add_comm]

theorem composedSin_self_neg (u : Rat) :
    composedSin u (-u) = 0 := by
  rw [composed_sin_eq, cos_neg, sin_neg]
  grind [Rat.mul_neg, Rat.neg_mul, Rat.add_assoc, Rat.add_comm,
    Rat.mul_assoc, Rat.mul_comm]

theorem product_to_sum_cos_cos (u v : Rat) :
    composedCos u v + composedCos u (-v) = 2 * cos u * cos v := by
  rw [composed_cos_sub, composed_cos_eq]
  grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm,
    Rat.mul_assoc, Rat.mul_comm]

theorem product_to_sum_sin_sin (u v : Rat) :
    composedCos u (-v) - composedCos u v = 2 * sin u * sin v := by
  rw [composed_cos_sub, composed_cos_eq]
  grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm,
    Rat.mul_assoc, Rat.mul_comm]

theorem product_to_sum_sin_cos (u v : Rat) :
    composedSin u v + composedSin u (-v) = 2 * sin u * cos v := by
  rw [composed_sin_sub, composed_sin_eq]
  grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm,
    Rat.mul_assoc, Rat.mul_comm]

theorem product_to_sum_cos_sin (u v : Rat) :
    composedSin u v - composedSin u (-v) = 2 * cos u * sin v := by
  rw [composed_sin_sub, composed_sin_eq]
  grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm,
    Rat.mul_assoc, Rat.mul_comm]

theorem finiteTan_add_denominator_cleared {u v : Rat}
    (hcu : Ne (cos u) 0) (hcv : Ne (cos v) 0) :
    (1 - finiteTan u * finiteTan v) * composedSin u v =
      (finiteTan u + finiteTan v) * composedCos u v := by
  rw [composed_sin_eq, composed_cos_eq]
  unfold finiteTan
  rw [Rat.div_def, Rat.div_def]
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.add_assoc,
    Rat.add_comm, Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

theorem finiteTan_sub_denominator_cleared {u v : Rat}
    (hcu : Ne (cos u) 0) (hcv : Ne (cos v) 0) :
    (1 + finiteTan u * finiteTan v) * composedSin u (-v) =
      (finiteTan u - finiteTan v) * composedCos u (-v) := by
  rw [composed_sin_sub, composed_cos_sub]
  unfold finiteTan
  rw [Rat.div_def, Rat.div_def]
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.add_assoc,
    Rat.add_comm, Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

theorem cot_add_denominator_cleared {u v : Rat}
    (hsu : Ne (sin u) 0) (hsv : Ne (sin v) 0) :
    (cot u + cot v) * composedCos u v =
      (cot u * cot v - 1) * composedSin u v := by
  rw [composed_sin_eq, composed_cos_eq]
  unfold cot
  rw [Rat.div_def, Rat.div_def]
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.add_assoc,
    Rat.add_comm, Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

theorem cot_sub_denominator_cleared {u v : Rat}
    (hsu : Ne (sin u) 0) (hsv : Ne (sin v) 0) :
    (cot v - cot u) * composedCos u (-v) =
      (cot u * cot v + 1) * composedSin u (-v) := by
  rw [composed_sin_sub, composed_cos_sub]
  unfold cot
  rw [Rat.div_def, Rat.div_def]
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.add_assoc,
    Rat.add_comm, Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

theorem finiteTan_double_denominator_cleared {u : Rat}
    (hcu : Ne (cos u) 0) :
    (1 - sq (finiteTan u)) * doubleSin u =
      (2 * finiteTan u) * doubleCos u := by
  rw [double_sin_eq_two_mul, double_cos_eq_sq_sub_sq]
  unfold finiteTan sq
  rw [Rat.div_def]
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.add_assoc,
    Rat.add_comm, Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

theorem one_add_ne_zero_of_nonneg {u : Rat} (hu : 0 <= u) :
    Ne (1 + u) 0 := by
  grind

theorem one_add_pos_of_nonneg {u : Rat} (hu : 0 <= u) :
    0 < 1 + u := by
  grind

theorem quarterComplementParameter_zero :
    quarterComplementParameter 0 = 1 := by
  native_decide

theorem quarterComplementParameter_one :
    quarterComplementParameter 1 = 0 := by
  native_decide

theorem cos_quarterComplementParameter {u : Rat}
    (hu : Ne (1 + u) 0) :
    cos (quarterComplementParameter u) = sin u := by
  simp [quarterComplementParameter, cos, sin, point, Stage.point, Rat.div_def]
  grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_add, Rat.add_mul,
    Rat.sub_eq_add_neg, Rat.mul_inv_cancel]

theorem sin_quarterComplementParameter {u : Rat}
    (hu : Ne (1 + u) 0) :
    sin (quarterComplementParameter u) = cos u := by
  simp [quarterComplementParameter, cos, sin, point, Stage.point, Rat.div_def]
  grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_add, Rat.add_mul,
    Rat.sub_eq_add_neg, Rat.mul_inv_cancel]

theorem finiteTan_quarterComplementParameter {u : Rat}
    (hu : Ne (1 + u) 0) :
    finiteTan (quarterComplementParameter u) = cot u := by
  unfold finiteTan cot
  rw [sin_quarterComplementParameter hu, cos_quarterComplementParameter hu]

theorem cot_quarterComplementParameter {u : Rat}
    (hu : Ne (1 + u) 0) :
    cot (quarterComplementParameter u) = finiteTan u := by
  unfold finiteTan cot
  rw [sin_quarterComplementParameter hu, cos_quarterComplementParameter hu]

theorem sec_quarterComplementParameter {u : Rat}
    (hu : Ne (1 + u) 0) :
    sec (quarterComplementParameter u) = csc u := by
  unfold sec csc
  rw [cos_quarterComplementParameter hu]

theorem csc_quarterComplementParameter {u : Rat}
    (hu : Ne (1 + u) 0) :
    csc (quarterComplementParameter u) = sec u := by
  unfold sec csc
  rw [sin_quarterComplementParameter hu]

theorem tan_quarterComplementParameter {u : Rat}
    (hu : Ne (1 + u) 0) :
    tan (quarterComplementParameter u) = (tan u).inv := by
  unfold tan projectiveSlope
  change
    ProjectiveRat.ofHom
      (sin (quarterComplementParameter u))
      (cos (quarterComplementParameter u)) =
        (ProjectiveRat.ofHom (sin u) (cos u)).inv
  rw [sin_quarterComplementParameter hu, cos_quarterComplementParameter hu]
  exact ProjectiveRat.ofHom_swap_eq_inv (sin_ne_zero_or_cos_ne_zero u)

theorem cos_quarterComplementParameter_of_nonneg {u : Rat}
    (hu : 0 <= u) :
    cos (quarterComplementParameter u) = sin u :=
  cos_quarterComplementParameter (one_add_ne_zero_of_nonneg hu)

theorem sin_quarterComplementParameter_of_nonneg {u : Rat}
    (hu : 0 <= u) :
    sin (quarterComplementParameter u) = cos u :=
  sin_quarterComplementParameter (one_add_ne_zero_of_nonneg hu)

theorem tan_quarterComplementParameter_of_nonneg {u : Rat}
    (hu : 0 <= u) :
    tan (quarterComplementParameter u) = (tan u).inv :=
  tan_quarterComplementParameter (one_add_ne_zero_of_nonneg hu)

theorem cosRaw_valid (u : Rat) :
    (cosRaw u).Valid := by
  simpa [cosRaw] using RealRaw.ofRat_valid (cos u)

theorem sinRaw_valid (u : Rat) :
    (sinRaw u).Valid := by
  simpa [sinRaw] using RealRaw.ofRat_valid (sin u)

theorem tanRaw_valid (u : Rat) :
    (tanRaw u).Valid := by
  simpa [tanRaw] using RealRaw.ofRat_valid (finiteTan u)

theorem cotRaw_valid (u : Rat) :
    (cotRaw u).Valid := by
  simpa [cotRaw] using RealRaw.ofRat_valid (cot u)

theorem secRaw_valid (u : Rat) :
    (secRaw u).Valid := by
  simpa [secRaw] using RealRaw.ofRat_valid (sec u)

theorem cscRaw_valid (u : Rat) :
    (cscRaw u).Valid := by
  simpa [cscRaw] using RealRaw.ofRat_valid (csc u)

theorem dyadic_point_refineIndex (n k : Nat) :
    dyadicPoint (n + 1) (Stage.refineIndex k) =
      dyadicPoint n k := by
  unfold dyadicPoint
  exact dyadicStage_samplePoint_refineIndex n k

theorem dyadic_cos_refineIndex (n k : Nat) :
    dyadicCos (n + 1) (Stage.refineIndex k) =
      dyadicCos n k := by
  unfold dyadicCos dyadicPoint
  rw [dyadicStage_samplePoint_refineIndex]

theorem dyadic_sin_refineIndex (n k : Nat) :
    dyadicSin (n + 1) (Stage.refineIndex k) =
      dyadicSin n k := by
  unfold dyadicSin dyadicPoint
  rw [dyadicStage_samplePoint_refineIndex]

theorem dyadic_cos_sq_add_sin_sq (n k : Nat) :
    sq (dyadicCos n k) + sq (dyadicSin n k) = 1 := by
  simpa [dyadicCos, dyadicSin, dyadicPoint, sq] using
    Stage.samplePoint_normSq (dyadicStage n) k

theorem dyadic_cos_zero (n : Nat) :
    dyadicCos n 0 = 1 := by
  rw [dyadicCos, dyadicPoint, Stage.samplePoint_zero]

theorem dyadic_sin_zero (n : Nat) :
    dyadicSin n 0 = 0 := by
  rw [dyadicSin, dyadicPoint, Stage.samplePoint_zero]

theorem dyadic_cos_last (n : Nat) :
    dyadicCos n (dyadicSubdivisions n) = 0 := by
  unfold dyadicCos dyadicPoint
  change ((dyadicStage n).samplePoint (dyadicStage n).subdivisions).x = 0
  rw [Stage.samplePoint_last _ (dyadicStage_positive n)]

theorem dyadic_sin_last (n : Nat) :
    dyadicSin n (dyadicSubdivisions n) = 1 := by
  unfold dyadicSin dyadicPoint
  change ((dyadicStage n).samplePoint (dyadicStage n).subdivisions).y = 1
  rw [Stage.samplePoint_last _ (dyadicStage_positive n)]

/-- A first exact identity package for the rational half-angle trigonometric
functions.  Later angle-based sine and cosine should prove the same package by
equivalence with these rational-circle stages. -/
structure BasicIdentityPackage : Prop where
  circle : forall u : Rat, sq (cos u) + sq (sin u) = 1
  circle_comm : forall u : Rat, sq (sin u) + sq (cos u) = 1
  sin_sq_complement : forall u : Rat, sq (sin u) = 1 - sq (cos u)
  cos_sq_complement : forall u : Rat, sq (cos u) = 1 - sq (sin u)
  tan_cancel : forall u : Rat, Ne (cos u) 0 -> finiteTan u * cos u = sin u
  cot_cancel : forall u : Rat, Ne (sin u) 0 -> cot u * sin u = cos u
  sec_cancel : forall u : Rat, Ne (cos u) 0 -> sec u * cos u = 1
  csc_cancel : forall u : Rat, Ne (sin u) 0 -> csc u * sin u = 1
  cos_sec_cancel : forall u : Rat, Ne (cos u) 0 -> cos u * sec u = 1
  sin_csc_cancel : forall u : Rat, Ne (sin u) 0 -> sin u * csc u = 1
  tan_as_sin_mul_sec : forall u : Rat, finiteTan u = sin u * sec u
  cot_as_cos_mul_csc : forall u : Rat, cot u = cos u * csc u
  tan_cot_cancel :
    forall u : Rat, Ne (cos u) 0 -> Ne (sin u) 0 -> finiteTan u * cot u = 1
  tan_pythagorean :
    forall u : Rat, Ne (cos u) 0 -> 1 + sq (finiteTan u) = sq (sec u)
  cot_pythagorean :
    forall u : Rat, Ne (sin u) 0 -> 1 + sq (cot u) = sq (csc u)
  sec_tan_pythagorean :
    forall u : Rat, Ne (cos u) 0 -> sq (sec u) - sq (finiteTan u) = 1
  csc_cot_pythagorean :
    forall u : Rat, Ne (sin u) 0 -> sq (csc u) - sq (cot u) = 1
  add_cos :
    forall u v : Rat, composedCos u v = cos u * cos v - sin u * sin v
  add_sin :
    forall u v : Rat, composedSin u v = cos u * sin v + sin u * cos v
  chart_add_norm_den :
    forall u v : Rat, chartAddNormDen u v = (1 + u * u) * (1 + v * v)
  chart_add_norm_den_pos :
    forall u v : Rat, 0 < chartAddNormDen u v
  chart_add_cos_num :
    forall u v : Rat,
      chartAddCosNum u v =
        (1 - u * u) * (1 - v * v) - (2 * u) * (2 * v)
  chart_add_sin_num :
    forall u v : Rat,
      chartAddSinNum u v =
        (1 - u * u) * (2 * v) + (2 * u) * (1 - v * v)
  chart_add_cos_denominator_cleared :
    forall u v : Rat,
      ((1 + u * u) * (1 + v * v)) * composedCos u v =
        chartAddCosNum u v
  chart_add_sin_denominator_cleared :
    forall u v : Rat,
      ((1 + u * u) * (1 + v * v)) * composedSin u v =
        chartAddSinNum u v
  chart_add_cos :
    forall u v : Rat, Ne (chartAddDen u v) 0 ->
      composedCos u v = cos (chartAddParameter u v)
  chart_add_sin :
    forall u v : Rat, Ne (chartAddDen u v) 0 ->
      composedSin u v = sin (chartAddParameter u v)
  chart_add_point :
    forall u v : Rat, Ne (chartAddDen u v) 0 ->
      composedPoint u v = point (chartAddParameter u v)
  add_cos_comm : forall u v : Rat, composedCos u v = composedCos v u
  add_sin_comm : forall u v : Rat, composedSin u v = composedSin v u
  add_cos_zero_left : forall u : Rat, composedCos 0 u = cos u
  add_sin_zero_left : forall u : Rat, composedSin 0 u = sin u
  add_cos_zero_right : forall u : Rat, composedCos u 0 = cos u
  add_sin_zero_right : forall u : Rat, composedSin u 0 = sin u
  add_cos_quarter_left : forall u : Rat, composedCos 1 u = -sin u
  add_sin_quarter_left : forall u : Rat, composedSin 1 u = cos u
  add_cos_quarter_right : forall u : Rat, composedCos u 1 = -sin u
  add_sin_quarter_right : forall u : Rat, composedSin u 1 = cos u
  add_cos_neg_quarter_left : forall u : Rat, composedCos (-1) u = sin u
  add_sin_neg_quarter_left : forall u : Rat, composedSin (-1) u = -cos u
  add_cos_neg_quarter_right : forall u : Rat, composedCos u (-1) = sin u
  add_sin_neg_quarter_right : forall u : Rat, composedSin u (-1) = -cos u
  add_cos_self_neg : forall u : Rat, composedCos u (-u) = 1
  add_sin_self_neg : forall u : Rat, composedSin u (-u) = 0
  sub_cos_right :
    forall u v : Rat, composedCos u (-v) = cos u * cos v + sin u * sin v
  sub_sin_right :
    forall u v : Rat, composedSin u (-v) = sin u * cos v - cos u * sin v
  sub_cos_left :
    forall u v : Rat, composedCos (-u) v = cos u * cos v + sin u * sin v
  sub_sin_left :
    forall u v : Rat, composedSin (-u) v = cos u * sin v - sin u * cos v
  product_sum_cos_cos :
    forall u v : Rat,
      composedCos u v + composedCos u (-v) = 2 * cos u * cos v
  product_sum_sin_sin :
    forall u v : Rat,
      composedCos u (-v) - composedCos u v = 2 * sin u * sin v
  product_sum_sin_cos :
    forall u v : Rat,
      composedSin u v + composedSin u (-v) = 2 * sin u * cos v
  product_sum_cos_sin :
    forall u v : Rat,
      composedSin u v - composedSin u (-v) = 2 * cos u * sin v
  tan_add :
    forall u v : Rat, Ne (cos u) 0 -> Ne (cos v) 0 ->
      (1 - finiteTan u * finiteTan v) * composedSin u v =
        (finiteTan u + finiteTan v) * composedCos u v
  tan_sub :
    forall u v : Rat, Ne (cos u) 0 -> Ne (cos v) 0 ->
      (1 + finiteTan u * finiteTan v) * composedSin u (-v) =
        (finiteTan u - finiteTan v) * composedCos u (-v)
  cot_add :
    forall u v : Rat, Ne (sin u) 0 -> Ne (sin v) 0 ->
      (cot u + cot v) * composedCos u v =
        (cot u * cot v - 1) * composedSin u v
  cot_sub :
    forall u v : Rat, Ne (sin u) 0 -> Ne (sin v) 0 ->
      (cot v - cot u) * composedCos u (-v) =
        (cot u * cot v + 1) * composedSin u (-v)
  double_cos :
    forall u : Rat, doubleCos u = sq (cos u) - sq (sin u)
  double_cos_one_sub_two_sin_sq :
    forall u : Rat, doubleCos u = 1 - 2 * sq (sin u)
  double_cos_two_cos_sq_sub_one :
    forall u : Rat, doubleCos u = 2 * sq (cos u) - 1
  double_sin :
    forall u : Rat, doubleSin u = 2 * cos u * sin u
  double_sin_comm :
    forall u : Rat, doubleSin u = 2 * sin u * cos u
  tan_double :
    forall u : Rat, Ne (cos u) 0 ->
      (1 - sq (finiteTan u)) * doubleSin u = (2 * finiteTan u) * doubleCos u
  cos_at_zero : cos 0 = 1
  sin_at_zero : sin 0 = 0
  cos_at_one : cos 1 = 0
  sin_at_one : sin 1 = 1
  projective_tan_at_zero : tan 0 = ProjectiveRat.finite 0
  projective_tan_at_one : tan 1 = ProjectiveRat.infinity
  projective_tan_finite :
    forall u : Rat, Ne (cos u) 0 -> tan u = ProjectiveRat.finite (finiteTan u)
  projective_tan_odd : forall u : Rat, tan (-u) = (tan u).neg
  projective_tan_complement :
    forall u : Rat, Ne (1 + u) 0 ->
      tan (quarterComplementParameter u) = (tan u).inv
  projective_tan_complement_first_quadrant :
    forall u : Rat, 0 <= u ->
      tan (quarterComplementParameter u) = (tan u).inv
  cos_even : forall u : Rat, cos (-u) = cos u
  sin_odd : forall u : Rat, sin (-u) = -sin u
  tan_odd : forall u : Rat, finiteTan (-u) = -finiteTan u
  cot_odd : forall u : Rat, cot (-u) = -cot u
  sec_even : forall u : Rat, sec (-u) = sec u
  csc_odd : forall u : Rat, csc (-u) = -csc u
  complement_zero : quarterComplementParameter 0 = 1
  complement_one : quarterComplementParameter 1 = 0
  complement_cos :
    forall u : Rat, Ne (1 + u) 0 ->
      cos (quarterComplementParameter u) = sin u
  complement_sin :
    forall u : Rat, Ne (1 + u) 0 ->
      sin (quarterComplementParameter u) = cos u
  complement_tan :
    forall u : Rat, Ne (1 + u) 0 ->
      finiteTan (quarterComplementParameter u) = cot u
  complement_cot :
    forall u : Rat, Ne (1 + u) 0 ->
      cot (quarterComplementParameter u) = finiteTan u
  complement_sec :
    forall u : Rat, Ne (1 + u) 0 ->
      sec (quarterComplementParameter u) = csc u
  complement_csc :
    forall u : Rat, Ne (1 + u) 0 ->
      csc (quarterComplementParameter u) = sec u
  complement_cos_first_quadrant :
    forall u : Rat, 0 <= u ->
      cos (quarterComplementParameter u) = sin u
  complement_sin_first_quadrant :
    forall u : Rat, 0 <= u ->
      sin (quarterComplementParameter u) = cos u

theorem basicIdentityPackage : BasicIdentityPackage where
  circle := cos_sq_add_sin_sq
  circle_comm := sin_sq_add_cos_sq
  sin_sq_complement := sin_sq_eq_one_sub_cos_sq
  cos_sq_complement := cos_sq_eq_one_sub_sin_sq
  tan_cancel := fun _ h => finiteTan_mul_cos h
  cot_cancel := fun _ h => cot_mul_sin h
  sec_cancel := fun _ h => sec_mul_cos h
  csc_cancel := fun _ h => csc_mul_sin h
  cos_sec_cancel := fun _ h => cos_mul_sec h
  sin_csc_cancel := fun _ h => sin_mul_csc h
  tan_as_sin_mul_sec := finiteTan_eq_sin_mul_sec
  cot_as_cos_mul_csc := cot_eq_cos_mul_csc
  tan_cot_cancel := fun _ hcos hsin => finiteTan_mul_cot hcos hsin
  tan_pythagorean := fun _ h => one_add_tan_sq_eq_sec_sq h
  cot_pythagorean := fun _ h => one_add_cot_sq_eq_csc_sq h
  sec_tan_pythagorean := fun _ h => sec_sq_sub_tan_sq_eq_one h
  csc_cot_pythagorean := fun _ h => csc_sq_sub_cot_sq_eq_one h
  add_cos := composed_cos_eq
  add_sin := composed_sin_eq
  chart_add_norm_den := chartAdd_normDen_eq
  chart_add_norm_den_pos := chartAdd_normDen_pos
  chart_add_cos_num := chartAdd_cosNum_eq
  chart_add_sin_num := chartAdd_sinNum_eq
  chart_add_cos_denominator_cleared := composedCos_chartAdd_denominator_cleared
  chart_add_sin_denominator_cleared := composedSin_chartAdd_denominator_cleared
  chart_add_cos := fun _ _ h => composedCos_eq_cos_chartAdd h
  chart_add_sin := fun _ _ h => composedSin_eq_sin_chartAdd h
  chart_add_point := fun _ _ h => composedPoint_eq_point_chartAdd h
  add_cos_comm := composedCos_comm
  add_sin_comm := composedSin_comm
  add_cos_zero_left := composedCos_zero_left
  add_sin_zero_left := composedSin_zero_left
  add_cos_zero_right := composedCos_zero_right
  add_sin_zero_right := composedSin_zero_right
  add_cos_quarter_left := composedCos_one_left
  add_sin_quarter_left := composedSin_one_left
  add_cos_quarter_right := composedCos_one_right
  add_sin_quarter_right := composedSin_one_right
  add_cos_neg_quarter_left := composedCos_neg_one_left
  add_sin_neg_quarter_left := composedSin_neg_one_left
  add_cos_neg_quarter_right := composedCos_neg_one_right
  add_sin_neg_quarter_right := composedSin_neg_one_right
  add_cos_self_neg := composedCos_self_neg
  add_sin_self_neg := composedSin_self_neg
  sub_cos_right := composed_cos_sub
  sub_sin_right := composed_sin_sub
  sub_cos_left := composed_cos_neg_left
  sub_sin_left := composed_sin_neg_left
  product_sum_cos_cos := product_to_sum_cos_cos
  product_sum_sin_sin := product_to_sum_sin_sin
  product_sum_sin_cos := product_to_sum_sin_cos
  product_sum_cos_sin := product_to_sum_cos_sin
  tan_add := fun _ _ hcu hcv =>
    finiteTan_add_denominator_cleared hcu hcv
  tan_sub := fun _ _ hcu hcv =>
    finiteTan_sub_denominator_cleared hcu hcv
  cot_add := fun _ _ hsu hsv =>
    cot_add_denominator_cleared hsu hsv
  cot_sub := fun _ _ hsu hsv =>
    cot_sub_denominator_cleared hsu hsv
  double_cos := double_cos_eq_sq_sub_sq
  double_cos_one_sub_two_sin_sq := double_cos_eq_one_sub_two_sin_sq
  double_cos_two_cos_sq_sub_one := double_cos_eq_two_cos_sq_sub_one
  double_sin := double_sin_eq_two_mul
  double_sin_comm := double_sin_eq_two_sin_mul_cos
  tan_double := fun _ hcu =>
    finiteTan_double_denominator_cleared hcu
  cos_at_zero := cos_zero
  sin_at_zero := sin_zero
  cos_at_one := cos_one
  sin_at_one := sin_one
  projective_tan_at_zero := tan_zero
  projective_tan_at_one := tan_one
  projective_tan_finite := fun _ h => tan_finite_of_cos_ne_zero h
  projective_tan_odd := tan_neg
  projective_tan_complement := fun _ h => tan_quarterComplementParameter h
  projective_tan_complement_first_quadrant := fun _ h =>
    tan_quarterComplementParameter_of_nonneg h
  cos_even := cos_neg
  sin_odd := sin_neg
  tan_odd := finiteTan_neg
  cot_odd := cot_neg
  sec_even := sec_neg
  csc_odd := csc_neg
  complement_zero := quarterComplementParameter_zero
  complement_one := quarterComplementParameter_one
  complement_cos := fun _ h => cos_quarterComplementParameter h
  complement_sin := fun _ h => sin_quarterComplementParameter h
  complement_tan := fun _ h => finiteTan_quarterComplementParameter h
  complement_cot := fun _ h => cot_quarterComplementParameter h
  complement_sec := fun _ h => sec_quarterComplementParameter h
  complement_csc := fun _ h => csc_quarterComplementParameter h
  complement_cos_first_quadrant := fun _ h =>
    cos_quarterComplementParameter_of_nonneg h
  complement_sin_first_quadrant := fun _ h =>
    sin_quarterComplementParameter_of_nonneg h

end Trigonometry

namespace GeometricTrig

/-!
Algorithmic target for geometric sine and cosine.

Angles in this namespace are normalized quarter-turns: the rational input `t`
denotes the geometric angle `t * (pi / 2)`.  Thus `0` is the positive real axis
and `1` is ninety degrees.  This keeps function inputs rational while avoiding
an external radian input.

The geometric construction should first build a circle-point algorithm.  It is
encoded as a complex-valued raw function: for a normalized quarter-turn input,
the output box encloses the point `x + i y` on the oriented unit circle.  The
trigonometric algorithms are then just the coordinate projections.
-/

/-- Rational input interpreted as the angle `t * (pi / 2)`, so `1` is a
quarter turn. -/
abbrev QuarterTurn := Rat

/-- The raw real angle represented by a normalized quarter-turn input, using
the current geometric-area `pi` algorithm. -/
def quarterTurnRaw (t : QuarterTurn) : RealRaw :=
  RealRaw.scaleRat (t / 2) piCircleArea

/-- Principal branch for the inverse-arctangent search, measured in normalized
quarter-turns.  This is the interval `[0, 1]`, corresponding to
`[0, pi / 2]`. -/
def unitIntervalBranch (t : QuarterTurn) : Prop :=
  0 <= t /\ t <= 1

theorem unitIntervalBranch_zero : unitIntervalBranch 0 := by
  unfold unitIntervalBranch
  constructor <;> native_decide

theorem unitIntervalBranch_one : unitIntervalBranch 1 := by
  unfold unitIntervalBranch
  constructor <;> native_decide

theorem unitIntervalBranch_half :
    unitIntervalBranch ((1 : Rat) / 2) := by
  unfold unitIntervalBranch
  constructor <;> native_decide

/-- Stable interface for the monotone inverse-arctangent step.

A concrete implementation may use bisection, interval Newton steps, or a more
specialized rational search.  The downstream trigonometric construction only
needs this contract: a raw tangent/slope algorithm on normalized rational
quarter-turns, its validity on the principal branch, inverse laws relating it
to the chosen arctangent representative, and compatibility with the selected
`pi` algorithm. -/
structure ArctanInverseConstruction where
  tangentRaw : PartialRealFunRaw
  branch_spec : forall t : QuarterTurn, tangentRaw.definedAt t -> unitIntervalBranch t
  tangent_valid : forall t ht, RealRaw.ValidCompute (tangentRaw.compute t ht)
  left_inverse_law : Prop
  right_inverse_law : Prop
  pi_compatibility : Prop

namespace ArctanInverseConstruction

theorem tangentRaw_valid (C : ArctanInverseConstruction) :
    forall q hq, RealRaw.ValidCompute (C.tangentRaw.compute q hq) :=
  C.tangent_valid

theorem branch (C : ArctanInverseConstruction)
    (t : QuarterTurn) (ht : C.tangentRaw.definedAt t) :
    unitIntervalBranch t :=
  C.branch_spec t ht

theorem branch_nonneg (C : ArctanInverseConstruction)
    (t : QuarterTurn) (ht : C.tangentRaw.definedAt t) :
    0 <= t :=
  (C.branch t ht).1

theorem branch_le_one (C : ArctanInverseConstruction)
    (t : QuarterTurn) (ht : C.tangentRaw.definedAt t) :
    t <= 1 :=
  (C.branch t ht).2

end ArctanInverseConstruction

def realAxisDomain (pointRaw : FunctionRaw) : QuarterTurn -> Prop :=
  fun theta => pointRaw.domain (QComplex.ofRat theta)

def pointAt (pointRaw : FunctionRaw)
    (theta : Rat) (htheta : realAxisDomain pointRaw theta) : ComplexRaw :=
  pointRaw.evalRaw (QComplex.ofRat theta) htheta

def cosFunctionRawOfPoint (pointRaw : FunctionRaw) : PartialRealFunRaw where
  definedAt := realAxisDomain pointRaw
  compute := fun theta htheta n =>
    let B := pointRaw.compute (QComplex.ofRat theta) htheta n
    { lo := B.lo.re, hi := B.hi.re }

def sinFunctionRawOfPoint (pointRaw : FunctionRaw) : PartialRealFunRaw where
  definedAt := realAxisDomain pointRaw
  compute := fun theta htheta n =>
    let B := pointRaw.compute (QComplex.ofRat theta) htheta n
    { lo := B.lo.im, hi := B.hi.im }

theorem cosFunctionRawOfPoint_compute_eq
    (pointRaw : FunctionRaw) (theta : Rat)
    (htheta : (cosFunctionRawOfPoint pointRaw).definedAt theta) (n : Nat) :
    (cosFunctionRawOfPoint pointRaw).compute theta htheta n =
      { lo := (pointRaw.compute (QComplex.ofRat theta) htheta n).lo.re,
        hi := (pointRaw.compute (QComplex.ofRat theta) htheta n).hi.re } := by
  rfl

theorem sinFunctionRawOfPoint_compute_eq
    (pointRaw : FunctionRaw) (theta : Rat)
    (htheta : (sinFunctionRawOfPoint pointRaw).definedAt theta) (n : Nat) :
    (sinFunctionRawOfPoint pointRaw).compute theta htheta n =
      { lo := (pointRaw.compute (QComplex.ofRat theta) htheta n).lo.im,
        hi := (pointRaw.compute (QComplex.ofRat theta) htheta n).hi.im } := by
  rfl

/-- The theorem-facing package for the chapter: construct the geometric point
algorithm first, then obtain the sine and cosine algorithms by projection and
prove the identities for those projected algorithms. -/
structure FunctionRawConstruction where
  pointRaw : FunctionRaw
  point_valid_on_real_axis :
    forall theta htheta, ComplexRaw.Valid (pointAt pointRaw theta htheta)
  cos_valid :
    forall theta htheta,
      RealRaw.ValidCompute ((cosFunctionRawOfPoint pointRaw).compute theta htheta)
  sin_valid :
    forall theta htheta,
      RealRaw.ValidCompute ((sinFunctionRawOfPoint pointRaw).compute theta htheta)
  unit_circle_law : Prop
  identity_package : Prop

namespace FunctionRawConstruction

def cosFunctionRaw (C : FunctionRawConstruction) : PartialRealFunRaw :=
  cosFunctionRawOfPoint C.pointRaw

def sinFunctionRaw (C : FunctionRawConstruction) : PartialRealFunRaw :=
  sinFunctionRawOfPoint C.pointRaw

theorem cosFunctionRaw_valid (C : FunctionRawConstruction) :
    forall theta htheta,
      RealRaw.ValidCompute (C.cosFunctionRaw.compute theta htheta) :=
  C.cos_valid

theorem sinFunctionRaw_valid (C : FunctionRawConstruction) :
    forall theta htheta,
      RealRaw.ValidCompute (C.sinFunctionRaw.compute theta htheta) :=
  C.sin_valid

end FunctionRawConstruction

end GeometricTrig

end RationalCircle

end ComputableAnalysis
