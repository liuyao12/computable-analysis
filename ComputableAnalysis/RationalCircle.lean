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

/-- The rational point obtained by projecting from `(-1, 0)` through `(0, t)`.

The chart coordinate `t` is a height on the vertical radius, equivalently the
slope of that projection line; it is not an angle. -/
def point (t : Rat) : PiCirclePoint :=
  let d := 1 + t * t
  { x := (1 - t * t) / d,
    y := (2 * t) / d }

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

/-- A chart parameter stays in the first-quadrant interval whenever its
finite index has not passed the last subdivision. -/
theorem parameter_le_one (S : Stage)
    (hS : 0 < S.subdivisions) {k : Nat} (hk : k <= S.subdivisions) :
    S.parameter k <= 1 := by
  calc
    S.parameter k <= S.parameter S.subdivisions :=
      parameter_mono S hS hk
    _ = 1 := parameter_last S hS

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
`t ↦ ((1-t^2)/(1+t^2), 2t/(1+t^2))`.  This is an exact rational function,
not a limiting construction. -/
def pointDerivative (t : Rat) : PiCirclePoint :=
  let d := 1 + t * t
  { x := (-4 * t) / (d * d),
    y := (2 * (1 - t * t)) / (d * d) }

/-- The signed area speed of the parametrized unit-circle sector at `t`. -/
def sectorAreaSpeed (t : Rat) : Rat :=
  cross (point t) (pointDerivative t)

/-- The unit-sector area density at `t`: half of the signed area speed. -/
def sectorAreaDensity (t : Rat) : Rat :=
  sectorAreaSpeed t / 2

theorem sectorAreaSpeed_eq_two_over_one_plus_square (t : Rat) :
    sectorAreaSpeed t = 2 / (1 + t * t) := by
  unfold sectorAreaSpeed pointDerivative cross point
  simp
  rw [Rat.div_def, Rat.div_def, Rat.div_def, Rat.div_def]
  have hdpos : 0 < 1 + t * t := one_add_square_pos t
  have hdne : 1 + t * t ≠ 0 := Rat.ne_of_gt hdpos
  have htwo : (2 : Rat) ≠ 0 := by native_decide
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.add_assoc,
    Rat.add_comm, Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

theorem sectorAreaDensity_eq_one_over_one_plus_square (t : Rat) :
    sectorAreaDensity t = 1 / (1 + t * t) := by
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

/-- A denominator-cleared dot-product formula for the rational circle chart.
It makes the first-quadrant sign conditions used by chord refinements purely
rational inequalities on the chart parameters. -/
theorem point_dot_formula (u v : Rat) :
    dot (point u) (point v) =
      ((1 + u * v) * (1 + u * v) - (v - u) * (v - u)) /
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
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.add_assoc,
    Rat.add_comm, Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

/-- Adjacent nonnegative chart parameters at rational distance at most one
have nonnegative dot product. -/
theorem point_dot_nonneg_of_step_le_one
    {u v : Rat}
    (hu : 0 <= u) (hv : 0 <= v)
    (hstep : 0 <= v - u) (hstep_one : v - u <= 1) :
    0 <= dot (point u) (point v) := by
  rw [point_dot_formula]
  let a : Rat := 1 + u * v
  let d : Rat := v - u
  have huv : 0 <= u * v := Rat.mul_nonneg hu hv
  have haone : 1 <= a := by
    dsimp [a]
    grind
  have ha0 : 0 <= a := Rat.le_trans (by native_decide) haone
  have hd0 : 0 <= d := by
    simpa [d] using hstep
  have hdle : d <= a := Rat.le_trans hstep_one haone
  have hsq : sq d <= sq a := sq_le_sq_of_nonneg_le hd0 hdle
  have hnum : 0 <= a * a - d * d := by
    change 0 <= sq a - sq d
    grind [Rat.sub_eq_add_neg]
  have hden : 0 < (1 + u * u) * (1 + v * v) :=
    Rat.mul_pos (one_add_square_pos u) (one_add_square_pos v)
  rw [Rat.div_def]
  exact Rat.mul_nonneg hnum (Rat.le_of_lt ((Rat.inv_pos).2 hden))

/-- Pythagoras for two rational points on the unit circle, expressed through
their oriented cross product and dot-product deficit.  This finite identity is
the exact algebraic core behind rational chord-length refinements. -/
theorem segmentNormSq_eq_cross_sq_add_dot_deficit_sq_of_unit
    {p q : PiCirclePoint}
    (hp : normSq p = 1) (_hq : normSq q = 1) :
    segmentNormSq p q = sq (cross p q) + sq (1 - dot p q) := by
  unfold segmentNormSq normSq cross dot sq at *
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.add_assoc,
    Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]

/-- A rational lower certificate for the length of an oriented unit-circle
chord.  The denominator is positive for a nondegenerate positively oriented
chord, and the correction has the natural cubic scale near a short chord.
It is deliberately a rational expression: no exact square root is selected. -/
def secantChordLower (p q : PiCirclePoint) : Rat :=
  let c := cross p q
  let d := 1 - dot p q
  c + sq d / (2 * c + d)

/-- The rational secant certificate is nonnegative on an oriented
nondegenerate unit-circle chord. -/
theorem secantChordLower_nonneg
    {p q : PiCirclePoint}
    (hcross : 0 < cross p q) (hdeficit : 0 <= 1 - dot p q) :
    0 <= secantChordLower p q := by
  let c := cross p q
  let d := 1 - dot p q
  have hc : 0 <= c := Rat.le_of_lt hcross
  have hden : 0 < 2 * c + d := by
    have htwo : 0 < (2 : Rat) := by native_decide
    have htwoc : 0 < 2 * c := Rat.mul_pos htwo hcross
    grind
  have hinv : 0 <= (2 * c + d)⁻¹ :=
    Rat.le_of_lt ((Rat.inv_pos).2 hden)
  dsimp [secantChordLower, c, d]
  rw [Rat.div_def]
  exact Rat.add_nonneg hc (Rat.mul_nonneg (rat_sq_nonneg _) hinv)

/-- On a unit-circle chord, the secant certificate lies below the chord
length in the squared rational sense.  The exact remainder is
`2*c*d^3/(2*c+d)^2`, hence nonnegative from the orientation and dot-deficit
facts alone. -/
theorem secantChordLower_sq_le_segmentNormSq_of_unit
    {p q : PiCirclePoint}
    (hp : normSq p = 1) (hq : normSq q = 1)
    (hcross : 0 < cross p q) (hdeficit : 0 <= 1 - dot p q) :
    sq (secantChordLower p q) <= segmentNormSq p q := by
  let c := cross p q
  let d := 1 - dot p q
  let r := c + sq d / (2 * c + d)
  have hc : 0 <= c := Rat.le_of_lt hcross
  have hden : 0 < 2 * c + d := by
    have htwo : 0 < (2 : Rat) := by native_decide
    have htwoc : 0 < 2 * c := Rat.mul_pos htwo hcross
    grind
  have hden_ne : 2 * c + d ≠ 0 := Rat.ne_of_gt hden
  have hrem :
      sq c + sq d - sq r =
        (2 * c * d * d * d) / sq (2 * c + d) := by
    dsimp [r]
    unfold sq
    rw [Rat.div_def, Rat.div_def, Rat.inv_mul_rev]
    have hcancel : (2 * c + d) * (2 * c + d)⁻¹ = 1 :=
      Rat.mul_inv_cancel _ hden_ne
    grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.add_assoc,
      Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
  have hrem_nonneg : 0 <= (2 * c * d * d * d) / sq (2 * c + d) := by
    have htwoc : 0 <= 2 * c :=
      Rat.mul_nonneg (by native_decide) hc
    have hnum : 0 <= 2 * c * d * d * d := by
      exact Rat.mul_nonneg
        (Rat.mul_nonneg (Rat.mul_nonneg htwoc hdeficit) hdeficit) hdeficit
    have hden_sq : 0 < sq (2 * c + d) := by
      unfold sq
      exact Rat.mul_pos hden hden
    rw [Rat.div_def]
    exact Rat.mul_nonneg hnum (Rat.le_of_lt ((Rat.inv_pos).2 hden_sq))
  have hsum : sq r <= sq c + sq d := by
    have hdiff : 0 <= sq c + sq d - sq r := by
      rw [hrem]
      exact hrem_nonneg
    grind [Rat.sub_eq_add_neg]
  have hunit := segmentNormSq_eq_cross_sq_add_dot_deficit_sq_of_unit hp hq
  dsimp [secantChordLower, c, d, r] at hsum ⊢
  rw [hunit]
  exact hsum

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

/-- The positive polynomial core of midpoint curvature refinement.

For a rational chart cell `[u, u + h]` in the first quadrant, this is the
denominator-cleared inequality which says that the two midpoint curvature
corrections pay for the defect between the coarse chord and the two rational
cross-product cells.  It is purely ordered-field arithmetic; no square root,
limit, or completeness principle is involved. -/
theorem midpointCurvaturePolynomialBound
    {u h : Rat} (hu : 0 <= u) (hh : 0 <= h) (huend : u + h <= 1) :
    let m := u + h / 2
    let d0 := 1 + u * u
    let dm := 1 + m * m
    let dv := 1 + (u + h) * (u + h)
    let K := (1 + u * m) * dv + (1 + m * (u + h)) * d0
    8 * h * m * m * d0 * dm * dv <= K * (d0 * d0 + dv * dv) := by
  let m : Rat := u + h / 2
  let d0 : Rat := 1 + u * u
  let dm : Rat := 1 + m * m
  let dv : Rat := 1 + (u + h) * (u + h)
  let K : Rat := (1 + u * m) * dv + (1 + m * (u + h)) * d0
  change 8 * h * m * m * d0 * dm * dv <= K * (d0 * d0 + dv * dv)
  have hhhalf : h / 2 <= h := by
    have hinv : (2 : Rat)⁻¹ <= 1 := by native_decide
    simpa [Rat.div_def, Rat.mul_comm] using
      Rat.mul_le_mul_of_nonneg_left hinv hh
  have hh_le_one : h <= 1 := by
    grind
  have hhhalf_nonneg : 0 <= h / 2 := by
    rw [Rat.div_def]
    exact Rat.mul_nonneg hh (by native_decide)
  have hu_le_one : u <= 1 := by
    grind
  have hm0 : 0 <= m := by
    dsimp [m]
    exact Rat.add_nonneg hu hhhalf_nonneg
  have hmle : m <= 1 := by
    dsimp [m]
    have hsum : u + h / 2 <= u + h := (Rat.add_le_add_left).2 hhhalf
    exact Rat.le_trans hsum huend
  have ha0 : 0 <= 1 - h / 2 := by
    have hhalf : h / 2 <= 1 := Rat.le_trans hhhalf hh_le_one
    grind [Rat.sub_eq_add_neg]
  have hmle_a : m <= 1 - h / 2 := by
    dsimp [m]
    grind [Rat.sub_eq_add_neg]
  have hmsq_le : m * m <= (1 - h / 2) * (1 - h / 2) := by
    have hleft : m * m <= (1 - h / 2) * m :=
      Rat.mul_le_mul_of_nonneg_right hmle_a hm0
    have hright : (1 - h / 2) * m <=
        (1 - h / 2) * (1 - h / 2) :=
      Rat.mul_le_mul_of_nonneg_left hmle_a ha0
    exact Rat.le_trans hleft hright
  have ha_le_one : 1 - h / 2 <= 1 := by
    grind [Rat.sub_eq_add_neg]
  have ha_sq_le : (1 - h / 2) * (1 - h / 2) <= 1 - h / 2 := by
    have hmul := Rat.mul_le_mul_of_nonneg_left ha_le_one ha0
    simpa [Rat.mul_comm] using hmul
  have hhm_sq : h * m * m <= (1 : Rat) / 2 := by
    have hscaled := Rat.mul_le_mul_of_nonneg_left
      (Rat.le_trans hmsq_le ha_sq_le) hh
    have hquad : h * (1 - h / 2) <= (1 : Rat) / 2 := by
      have hsquare := ratSquare_nonneg (h - 1)
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_assoc, Rat.add_comm,
        Rat.mul_assoc, Rat.mul_comm]
    calc
      h * m * m = h * (m * m) := by grind [Rat.mul_assoc]
      _ <= h * (1 - h / 2) := hscaled
      _ <= (1 : Rat) / 2 := hquad
  have hdm_ge : 2 * h * m * m <= dm := by
    dsimp [dm]
    have hdouble : 2 * (h * m * m) <= 1 := by
      have hmul := Rat.mul_le_mul_of_nonneg_left hhm_sq
        (by native_decide : (0 : Rat) <= 2)
      calc
        2 * (h * m * m) <= 2 * ((1 : Rat) / 2) := by
          simpa [Rat.mul_assoc] using hmul
        _ = 1 := by native_decide
    have hm_sq_nonneg : 0 <= m * m := ratSquare_nonneg m
    calc
      2 * h * m * m = 2 * (h * m * m) := by
        grind [Rat.mul_assoc]
      _ <= 1 := hdouble
      _ <= 1 + m * m := by grind
      _ = dm := by rfl
  have hd0_pos : 0 < d0 := by
    dsimp [d0]
    exact one_add_square_pos u
  have hdm_pos : 0 < dm := by
    dsimp [dm]
    exact one_add_square_pos m
  have hdv_pos : 0 < dv := by
    dsimp [dv]
    exact one_add_square_pos (u + h)
  have hd0_nonneg : 0 <= d0 := Rat.le_of_lt hd0_pos
  have hdm_nonneg : 0 <= dm := Rat.le_of_lt hdm_pos
  have hdv_nonneg : 0 <= dv := Rat.le_of_lt hdv_pos
  have hfactor0 : 0 <= 2 - h - 2 * u := by
    have hfirst : 0 <= 1 - u - h := by
      grind [Rat.sub_eq_add_neg]
    have hsecond : 0 <= 1 - u := by
      grind [Rat.sub_eq_add_neg]
    grind [Rat.sub_eq_add_neg]
  have hfactor1 : 0 <= h + 2 * u + 2 := by
    grind
  have hK_ge : 2 * dm * dm <= K := by
    have hsq : 0 <= h * h := ratSquare_nonneg h
    have hterm : 0 <= h * h * (2 - h - 2 * u) * (h + 2 * u + 2) / 8 := by
      rw [Rat.div_def]
      exact Rat.mul_nonneg
        (Rat.mul_nonneg (Rat.mul_nonneg hsq hfactor0) hfactor1)
        (by native_decide)
    have hformula :
        K - 2 * dm * dm =
          h * h * (2 - h - 2 * u) * (h + 2 * u + 2) / 8 := by
      dsimp [K, d0, dm, dv, m]
      rw [Rat.div_def]
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.add_assoc,
        Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
    have hdiff : 0 <= K - 2 * dm * dm := by
      rw [hformula]
      exact hterm
    grind [Rat.sub_eq_add_neg]
  have hsum_ge : 2 * d0 * dv <= d0 * d0 + dv * dv := by
    have hsquare := ratSquare_nonneg (dv - d0)
    grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_assoc, Rat.add_comm,
      Rat.mul_assoc, Rat.mul_comm]
  have hsum_nonneg : 0 <= d0 * d0 + dv * dv := by
    exact Rat.add_nonneg
      (Rat.mul_nonneg hd0_nonneg hd0_nonneg)
      (Rat.mul_nonneg hdv_nonneg hdv_nonneg)
  have htwo_dm_sq_nonneg : 0 <= 2 * dm * dm := by
    exact Rat.mul_nonneg
      (Rat.mul_nonneg (by native_decide) hdm_nonneg) hdm_nonneg
  have hproduct_ge : 4 * dm * dm * d0 * dv <= K * (d0 * d0 + dv * dv) := by
    have hright : (2 * dm * dm) * (2 * d0 * dv) <=
        (2 * dm * dm) * (d0 * d0 + dv * dv) :=
      Rat.mul_le_mul_of_nonneg_left hsum_ge htwo_dm_sq_nonneg
    have hleft : (2 * dm * dm) * (d0 * d0 + dv * dv) <=
        K * (d0 * d0 + dv * dv) :=
      Rat.mul_le_mul_of_nonneg_right hK_ge hsum_nonneg
    calc
      4 * dm * dm * d0 * dv = (2 * dm * dm) * (2 * d0 * dv) := by
        grind [Rat.mul_assoc, Rat.mul_comm]
      _ <= (2 * dm * dm) * (d0 * d0 + dv * dv) := hright
      _ <= K * (d0 * d0 + dv * dv) := hleft
  have hscale_nonneg : 0 <= 4 * d0 * dm * dv := by
    exact Rat.mul_nonneg
      (Rat.mul_nonneg
        (Rat.mul_nonneg (by native_decide) hd0_nonneg) hdm_nonneg)
      hdv_nonneg
  have hscaled := Rat.mul_le_mul_of_nonneg_right hdm_ge hscale_nonneg
  calc
    8 * h * m * m * d0 * dm * dv =
        (2 * h * m * m) * (4 * d0 * dm * dv) := by
      grind [Rat.mul_assoc, Rat.mul_comm]
    _ <= dm * (4 * d0 * dm * dv) := hscaled
    _ = 4 * dm * dm * d0 * dv := by
      grind [Rat.mul_assoc, Rat.mul_comm]
    _ <= K * (d0 * d0 + dv * dv) := hproduct_ge

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

theorem tanSub_finite_finite (x y : Rat) :
    tanSub (finite x) (finite y) = ofHom (x - y) (1 + x * y) := by
  unfold tanSub
  rw [neg_finite, tanAdd_finite_finite]
  have hnum : x + -y = x - y := by grind [Rat.sub_eq_add_neg]
  have hden : 1 - x * (-y) = 1 + x * y := by
    grind [Rat.mul_neg, Rat.neg_mul, Rat.sub_eq_add_neg]
  rw [hnum, hden]

theorem tanSub_finite_infinity (x : Rat) :
    tanSub (finite x) infinity = ofHom 1 (-x) := by
  unfold tanSub
  rw [neg_infinity, tanAdd_finite_infinity]

theorem tanSub_infinity_finite (x : Rat) :
    tanSub infinity (finite x) = ofHom 1 x := by
  unfold tanSub
  rw [neg_finite, tanAdd_infinity_finite]
  have hneg : -(-x) = x := by grind
  rw [hneg]

theorem tanSub_infinity_infinity :
    tanSub infinity infinity = finite 0 := by
  unfold tanSub
  rw [neg_infinity, tanAdd_infinity_infinity]

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

theorem num_den_nonzero (x : ProjectiveRat) :
    x.num ≠ 0 ∨ x.den ≠ 0 := by
  cases x with
  | finite q =>
      right
      simp [den]
  | infinity =>
      left
      simp [num]

theorem ofHom_num_den (x : ProjectiveRat) :
    ofHom x.num x.den = x := by
  cases x with
  | finite q =>
      have hden : (finite q).den ≠ 0 := by
        simp [den]
      rw [ofHom_den_ne_zero hden]
      unfold num den
      rw [Rat.div_def]
      grind
  | infinity =>
      rw [ofHom_den_zero]
      rfl

theorem neg_neg (x : ProjectiveRat) :
    x.neg.neg = x := by
  cases x <;> simp [neg]

theorem inv_inv (x : ProjectiveRat) :
    x.inv.inv = x := by
  cases x with
  | finite q =>
      unfold inv
      by_cases hq : q = 0
      · simp [hq]
      · simp [hq]
        rw [Rat.div_def]
        grind [Rat.mul_inv_cancel]
  | infinity => rfl

theorem tanAdd_zero_left (x : ProjectiveRat) :
    tanAdd (finite 0) x = x := by
  cases x with
  | finite q =>
      rw [tanAdd_finite_finite]
      have hden : (1 : Rat) - 0 * q ≠ 0 := by grind
      rw [ofHom_den_ne_zero hden]
      grind [Rat.sub_eq_add_neg]
  | infinity =>
      rw [tanAdd_finite_infinity]
      native_decide

theorem tanAdd_zero_right (x : ProjectiveRat) :
    tanAdd x (finite 0) = x := by
  cases x with
  | finite q =>
      rw [tanAdd_finite_finite]
      have hden : (1 : Rat) - q * 0 ≠ 0 := by grind
      rw [ofHom_den_ne_zero hden]
      grind [Rat.sub_eq_add_neg]
  | infinity =>
      rw [tanAdd_infinity_finite]
      native_decide

theorem tanAdd_comm (x y : ProjectiveRat) :
    tanAdd x y = tanAdd y x := by
  cases x <;> cases y
  · rename_i q r
    rw [tanAdd_finite_finite, tanAdd_finite_finite]
    have hnum : q + r = r + q := by grind
    have hden : 1 - q * r = 1 - r * q := by grind [Rat.mul_comm]
    rw [hnum, hden]
  · rename_i q
    exact (tanAdd_finite_infinity q).trans
      (Eq.symm (tanAdd_infinity_finite q))
  · rename_i q
    exact (tanAdd_infinity_finite q).trans
      (Eq.symm (tanAdd_finite_infinity q))
  · rfl

theorem tanAdd_neg_self (x : ProjectiveRat) :
    tanAdd x x.neg = finite 0 := by
  cases x with
  | finite q =>
      rw [neg_finite, tanAdd_finite_finite]
      have hden : (1 : Rat) - q * (-q) ≠ 0 := by
        have hpos : 0 < 1 + q * q := Stage.one_add_square_pos q
        grind [Rat.sub_eq_add_neg]
      rw [ofHom_den_ne_zero hden]
      grind [Rat.sub_eq_add_neg]
  | infinity =>
      rw [neg_infinity, tanAdd_infinity_infinity]

theorem tanSub_self (x : ProjectiveRat) :
    tanSub x x = finite 0 := by
  unfold tanSub
  exact tanAdd_neg_self x

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

theorem ofHom_one_neg_den (q : Rat) :
    ofHom 1 q = (ofHom 1 (-q)).neg := by
  have hleft : ofHom 1 q = ofHom (-1) (-q) := by
    unfold ofHom
    by_cases hq : q = 0
    · simp [hq]
    · have hnq : -q ≠ 0 := by grind
      simp [hq, hnq]
      rw [Rat.div_def, Rat.div_def]
      grind [Rat.neg_mul, Rat.mul_neg, Rat.mul_assoc, Rat.mul_comm]
  rw [hleft]
  exact ofHom_neg_num 1 (-q)

theorem inv_neg (x : ProjectiveRat) :
    x.neg.inv = x.inv.neg := by
  cases x with
  | finite q =>
      by_cases hq : q = 0
      · simp [neg_finite, inv_zero, hq, neg_infinity]
      · have hnq : -q ≠ 0 := by grind
        rw [neg_finite, inv_finite_ne_zero hnq,
          inv_finite_ne_zero hq, neg_finite]
        have h := ofHom_one_neg_den (-q)
        have hnn : -(-q) = q := by grind
        rw [hnn] at h
        simpa [ofHom_den_ne_zero hnq, ofHom_den_ne_zero hq,
          neg_finite] using h
  | infinity =>
      simp [neg_infinity, inv_infinity, neg_finite]

theorem ofHom_scale {k n d : Rat} (hk : k ≠ 0) :
    ofHom (k * n) (k * d) = ofHom n d := by
  unfold ofHom
  by_cases hd : d = 0
  · have hkd : k * d = 0 := by grind
    simp [hd]
  · have hkd : k * d ≠ 0 := by grind
    simp [hd, hkd]
    rw [Rat.div_def, Rat.div_def]
    grind [Rat.inv_mul_rev, Rat.mul_assoc, Rat.mul_comm,
      Rat.mul_inv_cancel]

theorem tanAdd_pair_nonzero (x y : ProjectiveRat) :
    x.num * y.den + x.den * y.num ≠ 0 ∨
      x.den * y.den - x.num * y.num ≠ 0 := by
  cases x <;> cases y
  · rename_i q r
    by_cases hsum : q + r = 0
    · right
      intro hdenRaw
      have hden : 1 - q * r = 0 := by simpa [num, den] using hdenRaw
      have hq : q = -r := by grind
      have hz : 1 + r * r = 0 := by
        rw [hq] at hden
        grind [Rat.neg_mul, Rat.mul_neg, Rat.sub_eq_add_neg]
      have hpos : 0 < 1 + r * r := Stage.one_add_square_pos r
      rw [hz] at hpos
      exact Rat.lt_irrefl hpos
    · left
      simpa [num, den] using hsum
  · left
    intro h
    simp [num, den] at h
    have h' : (1 : Rat) = 0 := by grind
    exact (by native_decide : (1 : Rat) ≠ 0) h'
  · left
    intro h
    simp [num, den] at h
    have h' : (1 : Rat) = 0 := by grind
    exact (by native_decide : (1 : Rat) ≠ 0) h'
  · right
    intro h
    simp [num, den, Rat.sub_eq_add_neg] at h
    have h' : (-(1 : Rat)) = 0 := by grind
    exact (by native_decide : (-(1 : Rat)) ≠ 0) h'

theorem tanAdd_ofHom_left {n d : Rat}
    (hnd : n ≠ 0 ∨ d ≠ 0) (z : ProjectiveRat) :
    tanAdd (ofHom n d) z =
      ofHom (n * z.den + d * z.num) (d * z.den - n * z.num) := by
  cases z with
  | finite q =>
      by_cases hd : d = 0
      · have hn : n ≠ 0 := by
          cases hnd with
          | inl hn => exact hn
          | inr hd' => exact False.elim (hd' hd)
        rw [ofHom_den_zero hd, tanAdd_infinity_finite]
        have hnum : n * (finite q).den + d * (finite q).num = n := by
          simp [num, den, hd]
          grind
        have hden :
            d * (finite q).den - n * (finite q).num = n * (-q) := by
          simp [num, den, hd]
          grind [Rat.sub_eq_add_neg]
        rw [hnum, hden]
        simpa using (ofHom_scale (k := n) (n := 1) (d := -q) hn).symm
      · rw [ofHom_den_ne_zero hd, tanAdd_finite_finite]
        calc
          ofHom (n / d + q) (1 - (n / d) * q)
              =
            ofHom (d * (n / d + q))
              (d * (1 - (n / d) * q)) := by
              exact (ofHom_scale
                (k := d) (n := n / d + q)
                (d := 1 - (n / d) * q) hd).symm
          _ =
            ofHom (n * (finite q).den + d * (finite q).num)
              (d * (finite q).den - n * (finite q).num) := by
              congr <;>
                simp [num, den, Rat.div_def] <;>
                grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel,
                  Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul]
  | infinity =>
      by_cases hd : d = 0
      · have hn : n ≠ 0 := by
          cases hnd with
          | inl hn => exact hn
          | inr hd' => exact False.elim (hd' hd)
        rw [ofHom_den_zero hd, tanAdd_infinity_infinity]
        have hnum : n * infinity.den + d * infinity.num = 0 := by
          simp [num, den, hd]
          grind
        have hden : d * infinity.den - n * infinity.num = -n := by
          simp [num, den, hd, Rat.sub_eq_add_neg]
          grind
        rw [hnum, hden]
        have hneg : -n ≠ 0 := by grind
        rw [ofHom_den_ne_zero hneg]
        grind [Rat.div_def, Rat.mul_inv_cancel]
      · rw [ofHom_den_ne_zero hd, tanAdd_finite_infinity]
        calc
          ofHom 1 (-(n / d))
              =
            ofHom (d * 1) (d * (-(n / d))) := by
              exact (ofHom_scale
                (k := d) (n := 1) (d := -(n / d)) hd).symm
          _ =
            ofHom (n * infinity.den + d * infinity.num)
              (d * infinity.den - n * infinity.num) := by
              congr <;>
                simp [num, den, Rat.div_def] <;>
                grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel,
                  Rat.sub_eq_add_neg, Rat.neg_mul, Rat.mul_neg]

theorem tanAdd_ofHom_ofHom {a b c d : Rat}
    (hab : a ≠ 0 ∨ b ≠ 0) (hcd : c ≠ 0 ∨ d ≠ 0) :
    tanAdd (ofHom a b) (ofHom c d) =
      ofHom (a * d + b * c) (b * d - a * c) := by
  rw [tanAdd_ofHom_left hab (ofHom c d)]
  by_cases hd : d = 0
  · have hc : c ≠ 0 := by
      cases hcd with
      | inl hc => exact hc
      | inr hd' => exact False.elim (hd' hd)
    rw [ofHom_den_zero hd]
    simp [num, den]
    have hleft : ofHom ((0 : Rat) + b) (0 - a) = ofHom b (-a) := by
      congr <;> grind [Rat.sub_eq_add_neg]
    rw [hleft]
    calc
      ofHom b (-a) = ofHom (c * b) (c * (-a)) := by
        exact (ofHom_scale (k := c) (n := b) (d := -a) hc).symm
      _ = ofHom (a * d + b * c) (b * d - a * c) := by
        congr <;>
          grind [Rat.sub_eq_add_neg, Rat.mul_comm, Rat.mul_neg,
            Rat.neg_mul]
  · rw [ofHom_den_ne_zero hd]
    simp [num, den]
    calc
      ofHom (a + b * (c / d)) (b - a * (c / d)) =
          ofHom (d * (a + b * (c / d)))
            (d * (b - a * (c / d))) := by
        exact (ofHom_scale
          (k := d) (n := a + b * (c / d))
          (d := b - a * (c / d)) hd).symm
      _ = ofHom (a * d + b * c) (b * d - a * c) := by
        congr <;>
          simp [Rat.div_def] <;>
          grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
            Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm,
            Rat.mul_inv_cancel]

theorem tanAdd_assoc (x y z : ProjectiveRat) :
    tanAdd (tanAdd x y) z = tanAdd x (tanAdd y z) := by
  change
    tanAdd
      (ofHom (x.num * y.den + x.den * y.num)
        (x.den * y.den - x.num * y.num)) z =
      tanAdd x
        (ofHom (y.num * z.den + y.den * z.num)
          (y.den * z.den - y.num * z.num))
  rw [tanAdd_ofHom_left (tanAdd_pair_nonzero x y) z]
  rw [tanAdd_comm x
    (ofHom (y.num * z.den + y.den * z.num)
      (y.den * z.den - y.num * z.num))]
  rw [tanAdd_ofHom_left (tanAdd_pair_nonzero y z) x]
  have hnum :
      (x.num * y.den + x.den * y.num) * z.den +
          (x.den * y.den - x.num * y.num) * z.num =
        (y.num * z.den + y.den * z.num) * x.den +
          (y.den * z.den - y.num * z.num) * x.num := by
    grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
      Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
  have hden :
      (x.den * y.den - x.num * y.num) * z.den -
          (x.num * y.den + x.den * y.num) * z.num =
        (y.den * z.den - y.num * z.num) * x.den -
          (y.num * z.den + y.den * z.num) * x.num := by
    grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
      Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
  rw [hnum, hden]

theorem tanAdd_neg_left_self (x : ProjectiveRat) :
    tanAdd x.neg x = finite 0 := by
  rw [tanAdd_comm]
  exact tanAdd_neg_self x

theorem tanSub_zero_right (x : ProjectiveRat) :
    tanSub x (finite 0) = x := by
  unfold tanSub
  rw [neg_finite]
  simpa using tanAdd_zero_right x

theorem tanSub_zero_left (x : ProjectiveRat) :
    tanSub (finite 0) x = x.neg := by
  unfold tanSub
  exact tanAdd_zero_left x.neg

theorem tanSub_neg_right (x y : ProjectiveRat) :
    tanSub x y.neg = tanAdd x y := by
  unfold tanSub
  rw [neg_neg]

theorem tanAdd_neg_cancel_right (x y : ProjectiveRat) :
    tanAdd (tanAdd x y) y.neg = x := by
  rw [tanAdd_assoc, tanAdd_neg_self, tanAdd_zero_right]

theorem tanAdd_neg_cancel_left (x y : ProjectiveRat) :
    tanAdd x.neg (tanAdd x y) = y := by
  rw [← tanAdd_assoc, tanAdd_neg_left_self, tanAdd_zero_left]

theorem tanSub_add_cancel (x y : ProjectiveRat) :
    tanAdd (tanSub x y) y = x := by
  unfold tanSub
  rw [tanAdd_assoc, tanAdd_neg_left_self, tanAdd_zero_right]

theorem tanAdd_sub_cancel (x y : ProjectiveRat) :
    tanSub (tanAdd x y) y = x := by
  unfold tanSub
  exact tanAdd_neg_cancel_right x y

theorem tanDouble_zero :
    tanDouble (finite 0) = finite 0 := by
  unfold tanDouble
  exact tanAdd_zero_left (finite 0)

theorem tanDouble_neg (x : ProjectiveRat) :
    tanDouble x.neg = (tanDouble x).neg := by
  cases x with
  | finite q =>
      rw [neg_finite, tanDouble_finite, tanDouble_finite]
      have hnum : 2 * (-q) = -(2 * q) := by grind
      have hden : 1 - (-q) * (-q) = 1 - q * q := by
        grind [Rat.neg_mul, Rat.mul_neg, Rat.neg_neg]
      rw [hnum, hden]
      exact ofHom_neg_num (2 * q) (1 - q * q)
  | infinity =>
      rw [neg_infinity, tanDouble_infinity]
      native_decide

theorem tanAdd_neg_neg (x y : ProjectiveRat) :
    tanAdd x.neg y.neg = (tanAdd x y).neg := by
  cases x <;> cases y
  · rename_i q r
    rw [neg_finite, neg_finite, tanAdd_finite_finite,
      tanAdd_finite_finite]
    have hnum : (-q) + (-r) = -(q + r) := by grind
    have hden : 1 - (-q) * (-r) = 1 - q * r := by
      grind [Rat.neg_mul, Rat.mul_neg, Rat.neg_neg]
    rw [hnum, hden]
    exact ofHom_neg_num (q + r) (1 - q * r)
  · rename_i q
    rw [neg_finite, neg_infinity, tanAdd_finite_infinity,
      tanAdd_finite_infinity]
    have hnn : - -q = q := by grind
    rw [hnn]
    exact ofHom_one_neg_den q
  · rename_i q
    rw [neg_infinity, neg_finite, tanAdd_infinity_finite,
      tanAdd_infinity_finite]
    have hnn : - -q = q := by grind
    rw [hnn]
    exact ofHom_one_neg_den q
  · rw [neg_infinity, tanAdd_infinity_infinity]
    native_decide

theorem tanSub_neg_left (x y : ProjectiveRat) :
    tanSub x.neg y = (tanAdd x y).neg := by
  unfold tanSub
  exact tanAdd_neg_neg x y

theorem tanSub_neg_neg (x y : ProjectiveRat) :
    tanSub x.neg y.neg = (tanSub x y).neg := by
  unfold tanSub
  simpa [neg_neg] using tanAdd_neg_neg x y.neg

theorem tanSub_anti_comm (x y : ProjectiveRat) :
    tanSub y x = (tanSub x y).neg := by
  unfold tanSub
  rw [tanAdd_comm y x.neg]
  simpa [neg_neg] using tanAdd_neg_neg x y.neg

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
represents the point at infinity.  This is the natural setting for using the
rational circle parametrization on the full projective parameter line. -/
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

The parameter `t` is the rational slope coordinate for the stereographic
circle chart.  This gives a first, fully rational layer of circle-coordinate
identities before the later angle-to-point algorithm turns arbitrary raw
angles into circle points.
-/

def point (t : Rat) : PiCirclePoint :=
  Stage.point t

def cos (t : Rat) : Rat :=
  (point t).x

def sin (t : Rat) : Rat :=
  (point t).y

def finiteTan (t : Rat) : Rat :=
  sin t / cos t

def tan (t : Rat) : ProjectiveRat :=
  projectiveSlope (point t)

def cot (t : Rat) : Rat :=
  cos t / sin t

def sec (t : Rat) : Rat :=
  1 / cos t

def csc (t : Rat) : Rat :=
  1 / sin t

def cosRaw (t : Rat) : RealRaw :=
  RealRaw.ofRat (cos t)

def sinRaw (t : Rat) : RealRaw :=
  RealRaw.ofRat (sin t)

def tanRaw (t : Rat) : RealRaw :=
  RealRaw.ofRat (finiteTan t)

def cotRaw (t : Rat) : RealRaw :=
  RealRaw.ofRat (cot t)

def secRaw (t : Rat) : RealRaw :=
  RealRaw.ofRat (sec t)

def cscRaw (t : Rat) : RealRaw :=
  RealRaw.ofRat (csc t)

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

theorem projectiveSlope_pointMul
    {p q : PiCirclePoint}
    (hp : p.y ≠ 0 ∨ p.x ≠ 0)
    (hq : q.y ≠ 0 ∨ q.x ≠ 0) :
    projectiveSlope (pointMul p q) =
      ProjectiveRat.tanAdd (projectiveSlope p) (projectiveSlope q) := by
  unfold projectiveSlope pointMul
  rw [ProjectiveRat.tanAdd_ofHom_ofHom hp hq]
  have hnum :
      p.x * q.y + p.y * q.x = p.y * q.x + p.x * q.y := by
    grind [Rat.add_comm]
  rw [hnum]

def quarterComplementParameter (u : Rat) : Rat :=
  (1 - u) / (1 + u)

def chartAddNum (u v : Rat) : Rat :=
  u + v

def chartAddDen (u v : Rat) : Rat :=
  1 - u * v

def chartAddParameter (u v : Rat) : Rat :=
  chartAddNum u v / chartAddDen u v

theorem chartAddParameter_zero_right (u : Rat) :
    chartAddParameter u 0 = u := by
  unfold chartAddParameter chartAddNum chartAddDen
  rw [Rat.div_def]
  grind

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

/-- The tangent-addition chart gives the exact rational denominator identity
for the arctangent kernel. -/
theorem one_add_square_chartAddParameter {u v : Rat}
    (hden : chartAddDen u v ≠ 0) :
    1 + chartAddParameter u v * chartAddParameter u v =
      chartAddNormDen u v /
        (chartAddDen u v * chartAddDen u v) := by
  unfold chartAddParameter chartAddNormDen chartAddDen chartAddNum sq
  rw [Rat.div_def]
  have hsq : (1 - u * v) * (1 - u * v) ≠ 0 := by
    intro hzero
    rcases (Rat.mul_eq_zero.mp hzero) with hzero | hzero
    · exact hden hzero
    · exact hden hzero
  grind [Rat.mul_add, Rat.add_mul, Rat.add_assoc, Rat.add_comm,
    Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

/-- Under the rational tangent-addition chart, the Jacobian-scaled kernel
`1 / (1+x^2)` is preserved exactly.  This is the finite rational change of
variables identity needed to transport arctangent interval constructions. -/
theorem arctanKernel_chartAdd_jacobian {u v : Rat}
    (hden : chartAddDen u v ≠ 0) :
    (1 + u * u) /
        ((chartAddDen u v * chartAddDen u v) *
          (1 + chartAddParameter u v * chartAddParameter u v)) =
      1 / (1 + v * v) := by
  rw [one_add_square_chartAddParameter hden]
  have hcancel :
      (chartAddDen u v * chartAddDen u v) *
          (chartAddNormDen u v /
            (chartAddDen u v * chartAddDen u v)) =
        chartAddNormDen u v := by
    rw [Rat.div_def]
    have hsq : chartAddDen u v * chartAddDen u v ≠ 0 := by
      intro hzero
      rcases (Rat.mul_eq_zero.mp hzero) with hzero | hzero
      · exact hden hzero
      · exact hden hzero
    grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
  rw [hcancel, chartAdd_normDen_eq]
  rw [Rat.div_def, Rat.div_def]
  have hu : 1 + u * u ≠ 0 :=
    Rat.ne_of_gt (Stage.one_add_square_pos u)
  grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

private theorem rat_eq_of_mul_eq_mul_ne {a b c : Rat}
    (hc : c ≠ 0) (h : a * c = b * c) : a = b := by
  calc
    a = (a * c) * c⁻¹ := by
      have hcancel : c * c⁻¹ = 1 := Rat.mul_inv_cancel c hc
      grind [Rat.mul_assoc, Rat.mul_comm]
    _ = (b * c) * c⁻¹ := by rw [h]
    _ = b := by
      have hcancel : c * c⁻¹ = 1 := Rat.mul_inv_cancel c hc
      grind [Rat.mul_assoc, Rat.mul_comm]

/-- Exact endpoint displacement under the rational tangent-addition chart.
This is the finite interval-transport algebra paired with the kernel
Jacobian identity above. -/
theorem chartAddParameter_sub {u p r : Rat}
    (hp : chartAddDen u p ≠ 0) (hr : chartAddDen u r ≠ 0) :
    chartAddParameter u r - chartAddParameter u p =
      ((1 + u * u) * (r - p)) /
        (chartAddDen u p * chartAddDen u r) := by
  change 1 - u * p ≠ 0 at hp
  change 1 - u * r ≠ 0 at hr
  have hprod : (1 - u * p) * (1 - u * r) ≠ 0 := by
    intro hzero
    rcases (Rat.mul_eq_zero.mp hzero) with hzero | hzero
    · exact hp hzero
    · exact hr hzero
  apply rat_eq_of_mul_eq_mul_ne hprod
  unfold chartAddParameter chartAddNum chartAddDen
  simp only [Rat.div_def, Rat.inv_mul_rev]
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.add_assoc,
    Rat.add_comm, Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

/-- On cells whose chart denominators are positive, the tangent-addition
chart preserves endpoint order. -/
theorem chartAddParameter_mono {u p r : Rat}
    (hp : 0 < chartAddDen u p) (hr : 0 < chartAddDen u r)
    (hpr : p <= r) :
    chartAddParameter u p <= chartAddParameter u r := by
  have hpne : chartAddDen u p ≠ 0 := Rat.ne_of_gt hp
  have hrne : chartAddDen u r ≠ 0 := Rat.ne_of_gt hr
  have hnum : 0 <= (1 + u * u) * (r - p) :=
    Rat.mul_nonneg
      (Rat.le_of_lt (Stage.one_add_square_pos u))
      (by grind [Rat.sub_eq_add_neg])
  have hden : 0 < chartAddDen u p * chartAddDen u r :=
    Rat.mul_pos hp hr
  have hquot :
      0 <= ((1 + u * u) * (r - p)) /
        (chartAddDen u p * chartAddDen u r) := by
    rw [Rat.div_def]
    exact Rat.mul_nonneg hnum (Rat.le_of_lt ((Rat.inv_pos).2 hden))
  rw [← chartAddParameter_sub hpne hrne] at hquot
  grind [Rat.sub_eq_add_neg]

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

theorem tan_composedPoint_eq_tanAdd (u v : Rat) :
    projectiveSlope (composedPoint u v) =
      ProjectiveRat.tanAdd (tan u) (tan v) := by
  unfold composedPoint tan
  exact projectiveSlope_pointMul
    (p := point u) (q := point v)
    (sin_ne_zero_or_cos_ne_zero u)
    (sin_ne_zero_or_cos_ne_zero v)

theorem tan_chartAddParameter_eq_tanAdd {u v : Rat}
    (hden : Ne (chartAddDen u v) 0) :
    tan (chartAddParameter u v) =
      ProjectiveRat.tanAdd (tan u) (tan v) := by
  calc
    tan (chartAddParameter u v) =
        projectiveSlope (point (chartAddParameter u v)) := rfl
    _ = projectiveSlope (composedPoint u v) := by
        exact (congrArg projectiveSlope
          (composedPoint_eq_point_chartAdd hden)).symm
    _ = ProjectiveRat.tanAdd (tan u) (tan v) :=
        tan_composedPoint_eq_tanAdd u v

theorem tan_chartSubParameter_eq_tanSub {u v : Rat}
    (hden : Ne (chartAddDen u (-v)) 0) :
    tan (chartAddParameter u (-v)) =
      ProjectiveRat.tanSub (tan u) (tan v) := by
  calc
    tan (chartAddParameter u (-v)) =
        ProjectiveRat.tanAdd (tan u) (tan (-v)) :=
      tan_chartAddParameter_eq_tanAdd hden
    _ = ProjectiveRat.tanSub (tan u) (tan v) := by
      unfold ProjectiveRat.tanSub
      rw [tan_neg]

theorem tan_chartDoubleParameter_eq_tanDouble {u : Rat}
    (hden : Ne (chartAddDen u u) 0) :
    tan (chartAddParameter u u) =
      ProjectiveRat.tanDouble (tan u) := by
  calc
    tan (chartAddParameter u u) =
        ProjectiveRat.tanAdd (tan u) (tan u) :=
      tan_chartAddParameter_eq_tanAdd hden
    _ = ProjectiveRat.tanDouble (tan u) := rfl

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
  projective_neg_involutive :
    forall x : ProjectiveRat, x.neg.neg = x
  projective_inv_involutive :
    forall x : ProjectiveRat, x.inv.inv = x
  projective_inv_neg :
    forall x : ProjectiveRat, x.neg.inv = x.inv.neg
  projective_tan_add_finite_finite :
    forall x y : Rat,
      ProjectiveRat.tanAdd (ProjectiveRat.finite x) (ProjectiveRat.finite y) =
        ProjectiveRat.ofHom (x + y) (1 - x * y)
  projective_tan_add_finite_infinity :
    forall x : Rat,
      ProjectiveRat.tanAdd (ProjectiveRat.finite x) ProjectiveRat.infinity =
        ProjectiveRat.ofHom 1 (-x)
  projective_tan_add_infinity_finite :
    forall x : Rat,
      ProjectiveRat.tanAdd ProjectiveRat.infinity (ProjectiveRat.finite x) =
        ProjectiveRat.ofHom 1 (-x)
  projective_tan_add_infinity_infinity :
    ProjectiveRat.tanAdd ProjectiveRat.infinity ProjectiveRat.infinity =
      ProjectiveRat.finite 0
  projective_tan_sub_finite_finite :
    forall x y : Rat,
      ProjectiveRat.tanSub (ProjectiveRat.finite x) (ProjectiveRat.finite y) =
        ProjectiveRat.ofHom (x - y) (1 + x * y)
  projective_tan_sub_finite_infinity :
    forall x : Rat,
      ProjectiveRat.tanSub (ProjectiveRat.finite x) ProjectiveRat.infinity =
        ProjectiveRat.ofHom 1 (-x)
  projective_tan_sub_infinity_finite :
    forall x : Rat,
      ProjectiveRat.tanSub ProjectiveRat.infinity (ProjectiveRat.finite x) =
        ProjectiveRat.ofHom 1 x
  projective_tan_sub_infinity_infinity :
    ProjectiveRat.tanSub ProjectiveRat.infinity ProjectiveRat.infinity =
      ProjectiveRat.finite 0
  projective_tan_add_zero_left :
    forall x : ProjectiveRat, ProjectiveRat.tanAdd (ProjectiveRat.finite 0) x = x
  projective_tan_add_zero_right :
    forall x : ProjectiveRat, ProjectiveRat.tanAdd x (ProjectiveRat.finite 0) = x
  projective_tan_add_comm :
    forall x y : ProjectiveRat, ProjectiveRat.tanAdd x y = ProjectiveRat.tanAdd y x
  projective_tan_add_assoc :
    forall x y z : ProjectiveRat,
      ProjectiveRat.tanAdd (ProjectiveRat.tanAdd x y) z =
        ProjectiveRat.tanAdd x (ProjectiveRat.tanAdd y z)
  projective_tan_add_neg_self :
    forall x : ProjectiveRat, ProjectiveRat.tanAdd x x.neg = ProjectiveRat.finite 0
  projective_tan_add_neg_left_self :
    forall x : ProjectiveRat, ProjectiveRat.tanAdd x.neg x = ProjectiveRat.finite 0
  projective_tan_add_neg_cancel_right :
    forall x y : ProjectiveRat,
      ProjectiveRat.tanAdd (ProjectiveRat.tanAdd x y) y.neg = x
  projective_tan_add_neg_cancel_left :
    forall x y : ProjectiveRat,
      ProjectiveRat.tanAdd x.neg (ProjectiveRat.tanAdd x y) = y
  projective_tan_sub_self :
    forall x : ProjectiveRat, ProjectiveRat.tanSub x x = ProjectiveRat.finite 0
  projective_tan_sub_zero_right :
    forall x : ProjectiveRat, ProjectiveRat.tanSub x (ProjectiveRat.finite 0) = x
  projective_tan_sub_zero_left :
    forall x : ProjectiveRat, ProjectiveRat.tanSub (ProjectiveRat.finite 0) x = x.neg
  projective_tan_sub_neg_right :
    forall x y : ProjectiveRat, ProjectiveRat.tanSub x y.neg =
      ProjectiveRat.tanAdd x y
  projective_tan_sub_neg_left :
    forall x y : ProjectiveRat, ProjectiveRat.tanSub x.neg y =
      (ProjectiveRat.tanAdd x y).neg
  projective_tan_sub_neg_neg :
    forall x y : ProjectiveRat,
      ProjectiveRat.tanSub x.neg y.neg = (ProjectiveRat.tanSub x y).neg
  projective_tan_sub_anti_comm :
    forall x y : ProjectiveRat,
      ProjectiveRat.tanSub y x = (ProjectiveRat.tanSub x y).neg
  projective_tan_sub_add_cancel :
    forall x y : ProjectiveRat, ProjectiveRat.tanAdd (ProjectiveRat.tanSub x y) y = x
  projective_tan_add_sub_cancel :
    forall x y : ProjectiveRat, ProjectiveRat.tanSub (ProjectiveRat.tanAdd x y) y = x
  projective_tan_double_finite :
    forall x : Rat,
      ProjectiveRat.tanDouble (ProjectiveRat.finite x) =
        ProjectiveRat.ofHom (2 * x) (1 - x * x)
  projective_tan_double_infinity :
    ProjectiveRat.tanDouble ProjectiveRat.infinity = ProjectiveRat.finite 0
  projective_tan_double_zero :
    ProjectiveRat.tanDouble (ProjectiveRat.finite 0) = ProjectiveRat.finite 0
  projective_tan_double_neg :
    forall x : ProjectiveRat,
      ProjectiveRat.tanDouble x.neg = (ProjectiveRat.tanDouble x).neg
  projective_tan_add_neg_neg :
    forall x y : ProjectiveRat,
      ProjectiveRat.tanAdd x.neg y.neg = (ProjectiveRat.tanAdd x y).neg
  projective_slope_point_mul :
    forall p q : PiCirclePoint,
      p.y ≠ 0 ∨ p.x ≠ 0 ->
      q.y ≠ 0 ∨ q.x ≠ 0 ->
      projectiveSlope (pointMul p q) =
        ProjectiveRat.tanAdd (projectiveSlope p) (projectiveSlope q)
  projective_tan_composed_point :
    forall u v : Rat,
      projectiveSlope (composedPoint u v) =
        ProjectiveRat.tanAdd (tan u) (tan v)
  projective_tan_chart_add :
    forall u v : Rat, Ne (chartAddDen u v) 0 ->
      tan (chartAddParameter u v) =
        ProjectiveRat.tanAdd (tan u) (tan v)
  projective_tan_chart_sub :
    forall u v : Rat, Ne (chartAddDen u (-v)) 0 ->
      tan (chartAddParameter u (-v)) =
        ProjectiveRat.tanSub (tan u) (tan v)
  projective_tan_chart_double :
    forall u : Rat, Ne (chartAddDen u u) 0 ->
      tan (chartAddParameter u u) =
        ProjectiveRat.tanDouble (tan u)
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
  projective_neg_involutive := ProjectiveRat.neg_neg
  projective_inv_involutive := ProjectiveRat.inv_inv
  projective_inv_neg := ProjectiveRat.inv_neg
  projective_tan_add_finite_finite := ProjectiveRat.tanAdd_finite_finite
  projective_tan_add_finite_infinity := ProjectiveRat.tanAdd_finite_infinity
  projective_tan_add_infinity_finite := ProjectiveRat.tanAdd_infinity_finite
  projective_tan_add_infinity_infinity := ProjectiveRat.tanAdd_infinity_infinity
  projective_tan_sub_finite_finite := ProjectiveRat.tanSub_finite_finite
  projective_tan_sub_finite_infinity := ProjectiveRat.tanSub_finite_infinity
  projective_tan_sub_infinity_finite := ProjectiveRat.tanSub_infinity_finite
  projective_tan_sub_infinity_infinity := ProjectiveRat.tanSub_infinity_infinity
  projective_tan_add_zero_left := ProjectiveRat.tanAdd_zero_left
  projective_tan_add_zero_right := ProjectiveRat.tanAdd_zero_right
  projective_tan_add_comm := ProjectiveRat.tanAdd_comm
  projective_tan_add_assoc := ProjectiveRat.tanAdd_assoc
  projective_tan_add_neg_self := ProjectiveRat.tanAdd_neg_self
  projective_tan_add_neg_left_self := ProjectiveRat.tanAdd_neg_left_self
  projective_tan_add_neg_cancel_right := ProjectiveRat.tanAdd_neg_cancel_right
  projective_tan_add_neg_cancel_left := ProjectiveRat.tanAdd_neg_cancel_left
  projective_tan_sub_self := ProjectiveRat.tanSub_self
  projective_tan_sub_zero_right := ProjectiveRat.tanSub_zero_right
  projective_tan_sub_zero_left := ProjectiveRat.tanSub_zero_left
  projective_tan_sub_neg_right := ProjectiveRat.tanSub_neg_right
  projective_tan_sub_neg_left := ProjectiveRat.tanSub_neg_left
  projective_tan_sub_neg_neg := ProjectiveRat.tanSub_neg_neg
  projective_tan_sub_anti_comm := ProjectiveRat.tanSub_anti_comm
  projective_tan_sub_add_cancel := ProjectiveRat.tanSub_add_cancel
  projective_tan_add_sub_cancel := ProjectiveRat.tanAdd_sub_cancel
  projective_tan_double_finite := ProjectiveRat.tanDouble_finite
  projective_tan_double_infinity := ProjectiveRat.tanDouble_infinity
  projective_tan_double_zero := ProjectiveRat.tanDouble_zero
  projective_tan_double_neg := ProjectiveRat.tanDouble_neg
  projective_tan_add_neg_neg := ProjectiveRat.tanAdd_neg_neg
  projective_slope_point_mul := fun _ _ hp hq =>
    projectiveSlope_pointMul hp hq
  projective_tan_composed_point := tan_composedPoint_eq_tanAdd
  projective_tan_chart_add := fun _ _ h =>
    tan_chartAddParameter_eq_tanAdd h
  projective_tan_chart_sub := fun _ _ h =>
    tan_chartSubParameter_eq_tanSub h
  projective_tan_chart_double := fun _ h =>
    tan_chartDoubleParameter_eq_tanDouble h
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

/-- The unit-sector area of a normalized quarter-turn input.

If `t` denotes the geometric angle `t * (pi / 2)`, its unit-sector area is
`t * (pi / 4)`.  This is the quantity computed by `arctan.geom`: the rational
circle parameter is `u = tan(theta / 2)`, so the sector from `(1, 0)` to
`P(u)` has area `arctan(u) = theta / 2`.  Keeping this separate from
`quarterTurnRaw` prevents the inverse-arctangent construction from silently
losing that factor of two. -/
def halfQuarterTurnRaw (t : QuarterTurn) : RealRaw :=
  RealRaw.scaleRat (t / 4) piCircleArea

/-- Principal branch for the inverse-arctangent search, measured in normalized
quarter-turns.  This is the interval `[0, 1]`, corresponding to
`[0, pi / 2]`. -/
def unitIntervalBranch (t : QuarterTurn) : Prop :=
  0 <= t /\ t <= 1

/-- The first octant of the normalized quarter-turn coordinate.

This is the smaller branch `[0, π/4]`; it remains useful for symmetry and
complement reductions. -/
def firstOctantBranch (t : QuarterTurn) : Prop :=
  0 <= t /\ t <= (1 : Rat) / 2

/-- The full first-quadrant branch used by the half-angle arctangent inverse.

For `u = tan(theta / 2)`, the range `0 <= u <= 1` covers every
`0 <= theta <= pi / 2`, hence every normalized quarter-turn input
`0 <= t <= 1`.  The arctangent itself returns the sector area `theta / 2`,
which is why this branch is valid without any unbounded tangent calculation. -/
abbrev firstQuadrantBranch (t : QuarterTurn) : Prop :=
  unitIntervalBranch t

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

theorem firstOctantBranch_zero : firstOctantBranch 0 := by
  unfold firstOctantBranch
  constructor <;> native_decide

theorem firstOctantBranch_half : firstOctantBranch ((1 : Rat) / 2) := by
  unfold firstOctantBranch
  constructor <;> native_decide

theorem firstQuadrantBranch_zero : firstQuadrantBranch 0 :=
  unitIntervalBranch_zero

theorem firstQuadrantBranch_half : firstQuadrantBranch ((1 : Rat) / 2) :=
  unitIntervalBranch_half

theorem firstQuadrantBranch_one : firstQuadrantBranch 1 :=
  unitIntervalBranch_one

theorem firstOctantBranch_subset_unitInterval
    {t : QuarterTurn} (ht : firstOctantBranch t) :
    unitIntervalBranch t := by
  unfold firstOctantBranch at ht
  unfold unitIntervalBranch
  constructor
  · exact ht.1
  · exact Rat.le_trans ht.2 (by native_decide)

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
