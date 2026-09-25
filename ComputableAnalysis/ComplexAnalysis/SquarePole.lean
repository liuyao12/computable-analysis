import ComputableAnalysis.PDE.CauchyContour

/-!
# Sampled Cauchy periods on translated rational squares

The runtime evaluates all eight transformed reciprocal pullbacks at supplied
rational tags, then intersects explicit error boxes. The independent rectangle
period supplies the error certificate, not the centers of these boxes.
-/

namespace ComputableAnalysis.ComplexAnalysis.SquarePole

open PDE

open QComplex CauchyContour ArctanGeometry

structure Sampling where
  cells : Nat → List TaggedCell
  good : ∀ n, GoodCells (cells n)
  partition : ∀ n, intervals (cells n) = (arctanAreaLoopState 1 n).intervals

def midpoints : Sampling where
  cells := stageCells
  good n := midpointCells_good _
    (arctanAreaLoopState_intervals_unit (by grind) (by grind) n)
  partition _ := midpointCells_intervals _

def leftCells (pieces : List (Rat × Rat)) : List TaggedCell :=
  pieces.map fun (p, r) => ⟨p, r, p⟩

theorem leftCells_intervals (pieces : List (Rat × Rat)) :
    intervals (leftCells pieces) = pieces := by
  induction pieces with
  | nil => rfl
  | cons p ps ih => simp only [leftCells, intervals, List.map_cons] at ih ⊢; rw [ih]

theorem leftCells_good (pieces : List (Rat × Rat)) (hp : UnitIntervals pieces) :
    GoodCells (leftCells pieces) := by
  induction pieces with
  | nil => exact True.intro
  | cons p ps ih =>
    exact ⟨⟨hp.1, Rat.le_refl, hp.2.1, hp.2.2.1⟩, ih hp.2.2.2⟩

/-- A second literal algorithm, using the left endpoint instead of the
midpoint on every parameter cell. -/
def leftEndpoints : Sampling where
  cells n := leftCells (arctanAreaLoopState 1 n).intervals
  good n := leftCells_good _
    (arctanAreaLoopState_intervals_unit (by grind) (by grind) n)
  partition _ := leftCells_intervals _

def scaledDensity (center : QComplex) (r u : Rat) : QComplex :=
  (square.map fun e => scaledPullback center r e u).foldr add zero

theorem scaledDensity_eq (center : QComplex) (r : Rat) (hr : r ≠ 0) (u : Rat) :
    scaledDensity center r u = density u := by
  simp only [scaledDensity, scaledPullback_eq center r hr, density]

def scaledSum (center : QComplex) (r : Rat) : List TaggedCell → QComplex
  | [] => zero
  | c :: cs => add (scaleRat (c.right - c.left) (scaledDensity center r c.tag))
      (scaledSum center r cs)

theorem scaledSum_eq (center : QComplex) (r : Rat) (hr : r ≠ 0)
    (cells : List TaggedCell) : scaledSum center r cells = taggedSum cells := by
  induction cells with
  | nil => rfl
  | cons c cs ih => rw [scaledSum, scaledDensity_eq center r hr, ih, taggedSum]

def sample (center : QComplex) (r : Rat) (s : Sampling) (n : Nat) : QComplex :=
  scaledSum center r (s.cells n)

def candidate (center : QComplex) (r : Rat) (s : Sampling) : ComplexRaw where
  compute n := QBox.point (sample center r s n)

/-- The certified rectangle width is a literal rational error radius. -/
def radius (n : Nat) : Rat := (CauchyContour.raw.compute n).height

def quadrature (center : QComplex) (r : Rat) (s : Sampling) : ComplexRaw :=
  ComplexRaw.cauchyStabilize (candidate center r s) radius

theorem sample_enclosed (center : QComplex) (r : Rat) (hr : r ≠ 0)
    (s : Sampling) (n : Nat) :
    (QBox.point (sample center r s n)).NestedIn (CauchyContour.raw.compute n) := by
  unfold sample
  rw [scaledSum_eq center r hr]
  exact raw_encloses_taggedSum n (s.cells n) (s.good n) (s.partition n)

/-- The entire independent period box fits around the actual sampled sum. -/
theorem period_in_expanded_candidate (center : QComplex) (r : Rat) (hr : r ≠ 0)
    (s : Sampling) (n : Nat) :
    (CauchyContour.raw.compute n).NestedIn
      (QBox.expand ((candidate center r s).compute n) (radius n)) := by
  have hs := sample_enclosed center r hr s n
  have hh := CauchyContour.raw_valid.1 n
  have hz := CauchyContour.raw_width_zero n
  simp only [QBox.NestedIn, QComplex.le_def, QBox.point] at hs
  simp only [candidate, radius, QBox.NestedIn, QComplex.le_def,
    QBox.expand, QBox.point, QBox.width, QBox.height] at hh hz ⊢
  grind

theorem candidate_future (center : QComplex) (r : Rat) (hr : r ≠ 0)
    (s : Sampling) (k n : Nat) (hkn : k ≤ n) :
    ((candidate center r s).compute n).NestedIn
      (QBox.expand ((candidate center r s).compute k) (radius k)) :=
  QBox.nested_trans (sample_enclosed center r hr s n)
    (QBox.nested_trans (ComplexRaw.valid_nestedIn CauchyContour.raw_valid hkn)
      (period_in_expanded_candidate center r hr s k))

theorem radius_shrinks : ShrinksToZero radius := by
  intro eps
  obtain ⟨N, hN⟩ := CauchyContour.raw_valid.2.2 eps
  exact ⟨N, fun n hn => (hN n hn).2⟩

theorem quadrature_valid (center : QComplex) (r : Rat) (hr : r ≠ 0)
    (s : Sampling) : (quadrature center r s).Valid := by
  apply ComplexRaw.cauchyStabilize_valid
    (fun _ => QComplex.le_refl _) _ (candidate_future center r hr s) radius_shrinks
  intro eps
  refine ⟨0, ?_⟩
  intro n hn
  have hp := eps.property
  change (sample center r s n).re - (sample center r s n).re ≤ eps.val ∧
    (sample center r s n).im - (sample center r s n).im ≤ eps.val
  constructor <;> grind

theorem quadrature_compute_zero (center : QComplex) (r : Rat) (s : Sampling) :
    (quadrature center r s).compute 0 =
      QBox.expand (QBox.point (sample center r s 0)) (radius 0) := rfl

theorem quadrature_compute_succ (center : QComplex) (r : Rat) (s : Sampling) (n : Nat) :
    (quadrature center r s).compute (n + 1) =
      QBox.intersection ((quadrature center r s).compute n)
        (QBox.expand (QBox.point (sample center r s (n + 1))) (radius (n + 1))) := rfl

theorem quadrature_encloses_sample (center : QComplex) (r : Rat) (hr : r ≠ 0)
    (s : Sampling) (n : Nat) :
    (QBox.point (sample center r s n)).NestedIn ((quadrature center r s).compute n) :=
  ComplexRaw.cauchyStabilize_contains_current (candidate_future center r hr s) n

theorem quadrature_contains_period (center : QComplex) (r : Rat) (hr : r ≠ 0)
    (s : Sampling) (n : Nat) :
    (CauchyContour.raw.compute n).NestedIn ((quadrature center r s).compute n) := by
  apply ComplexRaw.cauchyStabilize_contains_external (external := CauchyContour.raw.compute)
    (fun k n hkn => QBox.nested_trans
      (ComplexRaw.valid_nestedIn CauchyContour.raw_valid hkn)
      (period_in_expanded_candidate center r hr s k)) n n (Nat.le_refl n)

theorem quadrature_equiv_period (center : QComplex) (r : Rat) (hr : r ≠ 0)
    (s : Sampling) : (quadrature center r s).Equiv CauchyContour.raw := by
  intro n
  apply (ComplexRaw.compareAt_overlap_iff _ _ n n).2
  have hc := quadrature_contains_period center r hr s n
  have ho := ComplexRaw.valid_ordered CauchyContour.raw_valid n
  exact ⟨QComplex.le_trans hc.1 ho, QComplex.le_trans ho hc.2⟩

theorem quadrature_equiv_twoPiI (center : QComplex) (r : Rat) (hr : r ≠ 0)
    (s : Sampling) : (quadrature center r s).Equiv CauchyContour.twoPiI :=
  ComplexRaw.equiv_trans (quadrature_valid center r hr s) CauchyContour.raw_valid
    CauchyContour.twoPiI_valid (quadrature_equiv_period center r hr s)
    CauchyContour.raw_equiv_twoPiI

/-- Translation, nonzero rational dilation, and the certified tag algorithm
may all change independently without changing the quadrature value. -/
theorem quadrature_independent (c d : QComplex) (r t : Rat) (hr : r ≠ 0) (ht : t ≠ 0)
    (s v : Sampling) : (quadrature c r s).Equiv (quadrature d t v) :=
  ComplexRaw.equiv_trans (quadrature_valid c r hr s) CauchyContour.raw_valid
    (quadrature_valid d t ht v) (quadrature_equiv_period c r hr s)
    (ComplexRaw.equiv_symm (quadrature_equiv_period d t ht v))

theorem quadrature_widths_bound (center : QComplex) (r : Rat) (s : Sampling) (n : Nat) :
    ((quadrature center r s).compute n).width ≤ 32 / (((2 ^ n : Nat) : Rat)) ∧
      ((quadrature center r s).compute n).height ≤ 32 / (((2 ^ n : Nat) : Rat)) := by
  have hc : ((quadrature center r s).compute n).NestedIn
      (QBox.expand (QBox.point (sample center r s n)) (radius n)) := by
    cases n with
    | zero => exact ⟨QComplex.le_refl _, QComplex.le_refl _⟩
    | succ n => rw [quadrature_compute_succ]; exact QBox.intersection_contained_right _ _
  have hw := QBox.width_height_le_of_nested hc
  have hp := CauchyContour.raw_height_geometric n
  simp only [QBox.expand, QBox.point, QBox.width, QBox.height, radius] at hw
  simp only [QBox.width, QBox.height] at hp ⊢
  constructor <;> grind [Rat.div_def]


end ComputableAnalysis.ComplexAnalysis.SquarePole
