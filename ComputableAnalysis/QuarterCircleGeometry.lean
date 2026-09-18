import ComputableAnalysis.RationalGeometry
import ComputableAnalysis.ArctanGeometry

/-!
# The quarter-circle computation and its polygonal interpretation

The existing rational area-loop computation is retained. Its validity does not
use the general polygon theory. This module identifies its concrete boundary
lists with that theory, including invariance under a change of starting vertex.
-/
namespace ComputableAnalysis.QuarterCircleGeometry
open RationalGeometry

/-- Reuse the existing quarter-sector program, without a new evaluation schedule. -/
abbrev raw : RealRaw := ArctanGeometry.arctanGeom 1

theorem raw_valid : raw.Valid := ArctanGeometry.arctanGeom_one_valid

/-- The opening's numerical formula: sums on the actual midpoint-refined cells. -/
theorem raw_compute (n : Nat) : raw.compute n =
    ArctanGeometry.geometricSumInterval (ArctanGeometry.arctanAreaLoopState 1 n).intervals := by
  rw [ArctanGeometry.arctanGeom_one_compute_eq]
  exact ArctanGeometry.positiveLoopComputeAtStage_eq_geometricSumInterval (by decide) n

/-- The exact cell gap, estimated without an integral or an area interpretation. -/
theorem cell_gap_le_cube {u v : Rat} (hu : 0 ≤ u) (huv : u ≤ v) :
    ArctanGeometry.geometricUpperStep u v - ArctanGeometry.geometricLowerStep u v ≤
      (v-u)*(v-u)*(v-u) := by
  let a := 1+u*v
  let b := (1+u*u)*(1+v*v)
  have hv : 0 ≤ v := Rat.le_trans hu huv
  have huv0 := Rat.mul_nonneg hu hv
  have hu2 := Rat.mul_nonneg hu hu
  have hv2 := Rat.mul_nonneg hv hv
  have ha : 1 ≤ a := by dsimp [a]; grind
  have hb : 1 ≤ b := by
    have h := Rat.mul_nonneg hu2 hv2
    dsimp [b]; grind
  have hab : 1 ≤ b*a := by
    have h := Rat.mul_le_mul_of_nonneg_left ha (show 0 ≤ b by grind)
    grind
  have hap : 0 < a := by grind
  have hbp : 0 < b := by grind
  have hac := Rat.mul_inv_cancel a (Rat.ne_of_gt hap)
  have hbc := Rat.mul_inv_cancel b (Rat.ne_of_gt hbp)
  have hid : (ArctanGeometry.geometricUpperStep u v - ArctanGeometry.geometricLowerStep u v)*(b*a)
      = (v-u)*(v-u)*(v-u) := by
    change ((v-u)/a-((v-u)*a)/b)*(b*a) = _
    simp only [Rat.div_def]
    have hpoly : b-a*a = (v-u)*(v-u) := by dsimp [a,b]; grind
    grind
  have hg := ArctanGeometry.geometricLowerStep_le_geometricUpperStep hu huv
  have h := Rat.mul_le_mul_of_nonneg_left hab (show 0 ≤
    ArctanGeometry.geometricUpperStep u v-ArctanGeometry.geometricLowerStep u v by grind)
  rw [hid] at h
  simpa only [Rat.mul_one] using h

private theorem geometric_gap_le_mesh (cells : List (Rat × Rat)) (h : Rat)
    (hc : ∀ c ∈ cells, 0 ≤ c.1 ∧ c.1 ≤ c.2 ∧ c.2-c.1 ≤ h) :
    ArctanGeometry.geometricUpperSum cells-ArctanGeometry.geometricLowerSum cells ≤
      h*ArctanGeometry.intervalSquareSum cells := by
  induction cells with
  | nil => simp only [ArctanGeometry.geometricUpperSum, ArctanGeometry.geometricLowerSum,
      ArctanGeometry.intervalSquareSum]; grind
  | cons c cs ih =>
    have hh := hc c (by simp)
    have ht := ih (fun d hd => hc d (by simp [hd]))
    have hcell := cell_gap_le_cube hh.1 hh.2.1
    have hl : 0 ≤ c.2-c.1 := by have hz := hh.2.1; grind
    have hm := Rat.mul_le_mul_of_nonneg_right hh.2.2 (Rat.mul_nonneg hl hl)
    rcases c with ⟨u,v⟩
    simp only [ArctanGeometry.geometricUpperSum, ArctanGeometry.geometricLowerSum,
      ArctanGeometry.intervalSquareSum]
    dsimp only at *
    grind

/-- The opening computation's geometric gap is at most 4⁻ⁿ. -/
theorem raw_width (n : Nat) : (raw.compute n).width ≤
    (1 / ((2^n : Nat) : Rat)) * (1 / ((2^n : Nat) : Rat)) := by
  let h : Rat := 1 / ((2^n : Nat) : Rat)
  have hn : 0 < ((2^n : Nat) : Rat) := by
    exact_mod_cast Nat.two_pow_pos n
  have hinv : 0 ≤ (((2^n : Nat) : Rat))⁻¹ := Rat.le_of_lt ((Rat.inv_pos).2 hn)
  have hc : ∀ c ∈ (ArctanGeometry.arctanAreaLoopState 1 n).intervals,
      0 ≤ c.1 ∧ c.1 ≤ c.2 ∧ c.2-c.1 ≤ h := by
    rw [ArctanGeometry.arctanAreaLoopState_one_intervals_eq_uniform]
    intro c hc
    obtain ⟨k,_,rfl⟩ := List.mem_map.mp hc
    have hk0 : 0 ≤ (k : Rat) := Rat.natCast_nonneg
    have hs : ((Nat.succ k : Nat) : Rat) = (k : Rat)+1 := by simp
    dsimp only
    rw [hs]
    simp only [Rat.div_def]
    dsimp [h]
    simp only [Rat.div_def, Rat.one_mul]
    have hh := Rat.mul_nonneg hk0 hinv
    constructor
    · exact hh
    constructor <;> grind
  have hw := geometric_gap_le_mesh (ArctanGeometry.arctanAreaLoopState 1 n).intervals h hc
  rw [ArctanGeometry.arctanAreaLoopState_one_squareSum] at hw
  rw [raw_compute]
  exact hw

/-- The old circle coordinate records carry exactly the same two rational coordinates. -/
def point (p : PiCirclePoint) : Point := ⟨p.x,p.y⟩

def innerPolygon (n : Nat) : Polygon :=
  (RationalCircle.Stage.origin :: (RationalCircle.dyadicStage n).innerBoundary).map point

def outerPolygon (n : Nat) : Polygon :=
  (RationalCircle.Stage.origin :: (RationalCircle.dyadicStage n).outerBoundary).map point

private theorem walk_legacy (finish p : PiCirclePoint) (ps : List PiCirclePoint) :
    walk edgeArea (point finish) (point p) (ps.map point) =
      RationalCircle.Stage.twiceSignedAreaAux finish p ps / 2 := by
  induction ps generalizing p with
  | nil => rfl
  | cons q ps ih =>
    simp only [List.map_cons, walk, ih]
    change RationalCircle.Stage.cross p q / 2 +
      RationalCircle.Stage.twiceSignedAreaAux finish q ps / 2 =
      (RationalCircle.Stage.cross p q + RationalCircle.Stage.twiceSignedAreaAux finish q ps) / 2
    simp only [Rat.div_def]; grind

/-- A bridge, not a replacement of old numerical definitions. -/
theorem area_legacy (ps : List PiCirclePoint) :
    area (ps.map point) = RationalCircle.Stage.twiceSignedArea ps / 2 := by
  cases ps with
  | nil => simp [area, cycleSum, RationalCircle.Stage.twiceSignedArea, Rat.div_def]
  | cons p ps => exact walk_legacy p p ps

private theorem edge_from_origin (p : PiCirclePoint) :
    edgeArea (point RationalCircle.Stage.origin) (point p) = 0 := by
  simp only [edgeArea, det, point, RationalCircle.Stage.origin, Rat.div_def]; grind

private theorem edge_to_origin (p : PiCirclePoint) :
    edgeArea (point p) (point RationalCircle.Stage.origin) = 0 := by
  simp only [edgeArea, det, point, RationalCircle.Stage.origin, Rat.div_def]; grind

private theorem inner_walk_nonneg (S : RationalCircle.Stage) (hS : 0 < S.subdivisions)
    (k count : Nat) (hk : k+count ≤ S.subdivisions) :
    0 ≤ walk edgeArea (point RationalCircle.Stage.origin) (point (S.samplePoint k))
      ((S.innerBoundaryFrom (k+1) count).map point) := by
  induction count generalizing k with
  | zero =>
    change 0 ≤ edgeArea (point (S.samplePoint k)) (point RationalCircle.Stage.origin)
    rw [edge_to_origin]; exact Rat.le_refl
  | succ count ih =>
    change 0 ≤ edgeArea (point (S.samplePoint k)) (point (S.samplePoint (k+1))) +
      walk edgeArea (point RationalCircle.Stage.origin) (point (S.samplePoint (k+1)))
        ((S.innerBoundaryFrom (k+1+1) count).map point)
    have he : 0 ≤ RationalCircle.Stage.cross (S.samplePoint k) (S.samplePoint (k+1)) :=
      RationalCircle.Stage.samplePoint_cross_nonneg_of_order S hS (i := k) (j := k+1) (by omega)
    have hh : 0 ≤ edgeArea (point (S.samplePoint k)) (point (S.samplePoint (k+1))) := by
      change 0 ≤ RationalCircle.Stage.cross (S.samplePoint k) (S.samplePoint (k+1)) / 2
      simp only [Rat.div_def]; exact Rat.mul_nonneg he (Rat.le_of_lt ((Rat.inv_pos).2 (by decide)))
    exact Rat.add_nonneg hh (ih (k+1) (by omega))

theorem inner_area_nonneg (n : Nat) : 0 ≤ area (innerPolygon n) := by
  let S := RationalCircle.dyadicStage n
  change 0 ≤ edgeArea (point RationalCircle.Stage.origin) (point (S.samplePoint 0)) +
    walk edgeArea (point RationalCircle.Stage.origin) (point (S.samplePoint 0))
      ((S.innerBoundaryFrom 1 S.subdivisions).map point)
  rw [edge_from_origin, Rat.zero_add]
  exact inner_walk_nonneg S (RationalCircle.dyadicStage_positive n) 0 S.subdivisions (by omega)

private theorem outer_walk_nonneg (S : RationalCircle.Stage) (hS : 0 < S.subdivisions)
    (k count : Nat) (hk : k+count ≤ S.subdivisions) :
    0 ≤ walk edgeArea (point RationalCircle.Stage.origin) (point (S.samplePoint k))
      ((S.outerBoundaryFrom k count).map point) := by
  induction count generalizing k with
  | zero =>
    change 0 ≤ edgeArea (point (S.samplePoint k)) (point RationalCircle.Stage.origin)
    rw [edge_to_origin]; exact Rat.le_refl
  | succ count ih =>
    change 0 ≤ edgeArea (point (S.samplePoint k)) (point (S.tangentPoint k)) +
      (edgeArea (point (S.tangentPoint k)) (point (S.samplePoint (k+1))) +
      walk edgeArea (point RationalCircle.Stage.origin) (point (S.samplePoint (k+1)))
        ((S.outerBoundaryFrom (k+1) count).map point))
    have h1 := RationalCircle.Stage.adjacentEntryTangentCross_nonneg S hS k
    have h2 := RationalCircle.Stage.adjacentExitTangentCross_nonneg S hS k
    have h3 := ih (k+1) (by omega)
    change 0 ≤ RationalCircle.Stage.cross (S.samplePoint k) (S.tangentPoint k) / 2 +
      (RationalCircle.Stage.cross (S.tangentPoint k) (S.samplePoint (k+1)) / 2 + _)
    simp only [Rat.div_def]
    grind

theorem outer_area_nonneg (n : Nat) : 0 ≤ area (outerPolygon n) := by
  let S := RationalCircle.dyadicStage n
  change 0 ≤ edgeArea (point RationalCircle.Stage.origin) (point (S.samplePoint 0)) +
    walk edgeArea (point RationalCircle.Stage.origin) (point (S.samplePoint 0))
      ((S.outerBoundaryFrom 0 S.subdivisions).map point)
  rw [edge_from_origin, Rat.zero_add]
  exact outer_walk_nonneg S (RationalCircle.dyadicStage_positive n) 0 S.subdivisions (by omega)

/-- These particular boundary orientations have positive area, so the old
magnitude convention agrees with the new orientation-aware area exactly. -/
theorem raw_compute_polygon_areas (n : Nat) :
    raw.compute n = {lo := area (innerPolygon n), hi := area (outerPolygon n)} := by
  have he := ArctanGeometry.four_arctanGeom_one_compute_eq_piCircleArea_compute n
  rw [ArctanGeometry.piCircleArea_compute_eq_piCircleAreaPolygon_compute] at he
  have hi := inner_area_nonneg n
  have ho := outer_area_nonneg n
  have ai : (RationalCircle.dyadicStage n).innerQuarterArea = area (innerPolygon n) := by
    rw [show area (innerPolygon n) = _ from area_legacy _] at hi ⊢
    exact qabs_eq_self_of_nonneg hi
  have ao : (RationalCircle.dyadicStage n).outerQuarterArea = area (outerPolygon n) := by
    rw [show area (outerPolygon n) = _ from area_legacy _] at ho ⊢
    exact qabs_eq_self_of_nonneg ho
  rw [RationalCircle.piCircleAreaPolygon_compute_eq_stage] at he
  change (RealRaw.scaleRatCompute 4 raw n) =
    {lo := 4*(RationalCircle.dyadicStage n).innerQuarterArea,
     hi := 4*(RationalCircle.dyadicStage n).outerQuarterArea} at he
  rw [ai,ao] at he
  simp only [RealRaw.scaleRatCompute, if_pos (show (0 : Rat) ≤ 4 by decide)] at he
  have hL := congrArg QInterval.lo he
  have hU := congrArg QInterval.hi he
  cases hR : raw.compute n with
  | mk a b =>
    rw [hR] at hL hU
    simp only at hL hU
    congr 1 <;> grind

/-- Any starting vertex and fan point give the same two rational stage endpoints. -/
theorem raw_compute_any_fans (n k l : Nat) (p q : Point) :
    raw.compute n =
      {lo := fanArea p (startAt (innerPolygon n) k),
       hi := fanArea q (startAt (outerPolygon n) l)} := by
  rw [fanArea_startAt, fanArea_startAt]
  exact raw_compute_polygon_areas n

end ComputableAnalysis.QuarterCircleGeometry
