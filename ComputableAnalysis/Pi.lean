import ComputableAnalysis.Basic
import ComputableAnalysis.AlgebraicFunctions
import ComputableAnalysis.PowerSeries

namespace ComputableAnalysis

/-- The Leibniz alternating series, computing `pi / 4`. -/
def leibnizSeries : RealRaw where
  compute := fun n =>
    let state : Rat × Rat := (List.range n).foldl
      (fun state (i : Nat) =>
        let term1 : Rat := 1 / (4 * i + 3)
        let term2 : Rat := 1 / (4 * i + 5)
        let lo := state.1 - term1
        let hi := lo + term2
        (hi, lo))
      (1, 0)
    { lo := state.2, hi := state.1 }

/-- Pi from the Leibniz alternating series. -/
def piLeibniz : RealRaw :=
  (4 : Nat) * leibnizSeries

/-- Pi from Machin's formula. -/
def piMachin : RealRaw :=
  (4 : Nat) * ((4 : Nat) * arctan (1 / 5) - arctan (1 / 239))

structure PiCirclePoint where
  x : Rat
  y : Rat
deriving Repr, DecidableEq

private theorem rat_square_nonneg (x : Rat) : 0 <= x * x := by
  by_cases hx : 0 <= x
  · exact Rat.mul_nonneg hx hx
  · have hneg : 0 <= -x := by grind
    have hsq : 0 <= (-x) * (-x) := Rat.mul_nonneg hneg hneg
    grind [Rat.mul_neg, Rat.neg_mul, Rat.neg_neg]

private theorem square_sum_sqrtDomain (dx dy : Rat) :
    sqrtDomain (dx * dx + dy * dy) := by
  change ¬dx * dx + dy * dy < 0
  have hx : 0 <= dx * dx := rat_square_nonneg dx
  have hy : 0 <= dy * dy := rat_square_nonneg dy
  grind

/-- Total length of a polygonal path through rational points. -/
def rationalPointPathLength (points : List PiCirclePoint) (n : Nat) : QInterval :=
  let segmentLength := fun (p q : PiCirclePoint) =>
    let dx := q.x - p.x
    let dy := q.y - p.y
    let normSq := dx * dx + dy * dy
    sqrtPartialRaw.compute normSq (square_sum_sqrtDomain dx dy) n
  let rec totalLength : List PiCirclePoint -> QInterval
    | [] => { lo := 0, hi := 0 }
    | [_] => { lo := 0, hi := 0 }
    | p :: q :: rest =>
        let length := segmentLength p q
        let tail := totalLength (q :: rest)
        { lo := length.lo + tail.lo,
          hi := length.hi + tail.hi }
  totalLength points

/-- Pi as the area of the unit disk. -/
def piCircleArea : RealRaw where
  compute := fun n =>
    let stage : Nat := 2 ^ n
    let parameter := fun (k : Nat) => (k : Rat) / (stage : Rat)
    let point := fun u =>
      let d := 1 + u * u
      let x := (1 - u * u) / d
      let y := (2 * u) / d
      ({ x := x, y := y } : PiCirclePoint)
    let samplePoint := fun k => point (parameter k)
    let rec innerBoundaryFrom (k count : Nat) : List PiCirclePoint :=
      match count with
      | 0 => []
      | count + 1 =>
          samplePoint k :: innerBoundaryFrom (k + 1) count
    let innerBoundary := innerBoundaryFrom 0 (stage + 1)
    let tangentIntersection := fun (p q : PiCirclePoint) =>
      let det := p.x * q.y - p.y * q.x
      let x := (q.y - p.y) / det
      let y := (p.x - q.x) / det
      ({ x := x, y := y } : PiCirclePoint)
    let outerTangentPoint := fun k =>
      tangentIntersection (samplePoint k) (samplePoint (k + 1))
    let rec outerBoundaryFrom (k count : Nat) : List PiCirclePoint :=
      match count with
      | 0 => []
      | count + 1 =>
          outerTangentPoint k ::
            samplePoint (k + 1) ::
              outerBoundaryFrom (k + 1) count
    let outerBoundary := samplePoint 0 :: outerBoundaryFrom 0 stage
    let origin : PiCirclePoint := { x := 0, y := 0 }
    let cross := fun (p q : PiCirclePoint) => p.x * q.y - p.y * q.x
    let rec twiceSignedAreaAux
        (first prev : PiCirclePoint) : List PiCirclePoint -> Rat
      | [] => cross prev first
      | vertex :: rest =>
          cross prev vertex + twiceSignedAreaAux first vertex rest
    let twiceSignedArea := fun vertices =>
      match vertices with
      | [] => 0
      | first :: rest => twiceSignedAreaAux first first rest
    let polygonArea := fun vertices => qabs (twiceSignedArea vertices / 2)
    let innerQuarter := polygonArea (origin :: innerBoundary)
    let outerQuarter := polygonArea (origin :: outerBoundary)
    { lo := 4 * innerQuarter,
      hi := 4 * outerQuarter }

/-- Pi as half the circumference of the unit circle. -/
def piCircumference : RealRaw where
  compute := fun n =>
    let stage : Nat := 2 ^ n
    let parameter := fun (k : Nat) => (k : Rat) / (stage : Rat)
    let point := fun u =>
      let d := 1 + u * u
      let x := (1 - u * u) / d
      let y := (2 * u) / d
      ({ x := x, y := y } : PiCirclePoint)
    let samplePoint := fun k => point (parameter k)
    let rec innerBoundaryFrom (k count : Nat) : List PiCirclePoint :=
      match count with
      | 0 => []
      | count + 1 =>
          samplePoint k :: innerBoundaryFrom (k + 1) count
    let innerBoundary := innerBoundaryFrom 0 (stage + 1)
    let tangentIntersection := fun (p q : PiCirclePoint) =>
      let det := p.x * q.y - p.y * q.x
      let x := (q.y - p.y) / det
      let y := (p.x - q.x) / det
      ({ x := x, y := y } : PiCirclePoint)
    let outerTangentPoint := fun k =>
      tangentIntersection (samplePoint k) (samplePoint (k + 1))
    let rec outerBoundaryFrom (k count : Nat) : List PiCirclePoint :=
      match count with
      | 0 => []
      | count + 1 =>
          outerTangentPoint k ::
            samplePoint (k + 1) ::
              outerBoundaryFrom (k + 1) count
    let outerBoundary := samplePoint 0 :: outerBoundaryFrom 0 stage
    let innerQuarter := rationalPointPathLength innerBoundary stage
    let outerQuarter := rationalPointPathLength outerBoundary stage
    { lo := (4 * innerQuarter.lo) / 2,
      hi := (4 * outerQuarter.hi) / 2 }

namespace PiExamples

#eval! (piLeibniz.compute 10).display
#eval! (piMachin.compute 10).display
#eval! (piCircleArea.compute 10).display
#eval! (piCircumference.compute 10).display

-- These are useful from the command line, but too large for the live infoview:
-- #eval! (piLeibniz.compute 100).display
-- #eval! (piMachin.compute 100).display

end PiExamples

end ComputableAnalysis
