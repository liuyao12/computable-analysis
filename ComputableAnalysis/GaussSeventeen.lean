import ComputableAnalysis.TrigSpecialValues

/-!
# Computational check for Gauss's 17-gon value

This file is deliberately computational rather than theorem-heavy.  It compares
the nested-radical expression for `cos(2*pi/17)` with a cosine value computed
from the power series, using the existing `piCircleArea` interval as the input
for `pi`.

The comparison is a sanity check, not a formal proof of Gauss's formula: the
power-series and square-root interval computations below are executable
certificates to the displayed precision, while the full semantic convergence
and constructibility theorem belongs to later infrastructure.
-/

namespace ComputableAnalysis

namespace GaussSeventeen

namespace Interval

def ofRat (q : Rat) : QInterval :=
  { lo := q, hi := q }

def add (I J : QInterval) : QInterval :=
  { lo := I.lo + J.lo, hi := I.hi + J.hi }

def sub (I J : QInterval) : QInterval :=
  add I (QInterval.neg J)

def scaleRat (r : Rat) (I : QInterval) : QInterval :=
  if 0 <= r then
    { lo := r * I.lo, hi := r * I.hi }
  else
    { lo := r * I.hi, hi := r * I.lo }

def mul (I J : QInterval) : QInterval :=
  QBox.mulRealInterval I.lo I.hi J.lo J.hi

def radius (I : QInterval) : Rat :=
  max (qabs (I.midpoint - I.lo)) (qabs (I.hi - I.midpoint))

def around (center radius : Rat) : QInterval :=
  { lo := center - radius, hi := center + radius }

end Interval

def nonnegativePart (q : Rat) : Rat :=
  if q < 0 then 0 else q

def sqrtUpperSeed (q : Rat) : Rat :=
  if q < 1 then 1 else q + 1

def sqrtRatRefine (q : Rat) (I : QInterval) : QInterval :=
  let m := I.midpoint
  if m * m <= q then
    { lo := m, hi := I.hi }
  else
    { lo := I.lo, hi := m }

def sqrtRatIntervalAux (q : Rat) : Nat -> QInterval -> QInterval
  | 0, I => I
  | n + 1, I => sqrtRatIntervalAux q n (sqrtRatRefine q I)

def sqrtRatInterval (q : Rat) (steps : Nat) : QInterval :=
  let q0 := nonnegativePart q
  sqrtRatIntervalAux q0 steps { lo := 0, hi := sqrtUpperSeed q0 }

def sqrtInterval (I : QInterval) (steps : Nat) : QInterval :=
  { lo := (sqrtRatInterval I.lo steps).lo,
    hi := (sqrtRatInterval I.hi steps).hi }

/-- The nested-radical expression

`(-1 + sqrt 17 + sqrt(34 - 2 sqrt 17)
  + 2 sqrt(17 + 3 sqrt 17 - sqrt(170 + 38 sqrt 17))) / 16`.
-/
def cosRadicalInterval (steps : Nat) : QInterval :=
  let s17 := sqrtRatInterval 17 steps
  let a := sqrtInterval
    (Interval.sub (Interval.ofRat 34) (Interval.scaleRat 2 s17)) steps
  let b0 := sqrtInterval
    (Interval.add (Interval.ofRat 170) (Interval.scaleRat 38 s17)) steps
  let b := sqrtInterval
    (Interval.sub (Interval.add (Interval.ofRat 17) (Interval.scaleRat 3 s17)) b0)
    steps
  Interval.scaleRat (1 / 16)
    (Interval.add
      (Interval.add (Interval.add (Interval.ofRat (-1)) s17) a)
      (Interval.scaleRat 2 b))

/-- The positive sine value recovered from `sqrt(1 - cos^2(2*pi/17))`. -/
def sinRadicalInterval (steps : Nat) : QInterval :=
  sqrtInterval
    (Interval.sub (Interval.ofRat 1)
      (Interval.mul (cosRadicalInterval steps) (cosRadicalInterval steps)))
    steps

/-- The angle `2*pi/17`, using `piCircleArea` as the pi interval source. -/
def angleInterval (piStage : Nat) : QInterval :=
  Interval.scaleRat (2 / 17) (piCircleArea.compute piStage)

/-- Finite cosine power-series sum at a rational input, with a simple
geometric-style tail radius.

The recurrence is the usual one:
`t_{k+1} = -t_k*x^2/((2k+1)(2k+2))`.
-/
def cosPowerSeriesPartialAndTail (x : Rat) (terms : Nat) : Rat × Rat :=
  Id.run do
    let mut sum : Rat := 0
    let mut term : Rat := 1
    for k in List.range terms do
      sum := sum + term
      term := -term * x * x /
        ((((2 * k + 1 : Nat) : Rat)) * (((2 * k + 2 : Nat) : Rat)))
    return (sum, 2 * qabs term)

/-- Finite sine power-series sum at a rational input, with a simple tail
radius. -/
def sinPowerSeriesPartialAndTail (x : Rat) (terms : Nat) : Rat × Rat :=
  Id.run do
    let mut sum : Rat := 0
    let mut term : Rat := x
    for k in List.range terms do
      sum := sum + term
      term := -term * x * x /
        ((((2 * k + 2 : Nat) : Rat)) * (((2 * k + 3 : Nat) : Rat)))
    return (sum, 2 * qabs term)

/-- Power-series cosine interval for `2*pi/17`.

The input-angle uncertainty is included by adding the radius of the
`piCircleArea`-derived input interval to the series tail radius. -/
def cosPowerSeriesInterval (piStage terms : Nat) : QInterval :=
  let X := angleInterval piStage
  let data := cosPowerSeriesPartialAndTail X.midpoint terms
  Interval.around data.1 (data.2 + Interval.radius X)

/-- Power-series sine interval for `2*pi/17`, with the same input-angle
uncertainty convention as `cosPowerSeriesInterval`. -/
def sinPowerSeriesInterval (piStage terms : Nat) : QInterval :=
  let X := angleInterval piStage
  let data := sinPowerSeriesPartialAndTail X.midpoint terms
  Interval.around data.1 (data.2 + Interval.radius X)

def powerSeriesCheck (piStage terms sqrtSteps : Nat) : Bool :=
  (cosPowerSeriesInterval piStage terms).overlaps (cosRadicalInterval sqrtSteps) &&
  (sinPowerSeriesInterval piStage terms).overlaps (sinRadicalInterval sqrtSteps)

def powerSeriesCheckReport (piStage terms sqrtSteps : Nat) : List String :=
  [ "angle " ++ (angleInterval piStage).display,
    "cos power series " ++ (cosPowerSeriesInterval piStage terms).display,
    "cos radical " ++ (cosRadicalInterval sqrtSteps).display,
    "sin power series " ++ (sinPowerSeriesInterval piStage terms).display,
    "sin radical " ++ (sinRadicalInterval sqrtSteps).display,
    "overlap check " ++ toString (powerSeriesCheck piStage terms sqrtSteps) ]

/-- A concrete executable check: at these stages, the cosine and sine
power-series intervals overlap the corresponding radical intervals. -/
theorem powerSeriesCheck_default :
    powerSeriesCheck 8 10 30 = true := by
  native_decide

end GaussSeventeen

end ComputableAnalysis
