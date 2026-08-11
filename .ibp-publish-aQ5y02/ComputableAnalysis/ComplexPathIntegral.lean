import ComputableAnalysis.ComplexInterval

/-!
# Complex path integrals over polygonal paths

This file is the first computational layer for complex line integrals.  It
uses only rational complex sample points and finite left Riemann sums along
straight segments.
-/

namespace ComputableAnalysis

namespace QInterval

def scaledDecimal (digits : Nat) (scaled : Int) : String :=
  let scale := decimalScale digits
  let scaledAbs := if scaled < 0 then -scaled else scaled
  let whole := Int.ediv scaledAbs scale
  let frac := Int.emod scaledAbs scale
  let sign := if scaled < 0 then "-" else ""
  trimDecimalString
    (sign ++ toString whole ++
      if digits = 0 then "" else "." ++ zeroPad digits (toString frac))

def floorDecimal (digits : Nat) (q : Rat) : String :=
  scaledDecimal digits
    (Int.ediv (q.num * decimalScale digits) (Int.ofNat q.den))

def ceilDecimal (digits : Nat) (q : Rat) : String :=
  scaledDecimal digits
    (-Int.ediv (-(q.num * decimalScale digits)) (Int.ofNat q.den))

def hasLeadingMinus (s : String) : Bool :=
  match s.toList with
  | '-' :: _ => true
  | _ => false

def stripLeadingMinus (s : String) : String :=
  match s.toList with
  | '-' :: chars => String.ofList chars
  | _ => s

end QInterval

namespace QComplex

def signedImagDecimal (digits : Nat) (y : Rat) : String :=
  if y < 0 then
    " - " ++ QInterval.ratDecimal digits (-y) ++ "i"
  else
    " + " ++ QInterval.ratDecimal digits y ++ "i"

def decimal (digits : Nat) (z : QComplex) : String :=
  QInterval.ratDecimal digits z.re ++ signedImagDecimal digits z.im

def decimalWith (reDigits imDigits : Nat) (z : QComplex) : String :=
  QInterval.ratDecimal reDigits z.re ++ signedImagDecimal imDigits z.im

def signedImagString (s : String) : String :=
  if QInterval.hasLeadingMinus s then
    " - " ++ QInterval.stripLeadingMinus s ++ "i"
  else
    " + " ++ s ++ "i"

def decimalFromStrings (re im : String) : String :=
  re ++ signedImagString im

end QComplex

namespace QBox

def hull (z w : QComplex) : QBox :=
  { lo := { re := minRat z.re w.re, im := minRat z.im w.im },
    hi := { re := maxRat2 z.re w.re, im := maxRat2 z.im w.im } }

def digitsForWidthAux (width : Rat) : Nat -> Nat -> Nat
  | 0, d => d
  | fuel + 1, d =>
      if 1 <= width * ((10 ^ d : Nat) : Rat) then
        d
      else
        digitsForWidthAux width fuel (d + 1)

def digitsForWidth (maxDigits : Nat) (width : Rat) : Nat :=
  if width = 0 then 0 else digitsForWidthAux (qabs width) maxDigits 0

def lowerCoordDecimal (maxDigits digits : Nat) (lo hi : Rat) : String :=
  if lo = hi then
    QInterval.ratDecimalCompact maxDigits lo
  else
    QInterval.floorDecimal digits lo

def upperCoordDecimal (maxDigits digits : Nat) (lo hi : Rat) : String :=
  if lo = hi then
    QInterval.ratDecimalCompact maxDigits hi
  else
    QInterval.ceilDecimal digits hi

def decimalResolution (digits : Nat) : String :=
  if digits = 0 then "1" else "1e-" ++ toString digits

def widthDecimal (maxDigits digits : Nat) (width : Rat) : String :=
  let displayDigits := Nat.min maxDigits (digits + 2)
  let s := QInterval.ratDecimalCompact displayDigits width
  if QInterval.decimalExactAt displayDigits width then
    s
  else if s = "0" then
    "<" ++ decimalResolution displayDigits
  else
    s ++ "..."

def lowerDecimal (maxDigits reDigits imDigits : Nat) (B : QBox) : String :=
  QComplex.decimalFromStrings
    (lowerCoordDecimal maxDigits reDigits B.lo.re B.hi.re)
    (lowerCoordDecimal maxDigits imDigits B.lo.im B.hi.im)

def upperDecimal (maxDigits reDigits imDigits : Nat) (B : QBox) : String :=
  QComplex.decimalFromStrings
    (upperCoordDecimal maxDigits reDigits B.lo.re B.hi.re)
    (upperCoordDecimal maxDigits imDigits B.lo.im B.hi.im)

def widthComplexDecimal (reDigits imDigits : Nat) (B : QBox) : String :=
  if B.height = 0 then
    QInterval.ratDecimal reDigits B.width
  else
    QComplex.decimalWith reDigits imDigits
      { re := B.width, im := B.height }

def compactWidthComplexDecimal (maxDigits reDigits imDigits : Nat) (B : QBox) : String :=
  let reWidth := widthDecimal maxDigits reDigits B.width
  let imWidth := widthDecimal maxDigits imDigits B.height
  if B.height = 0 then
    reWidth
  else
    QComplex.decimalFromStrings reWidth imWidth

def decimal (digits : Nat) (B : QBox) : String :=
  if B.lo.im = 0 ∧B.hi.im = 0 then
    "[" ++ QInterval.ratDecimal digits B.lo.re ++ ", " ++
      QInterval.ratDecimal digits B.hi.re ++ "] width=" ++
      QInterval.ratDecimal digits B.width
  else
    "[" ++ QComplex.decimal digits B.lo ++ ", " ++
      QComplex.decimal digits B.hi ++ "] width=" ++
      widthComplexDecimal digits digits B

def compactDecimal (maxDigits : Nat) (B : QBox) : String :=
  let reDigits := digitsForWidth maxDigits B.width
  let imDigits := digitsForWidth maxDigits B.height
  if B.lo.im = 0 ∧B.hi.im = 0 then
    "[" ++ lowerCoordDecimal maxDigits reDigits B.lo.re B.hi.re ++ ", " ++
      upperCoordDecimal maxDigits reDigits B.lo.re B.hi.re ++ "] width=" ++
      widthDecimal maxDigits reDigits B.width
  else
    "[" ++ lowerDecimal maxDigits reDigits imDigits B ++ ", " ++
      upperDecimal maxDigits reDigits imDigits B ++ "] width=" ++
      compactWidthComplexDecimal maxDigits reDigits imDigits B

end QBox

namespace ComplexRaw

def decimalAt (z : ComplexRaw) (digits : Nat) (n : Nat) : String :=
  QBox.decimal digits (z.compute n)

def compactDecimalAt (z : ComplexRaw) (maxDigits : Nat) (n : Nat) : String :=
  QBox.compactDecimal maxDigits (z.compute n)

end ComplexRaw

namespace FunctionRaw

/-- An exact rational-complex function as a complex `FunctionRaw`. -/
def exact (f : QComplex -> QComplex) : FunctionRaw where
  domain := FunctionRaw.entire
  compute := fun z _ _ => QBox.point (f z)

end FunctionRaw

namespace ComplexPathIntegral

/-- A point evaluator together with an interval evaluator for an entire
complex function.  The interval evaluator is what the integral uses: a point
sample alone is not an upper or lower bound. -/
structure EntireBoxFunctionRaw where
  point : FunctionRaw
  boxCompute : QBox -> QBox

/-- A point on the straight segment from `a` to `b`, with parameter `k/n`. -/
def segmentPoint (a b : QComplex) (n : Nat) (k : Nat) : QComplex :=
  QComplex.add a
    (QComplex.scaleRat ((k : Rat) * (1 / (n : Rat)))
      (QComplex.sub b a))

/-- The infinitesimal step `dz = (b-a)/n` for the segment from `a` to `b`. -/
def segmentStep (a b : QComplex) (n : Nat) : QComplex :=
  QComplex.scaleRat (1 / (n : Rat)) (QComplex.sub b a)

def segmentSubBox (a b : QComplex) (n : Nat) (k : Nat) : QBox :=
  QBox.hull (segmentPoint a b n k) (segmentPoint a b n (k + 1))

/-- Left Riemann sum for `integral_a^b f(z) dz` along one straight segment. -/
def segmentLeftSum (f : FunctionRaw) (a b : QComplex) (n : Nat)
    (hDomain : forall k : Fin n, f.domain (segmentPoint a b n k.val))
    (evalPrecision : Nat) : QBox :=
  let dz := segmentStep a b n
  (List.finRange n).foldl
    (fun acc k =>
      let z := segmentPoint a b n k.val
      let hz := hDomain k
      QBox.add acc (QBox.mul (f.compute z hz evalPrecision) (QBox.point dz)))
    QBox.zero

def segmentLeftSumEntire (f : FunctionRaw) (hEntire : forall z, f.domain z)
    (a b : QComplex) (n evalPrecision : Nat) : QBox :=
  segmentLeftSum f a b n (fun k => hEntire (segmentPoint a b n k.val)) evalPrecision

/-- Left Riemann sum over a polygonal path, represented by consecutive
vertices.  To integrate around a closed polygon, repeat the first vertex at the
end of the list. -/
def polygonalLeftSumEntire (f : FunctionRaw) (hEntire : forall z, f.domain z) :
    List QComplex -> Nat -> Nat -> QBox
  | a :: b :: rest, n, evalPrecision =>
      QBox.add
        (segmentLeftSumEntire f hEntire a b n evalPrecision)
        (polygonalLeftSumEntire f hEntire (b :: rest) n evalPrecision)
  | _, _, _ => QBox.zero

/-- Interval enclosure for one subsegment contribution.

The whole subsegment is first boxed, then `f` is evaluated on that box, and
only then do we multiply by `dz`.  This avoids assuming that a left endpoint
sample is a lower or upper bound. -/
def subsegmentIntegralBox (f : EntireBoxFunctionRaw)
    (a b : QComplex) (n : Nat) (k : Nat) : QBox :=
  QBox.mul (f.boxCompute (segmentSubBox a b n k)) (QBox.point (segmentStep a b n))

def segmentIntegralBoxEntire (f : EntireBoxFunctionRaw)
    (a b : QComplex) (n : Nat) : QBox :=
  (List.finRange n).foldl
    (fun acc k => QBox.add acc (subsegmentIntegralBox f a b n k.val))
    QBox.zero

def polygonalSegmentBoxesEntire (f : EntireBoxFunctionRaw) :
    List QComplex -> Nat -> List QBox
  | a :: b :: rest, n =>
      segmentIntegralBoxEntire f a b n ::
        polygonalSegmentBoxesEntire f (b :: rest) n
  | _, _ => []

def polygonalIntegralBoxEntire (f : EntireBoxFunctionRaw) :
    List QComplex -> Nat -> QBox
  | a :: b :: rest, n =>
      QBox.add
        (segmentIntegralBoxEntire f a b n)
        (polygonalIntegralBoxEntire f (b :: rest) n)
  | _, _ => QBox.zero

/-- A raw complex algorithm for a polygonal path integral.

At stage `n`, it boxes each of the `n` subsegments of every path segment,
evaluates the integrand by interval arithmetic on each subsegment box, and
adds the resulting `f(z) dz` boxes.  The output is an enclosure, not a left
sum being treated as a lower bound. -/
def polygonalIntegralRawEntire
    (f : EntireBoxFunctionRaw)
    (vertices : List QComplex) : ComplexRaw where
  compute := fun n => polygonalIntegralBoxEntire f vertices n

def zero : QComplex := QComplex.zero
def one : QComplex := QComplex.one
def I : QComplex := { re := 0, im := 1 }
def onePlusI : QComplex := { re := 1, im := 1 }

/-- The positively oriented unit square. -/
def unitSquare : List QComplex := [zero, one, onePlusI, I, zero]

def zSquared : EntireBoxFunctionRaw where
  point := FunctionRaw.exact (fun z => QComplex.mul z z)
  boxCompute := fun Z => QBox.mul Z Z

def zSquaredUnitSquareRaw : ComplexRaw :=
  polygonalIntegralRawEntire zSquared unitSquare

def zSquaredUnitSquareLeftSum (n : Nat) : QBox :=
  polygonalLeftSumEntire zSquared.point (fun _ => trivial) unitSquare n n

def zSquaredUnitSquareSegmentBoxes (n : Nat) : List QBox :=
  polygonalSegmentBoxesEntire zSquared unitSquare n

def zSquaredOnUnitSquare (n : Nat) : QBox :=
  zSquaredUnitSquareRaw.compute n

def cauchyCheckUnitSquareZSquared (n : Nat) : Bool :=
  let eps : QPos := if hn : n = 0 then
      { val := 1, property := by native_decide }
    else
      { val := (1 / (n : Rat)), property := one_div_nat_pos (Nat.pos_of_ne_zero hn) }
  QBox.overlaps (zSquaredOnUnitSquare n) (QBox.zeroAround eps)

def zCubedPlusTwoZ : EntireBoxFunctionRaw where
  point := FunctionRaw.exact (fun z =>
    QComplex.add (QComplex.mul z (QComplex.mul z z))
      (QComplex.scaleRat 2 z))
  boxCompute := fun Z =>
    QBox.add (QBox.mul Z (QBox.mul Z Z)) (QBox.scaleRat 2 Z)

def zCubedPlusTwoZUnitSquareRaw : ComplexRaw :=
  polygonalIntegralRawEntire zCubedPlusTwoZ unitSquare

def zCubedPlusTwoZUnitSquareLeftSum (n : Nat) : QBox :=
  polygonalLeftSumEntire zCubedPlusTwoZ.point (fun _ => trivial) unitSquare n n

def zCubedPlusTwoZUnitSquareSegmentBoxes (n : Nat) : List QBox :=
  polygonalSegmentBoxesEntire zCubedPlusTwoZ unitSquare n

def zCubedPlusTwoZOnUnitSquare (n : Nat) : QBox :=
  zCubedPlusTwoZUnitSquareRaw.compute n

def cauchyCheckUnitSquareZCubedPlusTwoZ (n : Nat) : Bool :=
  let eps : QPos := if hn : n = 0 then
      { val := 1, property := by native_decide }
    else
      { val := (1 / (n : Rat)), property := one_div_nat_pos (Nat.pos_of_ne_zero hn) }
  QBox.overlaps (zCubedPlusTwoZOnUnitSquare n) (QBox.zeroAround eps)

/- Put the cursor on these commands in VSCode to see the finite checks. -/
#eval! (zSquaredUnitSquareSegmentBoxes 10).map
  (QBox.compactDecimal 12)
#eval! QBox.compactDecimal 12 (zSquaredUnitSquareLeftSum 10)
#eval! zSquaredUnitSquareRaw.compactDecimalAt 12 10
#eval! cauchyCheckUnitSquareZSquared 10
#eval! zSquaredUnitSquareRaw.compactDecimalAt 12 100
#eval! cauchyCheckUnitSquareZSquared 100
#eval! zSquaredUnitSquareRaw.compactDecimalAt 12 1000
#eval! cauchyCheckUnitSquareZSquared 1000

#eval! (zCubedPlusTwoZUnitSquareSegmentBoxes 10).map
  (QBox.compactDecimal 12)
#eval! QBox.compactDecimal 12
  (zCubedPlusTwoZUnitSquareLeftSum 10)
#eval! zCubedPlusTwoZUnitSquareRaw.compactDecimalAt 12 10
#eval! cauchyCheckUnitSquareZCubedPlusTwoZ 10
#eval! zCubedPlusTwoZUnitSquareRaw.compactDecimalAt 12 100
#eval! cauchyCheckUnitSquareZCubedPlusTwoZ 100
#eval! zCubedPlusTwoZUnitSquareRaw.compactDecimalAt 12 1000
#eval! cauchyCheckUnitSquareZCubedPlusTwoZ 1000

end ComplexPathIntegral

end ComputableAnalysis
