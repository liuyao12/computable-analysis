import ComputableAnalysis.ComplexInterval
import ComputableAnalysis.ComplexMultiplication

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

/-! Finite endpoint algebra for polygonal paths. -/

def polygonalDisplacementTo (start : QComplex) : List QComplex -> QComplex
  | [] => QComplex.zero
  | stop :: rest =>
      QComplex.add (QComplex.sub stop start)
        (polygonalDisplacementTo stop rest)

theorem polygonalDisplacementTo_append_endpoint
    (start endpoint : QComplex) (vertices : List QComplex) :
    polygonalDisplacementTo start (vertices ++ [endpoint]) =
      QComplex.sub endpoint start := by
  induction vertices generalizing start with
  | nil =>
      cases endpoint
      cases start
      simp [polygonalDisplacementTo, QComplex.sub, QComplex.add,
        QComplex.neg, QComplex.zero]
      constructor <;> exact Rat.add_zero _
  | cons vertex vertices ih =>
      simp [polygonalDisplacementTo, ih, QComplex.sub, QComplex.add,
        QComplex.neg]
      grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]

theorem polygonalDisplacementTo_closed
    (start : QComplex) (vertices : List QComplex) :
    polygonalDisplacementTo start (vertices ++ [start]) =
      QComplex.zero := by
  rw [polygonalDisplacementTo_append_endpoint]
  cases start
  simp [QComplex.sub, QComplex.add, QComplex.neg, QComplex.zero]
  grind [Rat.sub_eq_add_neg]

theorem polygonalDisplacementTo_split_at
    (start middle : QComplex) (pre suf : List QComplex) :
    polygonalDisplacementTo start (pre ++ [middle] ++ suf) =
      QComplex.add
        (polygonalDisplacementTo start (pre ++ [middle]))
        (polygonalDisplacementTo middle suf) := by
  induction pre generalizing start with
  | nil =>
      cases middle
      cases start
      simp [polygonalDisplacementTo, QComplex.sub, QComplex.add,
        QComplex.neg, QComplex.zero]
      constructor <;> grind [Rat.add_assoc, Rat.add_comm]
  | cons vertex pre ih =>
      simp only [List.cons_append, polygonalDisplacementTo]
      rw [ih]
      cases start
      cases vertex
      simp [QComplex.sub, QComplex.add, QComplex.neg]
      constructor <;> grind [Rat.add_assoc, Rat.add_comm, Rat.sub_eq_add_neg]

/-- Finite primitive-cancellation value for the constant differential
`c dz` along a polygonal path. -/
def polygonalConstantDifferentialDisplacement
    (c start : QComplex) (vertices : List QComplex) : QComplex :=
  QComplex.mul c (polygonalDisplacementTo start vertices)

theorem polygonalConstantDifferentialDisplacement_split_at
    (c start middle : QComplex) (pre suf : List QComplex) :
    polygonalConstantDifferentialDisplacement c start
        (pre ++ [middle] ++ suf) =
      QComplex.add
        (polygonalConstantDifferentialDisplacement c start (pre ++ [middle]))
        (polygonalConstantDifferentialDisplacement c middle suf) := by
  unfold polygonalConstantDifferentialDisplacement
  rw [polygonalDisplacementTo_split_at]
  cases c
  cases (polygonalDisplacementTo start (pre ++ [middle]))
  cases (polygonalDisplacementTo middle suf)
  simp [QComplex.mul, QComplex.add]
  constructor <;> grind [Rat.mul_add, Rat.add_mul, Rat.mul_assoc,
    Rat.mul_comm, Rat.add_assoc, Rat.add_comm]

theorem polygonalConstantDifferentialDisplacement_append_endpoint
    (c start endpoint : QComplex) (vertices : List QComplex) :
    polygonalConstantDifferentialDisplacement c start
        (vertices ++ [endpoint]) =
      QComplex.mul c (QComplex.sub endpoint start) := by
  unfold polygonalConstantDifferentialDisplacement
  rw [polygonalDisplacementTo_append_endpoint]

theorem polygonalConstantDifferentialDisplacement_closed
    (c start : QComplex) (vertices : List QComplex) :
    polygonalConstantDifferentialDisplacement c start
        (vertices ++ [start]) = QComplex.zero := by
  unfold polygonalConstantDifferentialDisplacement
  rw [polygonalDisplacementTo_closed]
  cases c
  simp [QComplex.mul, QComplex.zero]
  constructor <;> grind

/-- The exact rational increment of the quadratic primitive `z ↦ z^2/2`.
This is a finite algebraic proxy for integrating the polynomial differential
`z dz` along one polygonal edge. -/
def quadraticPrimitiveIncrement (start stop : QComplex) : QComplex :=
  QComplex.scaleRat (1 / 2)
    (QComplex.sub (QComplex.mul stop stop) (QComplex.mul start start))

def polygonalQuadraticPrimitiveTo (start : QComplex) : List QComplex -> QComplex
  | [] => QComplex.zero
  | stop :: rest =>
      QComplex.add (quadraticPrimitiveIncrement start stop)
        (polygonalQuadraticPrimitiveTo stop rest)

theorem polygonalQuadraticPrimitiveTo_append_endpoint
    (start endpoint : QComplex) (vertices : List QComplex) :
    polygonalQuadraticPrimitiveTo start (vertices ++ [endpoint]) =
      quadraticPrimitiveIncrement start endpoint := by
  induction vertices generalizing start with
  | nil =>
      cases endpoint
      cases start
      simp [polygonalQuadraticPrimitiveTo, quadraticPrimitiveIncrement,
        QComplex.sub, QComplex.add, QComplex.neg, QComplex.scaleRat,
        QComplex.mul, QComplex.zero]
      constructor <;> exact Rat.add_zero _
  | cons vertex vertices ih =>
      simp [polygonalQuadraticPrimitiveTo, ih]
      cases endpoint
      cases start
      cases vertex
      simp [quadraticPrimitiveIncrement, QComplex.sub, QComplex.add,
        QComplex.neg, QComplex.scaleRat, QComplex.mul]
      constructor <;> grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
        Rat.mul_assoc, Rat.mul_comm]

theorem polygonalQuadraticPrimitiveTo_closed
    (start : QComplex) (vertices : List QComplex) :
    polygonalQuadraticPrimitiveTo start (vertices ++ [start]) =
      QComplex.zero := by
  rw [polygonalQuadraticPrimitiveTo_append_endpoint]
  cases start
  simp [quadraticPrimitiveIncrement, QComplex.sub, QComplex.add,
    QComplex.neg, QComplex.scaleRat, QComplex.mul, QComplex.zero]
  constructor <;> grind [Rat.sub_eq_add_neg]

/-- The finite endpoint increment for the monomial primitive
`z^(degree+1)/(degree+1)`.  The power is the executable rational-complex
natural power; no infinite series or analytic power function is involved. -/
def monomialPrimitiveIncrement (degree : Nat) (start stop : QComplex) : QComplex :=
  QComplex.scaleRat (((degree + 1 : Nat) : Rat)⁻¹)
    (QComplex.sub
      (QComplex.natPow stop (degree + 1))
      (QComplex.natPow start (degree + 1)))

def polygonalMonomialPrimitiveTo (degree : Nat) (start : QComplex) :
    List QComplex -> QComplex
  | [] => QComplex.zero
  | stop :: rest =>
      QComplex.add (monomialPrimitiveIncrement degree start stop)
        (polygonalMonomialPrimitiveTo degree stop rest)

theorem polygonalMonomialPrimitiveTo_append_endpoint
    (degree : Nat) (start endpoint : QComplex) (vertices : List QComplex) :
    polygonalMonomialPrimitiveTo degree start (vertices ++ [endpoint]) =
      monomialPrimitiveIncrement degree start endpoint := by
  induction vertices generalizing start with
  | nil =>
      cases endpoint
      cases start
      simp [polygonalMonomialPrimitiveTo, monomialPrimitiveIncrement,
        QComplex.sub, QComplex.add, QComplex.neg, QComplex.scaleRat,
        QComplex.natPow, QComplex.mul, QComplex.zero]
      constructor <;> exact Rat.add_zero _
  | cons vertex vertices ih =>
      simp [polygonalMonomialPrimitiveTo, ih]
      cases endpoint
      cases start
      cases vertex
      simp [monomialPrimitiveIncrement, QComplex.sub, QComplex.add,
        QComplex.neg, QComplex.scaleRat, QComplex.natPow, QComplex.mul]
      constructor <;> grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
        Rat.mul_assoc, Rat.mul_comm]

theorem polygonalMonomialPrimitiveTo_split_at
    (degree : Nat) (start middle : QComplex) (pre suf : List QComplex) :
    polygonalMonomialPrimitiveTo degree start
        (pre ++ [middle] ++ suf) =
      QComplex.add
        (polygonalMonomialPrimitiveTo degree start (pre ++ [middle]))
        (polygonalMonomialPrimitiveTo degree middle suf) := by
  induction pre generalizing start with
  | nil =>
      simp [polygonalMonomialPrimitiveTo, QComplex.add, QComplex.zero]
      constructor <;> grind [Rat.add_assoc, Rat.add_comm]
  | cons vertex pre ih =>
      simp only [List.cons_append, polygonalMonomialPrimitiveTo]
      rw [ih]
      cases start
      cases vertex
      cases middle
      simp [monomialPrimitiveIncrement, QComplex.sub, QComplex.add,
        QComplex.neg, QComplex.scaleRat, QComplex.natPow, QComplex.mul]
      constructor <;> grind [Rat.add_assoc, Rat.add_comm, Rat.sub_eq_add_neg]

theorem polygonalMonomialPrimitiveTo_closed
    (degree : Nat) (start : QComplex) (vertices : List QComplex) :
    polygonalMonomialPrimitiveTo degree start (vertices ++ [start]) =
      QComplex.zero := by
  rw [polygonalMonomialPrimitiveTo_append_endpoint]
  cases start
  simp [monomialPrimitiveIncrement, QComplex.sub, QComplex.add,
    QComplex.neg, QComplex.scaleRat, QComplex.natPow, QComplex.mul,
    QComplex.zero]
  constructor <;> grind [Rat.sub_eq_add_neg]

/-- Finite coefficient-list primitive evaluator.  A coefficient at index `k`
contributes `c * z^(k+1)/(k+1)`; the recursion is an executable finite sum. -/
def polynomialPrimitiveEvalAux : List QComplex -> QComplex -> Nat -> QComplex
  | [], _z, _degree => QComplex.zero
  | coefficient :: rest, z, degree =>
      QComplex.add
        (QComplex.mul coefficient
          (QComplex.scaleRat (((degree + 1 : Nat) : Rat)⁻¹)
            (QComplex.natPow z (degree + 1))))
        (polynomialPrimitiveEvalAux rest z (degree + 1))

def polynomialPrimitiveEval (coefficients : List QComplex) (z : QComplex) : QComplex :=
  polynomialPrimitiveEvalAux coefficients z 0

def polynomialPrimitiveIncrement
    (coefficients : List QComplex) (start stop : QComplex) : QComplex :=
  QComplex.sub (polynomialPrimitiveEval coefficients stop)
    (polynomialPrimitiveEval coefficients start)

def polygonalPolynomialPrimitiveTo
    (coefficients : List QComplex) (start : QComplex) : List QComplex -> QComplex
  | [] => QComplex.zero
  | stop :: rest =>
      QComplex.add (polynomialPrimitiveIncrement coefficients start stop)
        (polygonalPolynomialPrimitiveTo coefficients stop rest)

theorem polygonalPolynomialPrimitiveTo_append_endpoint
    (coefficients : List QComplex) (start endpoint : QComplex)
    (vertices : List QComplex) :
    polygonalPolynomialPrimitiveTo coefficients start
        (vertices ++ [endpoint]) =
      polynomialPrimitiveIncrement coefficients start endpoint := by
  have htel (x y z : QComplex) :
      QComplex.add (QComplex.sub y x) (QComplex.sub z y) =
        QComplex.sub z x := by
    cases x
    cases y
    cases z
    simp [QComplex.sub, QComplex.add, QComplex.neg]
    constructor <;> grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]
  have haddzero (x : QComplex) : QComplex.add x QComplex.zero = x := by
    cases x
    simp [QComplex.add, QComplex.zero]
    constructor <;> exact Rat.add_zero _
  induction vertices generalizing start with
  | nil =>
      simp [polygonalPolynomialPrimitiveTo]
      exact haddzero _
  | cons vertex vertices ih =>
      simp only [List.cons_append, polygonalPolynomialPrimitiveTo]
      rw [ih]
      exact htel _ _ _

theorem polygonalPolynomialPrimitiveTo_split_at
    (coefficients : List QComplex) (start middle : QComplex)
    (pre suf : List QComplex) :
    polygonalPolynomialPrimitiveTo coefficients start
        (pre ++ [middle] ++ suf) =
      QComplex.add
        (polygonalPolynomialPrimitiveTo coefficients start (pre ++ [middle]))
        (polygonalPolynomialPrimitiveTo coefficients middle suf) := by
  induction pre generalizing start with
  | nil =>
      simp [polygonalPolynomialPrimitiveTo, QComplex.add, QComplex.zero]
      constructor <;> grind [Rat.add_assoc, Rat.add_comm]
  | cons vertex pre ih =>
      simp only [List.cons_append, polygonalPolynomialPrimitiveTo]
      rw [ih]
      cases start
      cases vertex
      cases middle
      simp [polynomialPrimitiveIncrement, QComplex.sub, QComplex.add,
        QComplex.neg]
      constructor <;> grind [Rat.add_assoc, Rat.add_comm, Rat.sub_eq_add_neg]

theorem polygonalPolynomialPrimitiveTo_closed
    (coefficients : List QComplex) (start : QComplex)
    (vertices : List QComplex) :
    polygonalPolynomialPrimitiveTo coefficients start
        (vertices ++ [start]) = QComplex.zero := by
  rw [polygonalPolynomialPrimitiveTo_append_endpoint]
  cases start
  simp [polynomialPrimitiveIncrement, polynomialPrimitiveEval,
    QComplex.sub, QComplex.add, QComplex.neg, QComplex.zero]
  constructor <;> grind

/-! An exact finite polynomial path integral is useful when the differential is
already presented by its primitive coefficients.  It is a rational-complex
algorithm at every stage; no limiting path construction is involved. -/
def polygonalPolynomialIntegralRaw
    (coefficients : List QComplex) (start : QComplex)
    (vertices : List QComplex) : ComplexRaw :=
  ComplexRaw.ofQComplex
    (polygonalPolynomialPrimitiveTo coefficients start vertices)

theorem polygonalPolynomialIntegralRaw_valid
    (coefficients : List QComplex) (start : QComplex)
    (vertices : List QComplex) :
    (polygonalPolynomialIntegralRaw coefficients start vertices).Valid := by
  exact ComplexRaw.ofQComplex_valid _

theorem polygonalPolynomialIntegralRaw_equiv_endpoint
    (coefficients : List QComplex) (start endpoint : QComplex)
    (vertices : List QComplex) :
    (polygonalPolynomialIntegralRaw coefficients start (vertices ++ [endpoint])).Equiv
      (ComplexRaw.ofQComplex
        (polynomialPrimitiveIncrement coefficients start endpoint)) := by
  rw [polygonalPolynomialIntegralRaw,
    polygonalPolynomialPrimitiveTo_append_endpoint]
  exact ComplexRaw.equiv_refl _ (ComplexRaw.ofQComplex_valid _)

theorem polygonalPolynomialIntegralRaw_closed_equiv_zero
    (coefficients : List QComplex) (start : QComplex)
    (vertices : List QComplex) :
    (polygonalPolynomialIntegralRaw coefficients start
      (vertices ++ [start])).Equiv (ComplexRaw.ofQComplex QComplex.zero) := by
  rw [polygonalPolynomialIntegralRaw, polygonalPolynomialPrimitiveTo_closed]
  exact ComplexRaw.equiv_refl _ (ComplexRaw.ofQComplex_valid _)

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

/-- The finite certificate needed to promote a polygonal box computation to a
computable complex raw.  The three fields are exactly the project's
algorithmic validity obligations: every box is ordered, later stages refine
earlier ones, and every requested positive coordinate tolerance is eventually
met.  The certificate deliberately leaves those estimates as explicit finite
data rather than deriving them from completed-real convergence. -/
structure PolygonalIntegralCertificate
    (f : EntireBoxFunctionRaw) (vertices : List QComplex) where
  ordered : forall n, (polygonalIntegralBoxEntire f vertices n).Ordered
  nested : forall n m, n <= m ->
    QBox.NestedIn (polygonalIntegralBoxEntire f vertices m)
      (polygonalIntegralBoxEntire f vertices n)
  widths_shrink : ComplexRaw.WidthsShrinkToZero
    (polygonalIntegralBoxEntire f vertices)

theorem polygonalIntegralRawEntire_valid
    {f : EntireBoxFunctionRaw} {vertices : List QComplex}
    (certificate : PolygonalIntegralCertificate f vertices) :
    (polygonalIntegralRawEntire f vertices).Valid := by
  refine ⟨?_, ?_, certificate.widths_shrink⟩
  · intro n
    exact (QBox.ordered_iff_width_height_nonneg
      (polygonalIntegralBoxEntire f vertices n)).1
      (certificate.ordered n)
  · intro n m hnm
    have hnest := certificate.nested n m hnm
    exact ⟨hnest.1.1, hnest.2.1, hnest.1.2, hnest.2.2⟩

theorem PolygonalIntegralCertificate.precision_witness
    {f : EntireBoxFunctionRaw} {vertices : List QComplex}
    (certificate : PolygonalIntegralCertificate f vertices) (eps : QPos) :
    ∃ N : Nat, ∀ n : Nat, N <= n ->
      (polygonalIntegralBoxEntire f vertices n).width <= eps.val /\
      (polygonalIntegralBoxEntire f vertices n).height <= eps.val := by
  exact certificate.widths_shrink eps

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
