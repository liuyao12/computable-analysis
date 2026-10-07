import ComputableAnalysis.ModularForms.SquareSquaredPoleCancellation

/-! Affine numerator residue algebra for arbitrary valid represented coefficients. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions PDE.CauchyContour

theorem squarePole_position_times_squared (edge : HalfEdge) (R u : Rat) :
    QComplex.mul (QComplex.scaleRat R (point edge u)) (squaredPolePullback edge R u)=
      linearPolePullback edge R u := by
  simp only [squaredPolePullback,linearPolePullback,QComplex.mul,QComplex.scaleRat,QComplex.mk.injEq]
  constructor <;> grind only

def affinePoleDensity (A d : Scalar) (edge : HalfEdge) (R u : Rat) : Scalar :=
  scalarProduct
    (affineMidpointModel A d (rationalRectangleScalar (QComplex.scaleRat R (point edge u))))
    (rationalRectangleScalar (squaredPolePullback edge R u))

theorem affinePoleDensity_decomposition (A d : Scalar) (edge : HalfEdge) (R u : Rat) :
    (affinePoleDensity A d edge R u).val.Equiv
      (scalarSum (scalarProduct A (rationalRectangleScalar (squaredPolePullback edge R u)))
        (scalarProduct d (rationalRectangleScalar (linearPolePullback edge R u)))).val := by
  let q := QComplex.scaleRat R (point edge u)
  let k := squaredPolePullback edge R u
  let l := linearPolePullback edge R u
  have hq := RationalReciprocal.raw_mul_constants q k
  have he : QComplex.mul q k=l := squarePole_position_times_squared edge R u
  rw [he] at hq
  have hv := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid (ofQComplex_valid q) (ofQComplex_valid k))
    (hright := ofQComplex_valid l) hq
  rw [ComplexRawQuotient.ofRaw_mul _ _ (ofQComplex_valid q) (ofQComplex_valid k)] at hv
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (affinePoleDensity A d edge R u).property)
    (hright := (scalarSum (scalarProduct A (rationalRectangleScalar k))
      (scalarProduct d (rationalRectangleScalar l))).property)
  let X := gridScalarValue A
  let D := gridScalarValue d
  let Q := ComplexRawQuotient.ofRaw (ofQComplex q) (ofQComplex_valid q)
  let K := ComplexRawQuotient.ofRaw (ofQComplex k) (ofQComplex_valid k)
  let L := ComplexRawQuotient.ofRaw (ofQComplex l) (ofQComplex_valid l)
  change Q*K=L at hv
  change (X+D*Q)*K=X*K+D*L
  grind only

def affinePoleEdgeList (A d : Scalar) (R u : Rat) : List HalfEdge → Scalar
  | [] => ⟨zero,ofQComplex_valid _⟩
  | e::es => scalarSum (affinePoleDensity A d e R u) (affinePoleEdgeList A d R u es)

def poleCoefficientEdgeList (A : Scalar) (kernel : HalfEdge → QComplex) : List HalfEdge → Scalar
  | [] => ⟨zero,ofQComplex_valid _⟩
  | e::es => scalarSum (scalarProduct A (rationalRectangleScalar (kernel e)))
      (poleCoefficientEdgeList A kernel es)

theorem affinePoleEdgeList_decomposition (A d : Scalar) (R u : Rat) (es : List HalfEdge) :
    (affinePoleEdgeList A d R u es).val.Equiv
      (scalarSum (poleCoefficientEdgeList A (fun e => squaredPolePullback e R u) es)
        (poleCoefficientEdgeList d (fun e => linearPolePullback e R u) es)).val := by
  induction es with
  | nil =>
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := (affinePoleEdgeList A d R u []).property)
      (hright := (scalarSum (poleCoefficientEdgeList A (fun e => squaredPolePullback e R u) [])
        (poleCoefficientEdgeList d (fun e => linearPolePullback e R u) [])).property)
    change (0:ScalarAlgebra.Value)=0+0
    grind only
  | cons e es ih =>
    have h := add_equiv (affinePoleDensity_decomposition A d e R u) ih
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := (affinePoleEdgeList A d R u (e::es)).property)
      (hright := (scalarSum (poleCoefficientEdgeList A (fun e => squaredPolePullback e R u) (e::es))
        (poleCoefficientEdgeList d (fun e => linearPolePullback e R u) (e::es))).property)
    have hv := ComplexRawQuotient.ofRaw_eq_ofRaw
      (hleft := (affinePoleEdgeList A d R u (e::es)).property)
      (hright := (scalarSum
        (scalarSum (scalarProduct A (rationalRectangleScalar (squaredPolePullback e R u)))
          (scalarProduct d (rationalRectangleScalar (linearPolePullback e R u))))
        (scalarSum (poleCoefficientEdgeList A (fun e => squaredPolePullback e R u) es)
          (poleCoefficientEdgeList d (fun e => linearPolePullback e R u) es))).property) h
    change gridScalarValue (affinePoleEdgeList A d R u (e::es))=_ at hv ⊢
    rw [hv]
    let X := gridScalarValue (scalarProduct A (rationalRectangleScalar (squaredPolePullback e R u)))
    let Y := gridScalarValue (scalarProduct d (rationalRectangleScalar (linearPolePullback e R u)))
    let S := gridScalarValue (poleCoefficientEdgeList A (fun e => squaredPolePullback e R u) es)
    let T := gridScalarValue (poleCoefficientEdgeList d (fun e => linearPolePullback e R u) es)
    change (X+Y)+(S+T)=(X+S)+(Y+T)
    grind only

end ComputableAnalysis.ModularForms
