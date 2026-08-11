import ComputableAnalysis.ComplexPathIntegral

/-!
# Finite exactness for a constant differential on a closed polygonal path

This module packages the representation-first certificate for the finite
identity

`∫ c dz = c * (endpoint - start)`.

For a closed path the endpoint is represented by appending the starting point
to a finite list of rational-complex vertices.  Thus the exactness result is
purely finite algebra: it uses no limiting path, completed scalar field, or
analytic integral.
-/

namespace ComputableAnalysis
namespace ComplexPathIntegral

/-! A left-sum raw algorithm with its evaluator precision scheduled by stage. -/
def polygonalLeftSumRawEntire
    (f : FunctionRaw) (hEntire : forall z, f.domain z)
    (vertices : List QComplex) (evalPrecision : Nat -> Nat) : ComplexRaw where
  compute := fun n =>
    polygonalLeftSumEntire f hEntire vertices n (evalPrecision n)

structure PolygonalLeftSumCertificate
    (f : FunctionRaw) (hEntire : forall z, f.domain z)
    (vertices : List QComplex) (evalPrecision : Nat -> Nat) where
  ordered : forall n,
    (polygonalLeftSumRawEntire f hEntire vertices evalPrecision).compute n |>.Ordered
  nested : forall n m, n <= m ->
    QBox.NestedIn
      ((polygonalLeftSumRawEntire f hEntire vertices evalPrecision).compute m)
      ((polygonalLeftSumRawEntire f hEntire vertices evalPrecision).compute n)
  widths_shrink : ComplexRaw.WidthsShrinkToZero
    (polygonalLeftSumRawEntire f hEntire vertices evalPrecision).compute

theorem polygonalLeftSumRawEntire_valid
    {f : FunctionRaw} {hEntire : forall z, f.domain z}
    {vertices : List QComplex} {evalPrecision : Nat -> Nat}
    (certificate : PolygonalLeftSumCertificate f hEntire vertices evalPrecision) :
    (polygonalLeftSumRawEntire f hEntire vertices evalPrecision).Valid := by
  refine ⟨?_, ?_, certificate.widths_shrink⟩
  · intro n
    exact (QBox.ordered_iff_width_height_nonneg _).1
      (certificate.ordered n)
  · intro n m hnm
    have hnest := certificate.nested n m hnm
    exact ⟨hnest.1.1, hnest.2.1, hnest.1.2, hnest.2.2⟩

/-! The direct finite exactness theorem for a closed polygonal path. -/
theorem finiteConstantDifferentialExactness_closed
    (c start : QComplex) (vertices : List QComplex) :
    polygonalConstantDifferentialDisplacement c start
        (vertices ++ [start]) = QComplex.zero := by
  exact polygonalConstantDifferentialDisplacement_closed c start vertices

/-! The same endpoint-cancellation principle for every finite polynomial
differential represented by its rational-complex coefficient list. -/
theorem finitePolynomialDifferentialExactness_closed
    (coefficients : List QComplex) (start : QComplex)
    (vertices : List QComplex) :
    polygonalPolynomialPrimitiveTo coefficients start
        (vertices ++ [start]) = QComplex.zero := by
  exact polygonalPolynomialPrimitiveTo_closed coefficients start vertices

/-! A finite rational certificate for a closed polygonal path carrying the
constant differential `c dz`.  The endpoint is closed by construction. -/
structure FiniteClosedPolygonalPathCertificate where
  coefficient : QComplex
  start : QComplex
  vertices : List QComplex

namespace FiniteClosedPolygonalPathCertificate

def path (certificate : FiniteClosedPolygonalPathCertificate) : List QComplex :=
  certificate.vertices ++ [certificate.start]

def exactDisplacement
    (certificate : FiniteClosedPolygonalPathCertificate) : QComplex :=
  polygonalConstantDifferentialDisplacement certificate.coefficient
    certificate.start certificate.path

theorem endpoint (certificate : FiniteClosedPolygonalPathCertificate) :
    certificate.path.getLast? = some certificate.start := by
  simp [path]

theorem exactDisplacement_eq_zero
    (certificate : FiniteClosedPolygonalPathCertificate) :
    certificate.exactDisplacement = QComplex.zero := by
  exact finiteConstantDifferentialExactness_closed
    certificate.coefficient certificate.start certificate.vertices

end FiniteClosedPolygonalPathCertificate

structure FiniteClosedPolynomialPathCertificate where
  coefficients : List QComplex
  start : QComplex
  vertices : List QComplex

namespace FiniteClosedPolynomialPathCertificate

def path (certificate : FiniteClosedPolynomialPathCertificate) : List QComplex :=
  certificate.vertices ++ [certificate.start]

def exactDisplacement
    (certificate : FiniteClosedPolynomialPathCertificate) : QComplex :=
  polygonalPolynomialPrimitiveTo certificate.coefficients certificate.start
    certificate.path

theorem endpoint (certificate : FiniteClosedPolynomialPathCertificate) :
    certificate.path.getLast? = some certificate.start := by
  simp [path]

theorem exactDisplacement_eq_zero
    (certificate : FiniteClosedPolynomialPathCertificate) :
    certificate.exactDisplacement = QComplex.zero := by
  exact finitePolynomialDifferentialExactness_closed
    certificate.coefficients certificate.start certificate.vertices

end FiniteClosedPolynomialPathCertificate

end ComplexPathIntegral
end ComputableAnalysis
