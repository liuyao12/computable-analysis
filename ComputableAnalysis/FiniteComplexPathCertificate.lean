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

theorem PolygonalLeftSumCertificate.of_stage_eq_point
    {f : FunctionRaw} {hEntire : forall z, f.domain z}
    {vertices : List QComplex} {evalPrecision : Nat -> Nat}
    (anchor : QComplex)
    (hcompute : forall n,
      (polygonalLeftSumRawEntire f hEntire vertices evalPrecision).compute n =
        QBox.point anchor) :
    PolygonalLeftSumCertificate f hEntire vertices evalPrecision := by
  refine
    { ordered := ?_
      nested := ?_
      widths_shrink := ?_ }
  · intro n
    rw [hcompute n]
    simp [QBox.Ordered, QBox.point, QComplex.le_def]
  · intro n m hnm
    rw [hcompute m, hcompute n]
    simp [QBox.NestedIn, QBox.point, QComplex.le_def]
  · intro eps
    refine ⟨0, ?_⟩
    intro n hn
    rw [hcompute n]
    simp [QBox.point, QBox.width, QBox.height] <;> grind

theorem constantClosedPolygonalLeftSumCertificate
    (c start : QComplex) (vertices : List QComplex)
    (evalPrecision : Nat -> Nat) :
    PolygonalLeftSumCertificate (FunctionRaw.exact (fun _ => c))
      (by intro z; change True; trivial)
      (start :: (vertices ++ [start])) evalPrecision := by
  apply PolygonalLeftSumCertificate.of_stage_eq_point QComplex.zero
  intro n
  cases n with
  | zero =>
      have hzero : forall xs : List QComplex,
          polygonalLeftSumEntire (FunctionRaw.exact (fun _ => c))
            (by intro z; change True; trivial) xs 0 (evalPrecision 0) =
            QBox.zero := by
        intro xs
        induction xs with
        | nil => rfl
        | cons x xs ih =>
            cases xs with
            | nil => rfl
            | cons y ys =>
                simp [polygonalLeftSumEntire, segmentLeftSumEntire,
                  segmentLeftSum, QBox.zero, QBox.add, QBox.point,
                  QComplex.zero, QComplex.add, ih] <;> grind
      exact hzero _
  | succ n =>
      exact polygonalLeftSum_constant_closed c start vertices (n + 1)
        (Nat.succ_pos n) (evalPrecision (n + 1))

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
    have hnest := @PolygonalLeftSumCertificate.nested f hEntire vertices
      evalPrecision certificate n m hnm
    exact ⟨hnest.1.1, hnest.2.1, hnest.1.2, hnest.2.2⟩

/-! A representation-level convergence certificate for polygonal integration.
The two algorithms need not share an evaluator or a rate: same-stage box
overlap, together with the two validity certificates, is the complete
computable obligation for identifying them. -/
structure PolygonalLeftSumIntegralOverlapCertificate
    (f : FunctionRaw) (hEntire : forall z, f.domain z)
    (boxFunction : EntireBoxFunctionRaw) (vertices : List QComplex)
    (evalPrecision : Nat -> Nat) where
  left_sum : PolygonalLeftSumCertificate f hEntire vertices evalPrecision
  interval_integral : PolygonalIntegralCertificate boxFunction vertices
  overlap : forall n,
    QBox.Overlaps
      ((polygonalLeftSumRawEntire f hEntire vertices evalPrecision).compute n)
      ((polygonalIntegralRawEntire boxFunction vertices).compute n)

def PolygonalLeftSumIntegralOverlapCertificate.leftRaw
    {f : FunctionRaw} {hEntire : forall z, f.domain z}
    {boxFunction : EntireBoxFunctionRaw} {vertices : List QComplex}
    {evalPrecision : Nat -> Nat}
    (_certificate : PolygonalLeftSumIntegralOverlapCertificate f hEntire
      boxFunction vertices evalPrecision) : ComplexRaw :=
  polygonalLeftSumRawEntire f hEntire vertices evalPrecision

def PolygonalLeftSumIntegralOverlapCertificate.intervalRaw
    {f : FunctionRaw} {hEntire : forall z, f.domain z}
    {boxFunction : EntireBoxFunctionRaw} {vertices : List QComplex}
    {evalPrecision : Nat -> Nat}
    (_certificate : PolygonalLeftSumIntegralOverlapCertificate f hEntire
      boxFunction vertices evalPrecision) : ComplexRaw :=
  polygonalIntegralRawEntire boxFunction vertices

theorem PolygonalLeftSumIntegralOverlapCertificate.leftRaw_valid
    {f : FunctionRaw} {hEntire : forall z, f.domain z}
    {boxFunction : EntireBoxFunctionRaw} {vertices : List QComplex}
    {evalPrecision : Nat -> Nat}
    (certificate : PolygonalLeftSumIntegralOverlapCertificate f hEntire
      boxFunction vertices evalPrecision) :
    certificate.leftRaw.Valid := by
  exact polygonalLeftSumRawEntire_valid certificate.left_sum

theorem PolygonalLeftSumIntegralOverlapCertificate.intervalRaw_valid
    {f : FunctionRaw} {hEntire : forall z, f.domain z}
    {boxFunction : EntireBoxFunctionRaw} {vertices : List QComplex}
    {evalPrecision : Nat -> Nat}
    (certificate : PolygonalLeftSumIntegralOverlapCertificate f hEntire
      boxFunction vertices evalPrecision) :
    certificate.intervalRaw.Valid := by
  exact polygonalIntegralRawEntire_valid certificate.interval_integral

theorem PolygonalLeftSumIntegralOverlapCertificate.equiv
    {f : FunctionRaw} {hEntire : forall z, f.domain z}
    {boxFunction : EntireBoxFunctionRaw} {vertices : List QComplex}
    {evalPrecision : Nat -> Nat}
    (certificate : PolygonalLeftSumIntegralOverlapCertificate f hEntire
      boxFunction vertices evalPrecision) :
    certificate.leftRaw.Equiv certificate.intervalRaw := by
  intro n
  exact (ComplexRaw.compareAt_overlap_iff
    certificate.leftRaw certificate.intervalRaw n n).2
    (certificate.overlap n)

theorem PolygonalLeftSumIntegralOverlapCertificate.equiv_of_interval_anchor
    {f : FunctionRaw} {hEntire : forall z, f.domain z}
    {boxFunction : EntireBoxFunctionRaw} {vertices : List QComplex}
    {evalPrecision : Nat -> Nat} (certificate :
      PolygonalLeftSumIntegralOverlapCertificate f hEntire boxFunction
        vertices evalPrecision) {anchor : ComplexRaw}
    (hanchor : anchor.Valid)
    (hinterval_anchor : certificate.intervalRaw.Equiv anchor) :
    certificate.leftRaw.Equiv anchor := by
  exact ComplexRaw.equiv_trans
    certificate.leftRaw_valid certificate.intervalRaw_valid hanchor
    certificate.equiv hinterval_anchor

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

/- A concrete representative for the complex polynomial FTC: the differential
`z dz` has zero exact displacement around the positively oriented rational unit
square.  The certificate stores only the finite vertex list and coefficient;
the endpoint cancellation is inherited from the generic polynomial theorem. -/
def unitSquareZDifferentialCertificate :
    FiniteClosedPolynomialPathCertificate where
  coefficients := [QComplex.one]
  start := ComplexPathIntegral.zero
  vertices := [ComplexPathIntegral.one,
    ComplexPathIntegral.onePlusI, ComplexPathIntegral.I]

theorem unitSquareZDifferentialCertificate_exactDisplacement_zero :
    unitSquareZDifferentialCertificate.exactDisplacement = QComplex.zero := by
  exact unitSquareZDifferentialCertificate.exactDisplacement_eq_zero

end ComplexPathIntegral
end ComputableAnalysis
