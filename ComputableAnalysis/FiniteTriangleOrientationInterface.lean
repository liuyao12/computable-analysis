import ComputableAnalysis.RationalCircle

/-!
# Reusable finite triangle-orientation interface

The angle-sum benchmark is represented by its rational signed-area core.
Orientation, cyclic relabelling, and reversal are exact determinant
computations; angle-valued semantics are a separate bridge.
-/

namespace ComputableAnalysis
namespace RationalCircle

structure FiniteTriangleOrientationCertificate where
  pointP : PiCirclePoint
  pointQ : PiCirclePoint
  pointR : PiCirclePoint
  twiceArea : Rat
  twiceArea_eq : twiceArea = triangleTwiceArea pointP pointQ pointR
  positive : 0 < twiceArea

theorem FiniteTriangleOrientationCertificate.oriented
    (certificate : FiniteTriangleOrientationCertificate) :
    0 < triangleTwiceArea certificate.pointP certificate.pointQ certificate.pointR := by
  rw [← certificate.twiceArea_eq]
  exact certificate.positive

def finiteTriangleOrientationCertificate
    (pointP pointQ pointR : PiCirclePoint)
    (positive : 0 < triangleTwiceArea pointP pointQ pointR) :
    FiniteTriangleOrientationCertificate where
  pointP := pointP
  pointQ := pointQ
  pointR := pointR
  twiceArea := triangleTwiceArea pointP pointQ pointR
  twiceArea_eq := rfl
  positive := positive

end RationalCircle
end ComputableAnalysis
