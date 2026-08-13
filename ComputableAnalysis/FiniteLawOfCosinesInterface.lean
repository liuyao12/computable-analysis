import ComputableAnalysis.RationalCircle

/-!
# Reusable finite squared law-of-cosines interface

The project keeps the law of cosines at the rational squared-length level.
This avoids choosing square roots while retaining the exact coordinate identity.
-/

namespace ComputableAnalysis
namespace RationalCircle
namespace Stage

structure FiniteLawOfCosinesCertificate where
  pointP : PiCirclePoint
  pointQ : PiCirclePoint
  squaredDistance : Rat
  squaredDistance_eq : squaredDistance = segmentNormSq pointP pointQ

theorem FiniteLawOfCosinesCertificate.identity
    (certificate : FiniteLawOfCosinesCertificate) :
    certificate.squaredDistance =
      normSq certificate.pointP + normSq certificate.pointQ -
        2 * dot certificate.pointP certificate.pointQ := by
  rw [certificate.squaredDistance_eq]
  exact segmentNormSq_law_of_cosines _ _

def finiteLawOfCosinesCertificate
    (pointP pointQ : PiCirclePoint) : FiniteLawOfCosinesCertificate where
  pointP := pointP
  pointQ := pointQ
  squaredDistance := segmentNormSq pointP pointQ
  squaredDistance_eq := rfl

end Stage
end RationalCircle
end ComputableAnalysis
