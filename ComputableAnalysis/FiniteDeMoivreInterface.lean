import ComputableAnalysis.ComplexCircleBridge

/-!
# Reusable finite De Moivre interface

De Moivre's formula is represented by natural powers in the rational circle
group.  The identity is algebraic and finite; angle and completed-complex
interpretations are separate bridges.
-/

namespace ComputableAnalysis
namespace RationalCircle
namespace Trigonometry

structure FiniteDeMoivreCertificate where
  pointP : PiCirclePoint
  pointQ : PiCirclePoint
  exponent : Nat
  productPower : PiCirclePoint
  productPower_eq : productPower = pointPow (pointMul pointP pointQ) exponent
  separatePower_eq : productPower = pointMul (pointPow pointP exponent)
    (pointPow pointQ exponent)

theorem FiniteDeMoivreCertificate.power_identity
    (certificate : FiniteDeMoivreCertificate) :
    certificate.productPower = pointMul
      (pointPow certificate.pointP certificate.exponent)
      (pointPow certificate.pointQ certificate.exponent) :=
  certificate.separatePower_eq

def finiteDeMoivreCertificate
    (pointP pointQ : PiCirclePoint) (exponent : Nat) :
    FiniteDeMoivreCertificate where
  pointP := pointP
  pointQ := pointQ
  exponent := exponent
  productPower := pointPow (pointMul pointP pointQ) exponent
  productPower_eq := rfl
  separatePower_eq := pointPow_mul pointP pointQ exponent

end Trigonometry
end RationalCircle
end ComputableAnalysis
