import ComputableAnalysis.RiemannHilbert.ContourDerivativeNormalized
import ComputableAnalysis.RiemannHilbert.ContourFixedRectangleExamples

/-! Constructed affine and nonpolynomial first-moment clients. Both the
coefficients and the interior poles may be arbitrary represented values. -/
namespace ComputableAnalysis.RiemannHilbert.RectangularContour.DerivativeExamples
open ComplexRaw FunctionTheory DomainFunctions
open FixedRectangleExamples
set_option autoImplicit false

def affineDerivativeContour (a d : Scalar) (J : QInterval × QInterval) (b : Scalar)
    (hb : RectanglePoleInterior J b) : Nat → Scalar :=
  normalizedFixedRectangleDerivativeContour (DomainFunctions.affine a d) J (fun _ _ => trivial) b hb

theorem affineDerivativeContour_converges (a d : Scalar) (J : QInterval × QInterval) (b : Scalar)
    (hb : RectanglePoleInterior J b) : Converges (affineDerivativeContour a d J b hb) d :=
  normalizedFixedRectangleDerivativeContour_converges _ (DomainFunctions.affine_holomorphic a d) J
    (fun _ _ => trivial) b hb

theorem affineDerivativeContour_limit_identity (a d : Scalar) (J : QInterval × QInterval) (b : Scalar)
    (hb : RectanglePoleInterior J b) (u : Scalar) (hu : Converges (affineDerivativeContour a d J b hb) u) : u≈d :=
  normalizedFixedRectangleDerivativeContour_limit_identity _ (DomainFunctions.affine_holomorphic a d) J
    (fun _ _ => trivial) b hb u hu

def geometricDerivative (b : Scalar) (hb : RectanglePoleInterior geometricRectangle b) : Scalar :=
  let v := CauchyGeometricExample.analyticFunction.eval b (geometricRectangle_domain b
    (rectanglePoleInterior_mem geometricRectangle b hb))
  scalarProduct v v

theorem geometricDerivative_agreement (b : Scalar) (hb : RectanglePoleInterior geometricRectangle b) :
    CauchyGeometricExample.analyticHolomorphic.derivative b (geometricRectangle_domain b
      (rectanglePoleInterior_mem geometricRectangle b hb))≈geometricDerivative b hb := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (CauchyGeometricExample.analyticHolomorphic.derivative b (geometricRectangle_domain b
      (rectanglePoleInterior_mem geometricRectangle b hb))).property) (hright := (geometricDerivative b hb).property)
  let R := gridScalarValue (CauchyGeometricExample.analyticFunction.eval b (geometricRectangle_domain b
    (rectanglePoleInterior_mem geometricRectangle b hb)))
  change (-(R*R))*(-1)=R*R
  grind only

def geometricDerivativeContour (b : Scalar) (hb : RectanglePoleInterior geometricRectangle b) : Nat → Scalar :=
  normalizedFixedRectangleDerivativeContour CauchyGeometricExample.analyticFunction geometricRectangle
    geometricRectangle_domain b hb

theorem geometricDerivativeContour_converges (b : Scalar) (hb : RectanglePoleInterior geometricRectangle b) :
    Converges (geometricDerivativeContour b hb) (geometricDerivative b hb) :=
  converge_limit_congr _ _ _ (normalizedFixedRectangleDerivativeContour_converges _
    CauchyGeometricExample.analyticHolomorphic geometricRectangle geometricRectangle_domain b hb)
    (geometricDerivative_agreement b hb)

theorem geometricDerivativeContour_limit_identity (b : Scalar) (hb : RectanglePoleInterior geometricRectangle b)
    (u : Scalar) (hu : Converges (geometricDerivativeContour b hb) u) : u≈geometricDerivative b hb :=
  converge_unique _ _ _ hu (geometricDerivativeContour_converges b hb)

end ComputableAnalysis.RiemannHilbert.RectangularContour.DerivativeExamples
