import ComputableAnalysis.RiemannHilbert.ContourFixedRectangleInvariance
import ComputableAnalysis.RiemannHilbert.ContourDisplacedExamples

/-! Constructed fixed-rectangle affine and reciprocal clients. Their interior
poles may be arbitrary represented values, with equivalent nonliteral names. -/
namespace ComputableAnalysis.RiemannHilbert.RectangularContour.FixedRectangleExamples
open ComplexRaw FunctionTheory DomainFunctions LocalODE
set_option autoImplicit false

def affineContour (a d : Scalar) (J : QInterval × QInterval) (b : Scalar)
    (hb : RectanglePoleInterior J b) : Nat → Scalar :=
  normalizedFixedRectangleCauchyContour (DomainFunctions.affine a d) J (fun _ _ => trivial) b hb

theorem affineContour_converges (a d : Scalar) (J : QInterval × QInterval) (b : Scalar)
    (hb : RectanglePoleInterior J b) : Converges (affineContour a d J b hb) (scalarSum a (scalarProduct d b)) :=
  normalizedFixedRectangleCauchyContour_converges _ (DomainFunctions.affine_holomorphic a d) J
    (fun _ _ => trivial) b hb

theorem affineContour_limit_identity (a d : Scalar) (J : QInterval × QInterval) (b : Scalar)
    (hb : RectanglePoleInterior J b) (u : Scalar) (hu : Converges (affineContour a d J b hb) u) :
    u≈scalarSum a (scalarProduct d b) :=
  normalizedFixedRectangleCauchyContour_limit_identity _ (DomainFunctions.affine_holomorphic a d) J
    (fun _ _ => trivial) b hb u hu

def unitRectangle : QInterval × QInterval := (⟨-1,1⟩,⟨-1,1⟩)
def unitPole : Scalar := rationalRectangleScalar ⟨1/4,0⟩
theorem unitPole_inside : RectanglePoleInterior unitRectangle unitPole :=
  ⟨⟨1/8,by decide +kernel⟩,rationalRectangle_represented_mem _ _ (by decide +kernel)⟩

def asymmetricPole : Scalar := DisplacedExamples.asymmetricName ⟨1/4,0⟩
theorem asymmetricPole_agreement : asymmetricPole≈unitPole := DisplacedExamples.asymmetricName_agreement _
theorem asymmetricPole_inside : RectanglePoleInterior unitRectangle asymmetricPole :=
  rectanglePoleInterior_congr unitRectangle unitPole asymmetricPole (equiv_symm asymmetricPole_agreement) unitPole_inside

def geometricRectangle : QInterval × QInterval := (⟨-1/256,1/256⟩,⟨-1/256,1/256⟩)

theorem geometricRectangle_interior (z : Scalar) (hz : representedRectangleContains geometricRectangle z) :
    interior CauchyGeometricExample.radius z := by
  have hs := representedRectangle_small geometricRectangle z (1/128)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) hz
  exact ⟨1/128,by decide +kernel,by decide +kernel,hs⟩

theorem geometricRectangle_domain : ∀ z, representedRectangleContains geometricRectangle z →
    CauchyGeometricExample.analyticFunction.domain z :=
  fun z hz => CauchyGeometricExample.included z (geometricRectangle_interior z hz)

def geometricContour (b : Scalar) (hb : RectanglePoleInterior geometricRectangle b) : Nat → Scalar :=
  normalizedFixedRectangleCauchyContour CauchyGeometricExample.analyticFunction geometricRectangle
    geometricRectangle_domain b hb

theorem geometricContour_converges (b : Scalar) (hb : RectanglePoleInterior geometricRectangle b) :
    Converges (geometricContour b hb)
      (RepresentedReciprocal.inverse (CauchyGeometricExample.denominator b)
        (CauchyGeometricExample.denominator_nonzero b
          (geometricRectangle_interior b (rectanglePoleInterior_mem geometricRectangle b hb)))) :=
  normalizedFixedRectangleCauchyContour_converges _ CauchyGeometricExample.analyticHolomorphic geometricRectangle
    geometricRectangle_domain b hb

theorem geometricContour_limit_identity (b : Scalar) (hb : RectanglePoleInterior geometricRectangle b)
    (u : Scalar) (hu : Converges (geometricContour b hb) u) :
    u≈RepresentedReciprocal.inverse (CauchyGeometricExample.denominator b)
      (CauchyGeometricExample.denominator_nonzero b
        (geometricRectangle_interior b (rectanglePoleInterior_mem geometricRectangle b hb))) :=
  normalizedFixedRectangleCauchyContour_limit_identity _ CauchyGeometricExample.analyticHolomorphic geometricRectangle
    geometricRectangle_domain b hb u hu

def geometricPole : Scalar := rationalRectangleScalar ⟨1/2048,-1/2048⟩
theorem geometricPole_inside : RectanglePoleInterior geometricRectangle geometricPole :=
  ⟨⟨1/4096,by decide +kernel⟩,rationalRectangle_represented_mem _ _ (by decide +kernel)⟩

end ComputableAnalysis.RiemannHilbert.RectangularContour.FixedRectangleExamples
