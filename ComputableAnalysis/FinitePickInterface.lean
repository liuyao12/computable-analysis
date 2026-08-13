import ComputableAnalysis.FinitePickCertificate

/-!
# Reusable finite Pick interface

Pick's formula is represented by finite lattice data: three vertices, the
shoelace area, gcd edge contributions, and a supplied interior-point count.
The certificate checks the resulting rational identity without invoking a
continuous region or a completed geometric measure.
-/

namespace ComputableAnalysis

structure FiniteLatticePoint where
  x : Int
  y : Int

def FiniteLatticePoint.toRat (point : FiniteLatticePoint) : PiCirclePoint :=
  { x := point.x, y := point.y }

structure FinitePickTriangleCertificate where
  vertexA : FiniteLatticePoint
  vertexB : FiniteLatticePoint
  vertexC : FiniteLatticePoint
  area : Rat
  boundary : Nat
  interior : Nat
  area_eq : area =
    qabs (RationalCircle.triangleTwiceArea vertexA.toRat vertexB.toRat vertexC.toRat) / 2
  boundary_eq : boundary =
    Nat.gcd (Int.natAbs (vertexB.x - vertexA.x))
        (Int.natAbs (vertexB.y - vertexA.y)) +
      Nat.gcd (Int.natAbs (vertexC.x - vertexB.x))
        (Int.natAbs (vertexC.y - vertexB.y)) +
      Nat.gcd (Int.natAbs (vertexA.x - vertexC.x))
        (Int.natAbs (vertexA.y - vertexC.y))
  pick_identity : area = (interior : Rat) + (boundary : Rat) / 2 - 1

theorem FinitePickTriangleCertificate.identity
    (certificate : FinitePickTriangleCertificate) :
    certificate.area = (certificate.interior : Rat) +
      (certificate.boundary : Rat) / 2 - 1 :=
  certificate.pick_identity

def finitePickTriangleCertificate
    (vertexA vertexB vertexC : FiniteLatticePoint) (area : Rat) (boundary interior : Nat)
    (area_eq : area =
      qabs (RationalCircle.triangleTwiceArea vertexA.toRat vertexB.toRat vertexC.toRat) / 2)
    (boundary_eq : boundary =
      Nat.gcd (Int.natAbs (vertexB.x - vertexA.x))
          (Int.natAbs (vertexB.y - vertexA.y)) +
        Nat.gcd (Int.natAbs (vertexC.x - vertexB.x))
          (Int.natAbs (vertexC.y - vertexB.y)) +
        Nat.gcd (Int.natAbs (vertexA.x - vertexC.x))
          (Int.natAbs (vertexA.y - vertexC.y)))
    (pick_identity : area = (interior : Rat) + (boundary : Rat) / 2 - 1) :
    FinitePickTriangleCertificate where
  vertexA := vertexA
  vertexB := vertexB
  vertexC := vertexC
  area := area
  boundary := boundary
  interior := interior
  area_eq := area_eq
  boundary_eq := boundary_eq
  pick_identity := pick_identity

end ComputableAnalysis
