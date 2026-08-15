import ComputableAnalysis.RationalCircle

/-!
# A finite Green theorem certificate

For a rational rectangle, the circulation of the one-form x dy around its
counterclockwise boundary equals its signed area.  This is the rectangular
polygon core of Green's theorem: every quantity is a finite rational sum, with
no measure or completed line integral.
-/

namespace ComputableAnalysis

def greenTriangleBoundary
    (p q r : PiCirclePoint) : Rat :=
  (p.x + q.x) / 2 * (q.y - p.y) +
    (q.x + r.x) / 2 * (r.y - q.y) +
    (r.x + p.x) / 2 * (p.y - r.y)

theorem greenTriangleBoundary_eq_half_shoelace
    (p q r : PiCirclePoint) :
    greenTriangleBoundary p q r =
      RationalCircle.triangleTwiceArea p q r / 2 := by
  unfold greenTriangleBoundary RationalCircle.triangleTwiceArea
  grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm,
    Rat.mul_add, Rat.add_mul, Rat.mul_assoc, Rat.mul_comm]

def greenRectangleBoundary (left right bottom top : Rat) : Rat :=
  right * (top - bottom) + left * (bottom - top)

def greenRectangleArea (left right bottom top : Rat) : Rat :=
  (right - left) * (top - bottom)

structure FiniteGreenRectangleCertificate where
  left : Rat
  right : Rat
  bottom : Rat
  top : Rat
  horizontal_order : left <= right
  vertical_order : bottom <= top

def FiniteGreenRectangleCertificate.boundary
    (certificate : FiniteGreenRectangleCertificate) : Rat :=
  greenRectangleBoundary certificate.left certificate.right
    certificate.bottom certificate.top

def FiniteGreenRectangleCertificate.area
    (certificate : FiniteGreenRectangleCertificate) : Rat :=
  greenRectangleArea certificate.left certificate.right
    certificate.bottom certificate.top

theorem greenRectangleBoundary_eq_area
    (left right bottom top : Rat) :
    greenRectangleBoundary left right bottom top =
      greenRectangleArea left right bottom top := by
  unfold greenRectangleBoundary greenRectangleArea
  grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm,
    Rat.mul_add, Rat.add_mul, Rat.mul_assoc, Rat.mul_comm]

theorem greenRectangleBoundary_split_horizontal
    (left middle right bottom top : Rat) :
    greenRectangleBoundary left middle bottom top +
        greenRectangleBoundary middle right bottom top =
      greenRectangleBoundary left right bottom top := by
  unfold greenRectangleBoundary
  grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm,
    Rat.mul_add, Rat.add_mul, Rat.mul_assoc, Rat.mul_comm]

theorem greenRectangleBoundary_split_vertical
    (left right bottom middle top : Rat) :
    greenRectangleBoundary left right bottom middle +
        greenRectangleBoundary left right middle top =
      greenRectangleBoundary left right bottom top := by
  unfold greenRectangleBoundary
  grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm,
    Rat.mul_add, Rat.add_mul, Rat.mul_assoc, Rat.mul_comm]

theorem greenRectangleArea_split_horizontal
    (left middle right bottom top : Rat) :
    greenRectangleArea left middle bottom top +
        greenRectangleArea middle right bottom top =
      greenRectangleArea left right bottom top := by
  unfold greenRectangleArea
  grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm,
    Rat.mul_add, Rat.add_mul, Rat.mul_assoc, Rat.mul_comm]

theorem greenRectangleArea_split_vertical
    (left right bottom middle top : Rat) :
    greenRectangleArea left right bottom middle +
        greenRectangleArea left right middle top =
      greenRectangleArea left right bottom top := by
  unfold greenRectangleArea
  grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm,
    Rat.mul_add, Rat.add_mul, Rat.mul_assoc, Rat.mul_comm]

theorem FiniteGreenRectangleCertificate.boundary_eq_area
    (certificate : FiniteGreenRectangleCertificate) :
    certificate.boundary = certificate.area := by
  exact greenRectangleBoundary_eq_area
    certificate.left certificate.right certificate.bottom certificate.top

def finiteGreenRectangleCertificate
    (left right bottom top : Rat)
    (horizontal_order : left <= right)
    (vertical_order : bottom <= top) :
    FiniteGreenRectangleCertificate :=
  { left := left
    right := right
    bottom := bottom
    top := top
    horizontal_order := horizontal_order
    vertical_order := vertical_order }

theorem finiteGreenRectangleCertificate_unit :
    (finiteGreenRectangleCertificate 0 1 0 1
      (by native_decide) (by native_decide)).boundary =
      (finiteGreenRectangleCertificate 0 1 0 1
        (by native_decide) (by native_decide)).area := by
  exact FiniteGreenRectangleCertificate.boundary_eq_area _

end ComputableAnalysis
