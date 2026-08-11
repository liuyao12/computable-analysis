import ComputableAnalysis.RationalCircle

/-!
# A finite Pick-theorem certificate

This module records one exact lattice triangle.  Its shoelace area, primitive
edge contributions, boundary count, and interior count satisfy Pick's
identity entirely by rational and natural-number computation.
-/

namespace ComputableAnalysis

def pickTriangleA : PiCirclePoint := { x := 0, y := 0 }
def pickTriangleB : PiCirclePoint := { x := 4, y := 0 }
def pickTriangleC : PiCirclePoint := { x := 0, y := 3 }

def pickTriangleArea : Rat :=
  qabs (RationalCircle.triangleTwiceArea
    pickTriangleA pickTriangleB pickTriangleC) / 2

def pickTriangleBoundary : Nat :=
  Nat.gcd 4 0 + Nat.gcd 4 3 + Nat.gcd 0 3

def pickTriangleInterior : Nat := 3

theorem pickTriangle_twice_area :
    RationalCircle.triangleTwiceArea
      pickTriangleA pickTriangleB pickTriangleC = 12 := by
  native_decide

theorem pickTriangle_area : pickTriangleArea = 6 := by
  native_decide

theorem pickTriangle_boundary : pickTriangleBoundary = 8 := by
  native_decide

theorem pickTriangle_interior : pickTriangleInterior = 3 := by
  native_decide

theorem pickTriangle_pick_identity :
    pickTriangleArea = (pickTriangleInterior : Rat) +
      (pickTriangleBoundary : Rat) / 2 - 1 := by
  native_decide

theorem pickTriangle_certificate :
    pickTriangleArea = 6 /\
      pickTriangleBoundary = 8 /\
      pickTriangleInterior = 3 /\
      pickTriangleArea = (pickTriangleInterior : Rat) +
        (pickTriangleBoundary : Rat) / 2 - 1 := by
  exact ⟨pickTriangle_area, pickTriangle_boundary, pickTriangle_interior,
    pickTriangle_pick_identity⟩

/-! A second triangle changes both the area and the edge-gcd pattern. -/

def pickTriangleTwoA : PiCirclePoint := { x := 0, y := 0 }
def pickTriangleTwoB : PiCirclePoint := { x := 5, y := 0 }
def pickTriangleTwoC : PiCirclePoint := { x := 0, y := 2 }

def pickTriangleTwoArea : Rat :=
  qabs (RationalCircle.triangleTwiceArea
    pickTriangleTwoA pickTriangleTwoB pickTriangleTwoC) / 2

def pickTriangleTwoBoundary : Nat :=
  Nat.gcd 5 0 + Nat.gcd 5 2 + Nat.gcd 0 2

def pickTriangleTwoInterior : Nat := 2

theorem pickTriangleTwo_certificate :
    pickTriangleTwoArea = 5 /\
      pickTriangleTwoBoundary = 8 /\
      pickTriangleTwoInterior = 2 /\
      pickTriangleTwoArea = (pickTriangleTwoInterior : Rat) +
        (pickTriangleTwoBoundary : Rat) / 2 - 1 := by
  native_decide

/-! A non-axis-aligned triangle exercises the full edge-gcd boundary count. -/

def pickTriangleThreeA : PiCirclePoint := { x := 0, y := 0 }
def pickTriangleThreeB : PiCirclePoint := { x := 4, y := 1 }
def pickTriangleThreeC : PiCirclePoint := { x := 1, y := 4 }

def pickTriangleThreeArea : Rat :=
  qabs (RationalCircle.triangleTwiceArea
    pickTriangleThreeA pickTriangleThreeB pickTriangleThreeC) / 2

def pickTriangleThreeBoundary : Nat :=
  Nat.gcd 4 1 + Nat.gcd 3 3 + Nat.gcd 1 4

def pickTriangleThreeInterior : Nat := 6

theorem pickTriangleThree_certificate :
    pickTriangleThreeArea = 15 / 2 /\
      pickTriangleThreeBoundary = 5 /\
      pickTriangleThreeInterior = 6 /\
      pickTriangleThreeArea = (pickTriangleThreeInterior : Rat) +
        (pickTriangleThreeBoundary : Rat) / 2 - 1 := by
  native_decide

/-! A larger triangle with non-primitive coordinate edges. -/

def pickTriangleFourA : PiCirclePoint := { x := 0, y := 0 }
def pickTriangleFourB : PiCirclePoint := { x := 6, y := 0 }
def pickTriangleFourC : PiCirclePoint := { x := 2, y := 5 }

def pickTriangleFourArea : Rat :=
  qabs (RationalCircle.triangleTwiceArea
    pickTriangleFourA pickTriangleFourB pickTriangleFourC) / 2

def pickTriangleFourBoundary : Nat :=
  Nat.gcd 6 0 + Nat.gcd 4 5 + Nat.gcd 2 5

def pickTriangleFourInterior : Nat := 12

theorem pickTriangleFour_certificate :
    pickTriangleFourArea = 15 /\
      pickTriangleFourBoundary = 8 /\
      pickTriangleFourInterior = 12 /\
      pickTriangleFourArea = (pickTriangleFourInterior : Rat) +
        (pickTriangleFourBoundary : Rat) / 2 - 1 := by
  native_decide

end ComputableAnalysis
