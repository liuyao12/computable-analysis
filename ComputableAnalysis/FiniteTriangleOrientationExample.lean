import ComputableAnalysis.RationalCircle

/-!
# A worked rational triangle-orientation certificate

The points `(1,0)`, `(0,1)`, and `(-1,0)` give a positive signed twice-area
certificate using only rational coordinates.
-/

namespace ComputableAnalysis

namespace RationalCircle

def orientationPointP : PiCirclePoint := { x := 1, y := 0 }
def orientationPointQ : PiCirclePoint := { x := 0, y := 1 }
def orientationPointR : PiCirclePoint := { x := -1, y := 0 }

theorem orientation_triangle_twice_area :
    triangleTwiceArea orientationPointP orientationPointQ orientationPointR = 2 := by
  native_decide

theorem orientation_triangle_cyclic :
    triangleTwiceArea orientationPointP orientationPointQ orientationPointR =
      triangleTwiceArea orientationPointQ orientationPointR orientationPointP := by
  exact triangleTwiceArea_cyclic _ _ _

theorem orientation_triangle_swap_neg :
    triangleTwiceArea orientationPointP orientationPointQ orientationPointR =
      -triangleTwiceArea orientationPointP orientationPointR orientationPointQ := by
  exact triangleTwiceArea_swap_neg _ _ _

theorem orientation_triangle_positive :
    0 < triangleTwiceArea orientationPointP orientationPointQ orientationPointR := by
  rw [orientation_triangle_twice_area]
  native_decide

end RationalCircle

end ComputableAnalysis
