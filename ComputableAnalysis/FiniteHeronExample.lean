import ComputableAnalysis.RationalCircle

/-!
# A finite Heron certificate for a 5-5-6 triangle

This is a second worked instance of the Heron interface.  The coordinates
`(-3,0)`, `(3,0)`, and `(0,4)` give side lengths `6,5,5` and area `12`.
All displayed data are rational; the square-root output is only transported
through the existing finite rational-square certificate.
-/

namespace ComputableAnalysis

namespace RationalCircle

def heronFiveFiveSixLeft : PiCirclePoint := { x := -3, y := 0 }
def heronFiveFiveSixRight : PiCirclePoint := { x := 3, y := 0 }
def heronFiveFiveSixApex : PiCirclePoint := { x := 0, y := 4 }

theorem heron_five_five_six_coordinate_certificate :
    triangleTwiceArea heronFiveFiveSixLeft heronFiveFiveSixRight
        heronFiveFiveSixApex = 24 /\
      (heronFiveFiveSixRight.x - heronFiveFiveSixLeft.x) ^ 2 = 36 /\
      (heronFiveFiveSixApex.x - heronFiveFiveSixLeft.x) ^ 2 +
          (heronFiveFiveSixApex.y - heronFiveFiveSixLeft.y) ^ 2 = 25 /\
      (heronFiveFiveSixApex.x - heronFiveFiveSixRight.x) ^ 2 +
          (heronFiveFiveSixApex.y - heronFiveFiveSixRight.y) ^ 2 = 25 /\
      heronProduct 5 5 6 =
        (triangleTwiceArea heronFiveFiveSixLeft heronFiveFiveSixRight
          heronFiveFiveSixApex / 2) ^ 2 := by
  native_decide

theorem heron_five_five_six_product :
    heronProduct 5 5 6 = 144 := by
  native_decide

theorem heron_five_five_six_area_raw_equiv_twelve :
    (heronAreaRaw 5 5 6 (by native_decide)).Equiv
      (RealRaw.ofRat 12) := by
  apply heronAreaRaw_equiv_of_square 5 5 6 12 (by native_decide)
  native_decide

def heronThirteenFourteenFifteenLeft : PiCirclePoint := { x := 0, y := 0 }
def heronThirteenFourteenFifteenRight : PiCirclePoint := { x := 14, y := 0 }
def heronThirteenFourteenFifteenApex : PiCirclePoint := { x := 5, y := 12 }

theorem heron_thirteen_fourteen_fifteen_coordinate_certificate :
    triangleTwiceArea heronThirteenFourteenFifteenLeft
        heronThirteenFourteenFifteenRight heronThirteenFourteenFifteenApex = 168 /\
      (heronThirteenFourteenFifteenRight.x -
          heronThirteenFourteenFifteenLeft.x) ^ 2 = 196 /\
      (heronThirteenFourteenFifteenApex.x -
          heronThirteenFourteenFifteenLeft.x) ^ 2 +
          (heronThirteenFourteenFifteenApex.y -
            heronThirteenFourteenFifteenLeft.y) ^ 2 = 169 /\
      (heronThirteenFourteenFifteenApex.x -
          heronThirteenFourteenFifteenRight.x) ^ 2 +
          (heronThirteenFourteenFifteenApex.y -
            heronThirteenFourteenFifteenRight.y) ^ 2 = 225 /\
      heronProduct 13 14 15 =
        (triangleTwiceArea heronThirteenFourteenFifteenLeft
          heronThirteenFourteenFifteenRight heronThirteenFourteenFifteenApex / 2) ^ 2 := by
  native_decide

theorem heron_thirteen_fourteen_fifteen_product :
    heronProduct 13 14 15 = 7056 := by
  native_decide

theorem heron_thirteen_fourteen_fifteen_area_raw_equiv_eighty_four :
    (heronAreaRaw 13 14 15 (by native_decide)).Equiv
      (RealRaw.ofRat 84) := by
  apply heronAreaRaw_equiv_of_square 13 14 15 84 (by native_decide)
  native_decide

end RationalCircle

end ComputableAnalysis
