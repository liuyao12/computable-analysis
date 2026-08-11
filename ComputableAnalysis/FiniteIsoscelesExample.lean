import ComputableAnalysis.RationalCircle

namespace ComputableAnalysis
namespace RationalCircle.Stage

/-! A concrete rational isosceles-triangle certificate for item 65. -/

theorem isosceles_3_4_equal_legs :
    segmentNormSq { x := 0, y := 3 } { x := 4, y := 0 } = 25 /\
      segmentNormSq { x := 0, y := 3 } { x := -4, y := 0 } = 25 := by
  native_decide

theorem isosceles_3_4_axis_orthogonal :
    dot { x := 0, y := 3 } { x := 4, y := 0 } = 0 := by
  native_decide

theorem isosceles_3_4_base_squared :
    segmentNormSq { x := 4, y := 0 } { x := -4, y := 0 } = 64 := by
  native_decide

theorem isosceles_3_4_certificate :
    segmentNormSq { x := 0, y := 3 } { x := 4, y := 0 } = 25 /\
      segmentNormSq { x := 0, y := 3 } { x := -4, y := 0 } = 25 /\
      dot { x := 0, y := 3 } { x := 4, y := 0 } = 0 /\
      segmentNormSq { x := 4, y := 0 } { x := -4, y := 0 } = 64 := by
  exact ⟨isosceles_3_4_equal_legs.1,
    isosceles_3_4_equal_legs.2,
    isosceles_3_4_axis_orthogonal,
    isosceles_3_4_base_squared⟩

theorem isosceles_5_12_certificate :
    segmentNormSq { x := 0, y := 5 } { x := 12, y := 0 } = 169 /\
      segmentNormSq { x := 0, y := 5 } { x := -12, y := 0 } = 169 /\
      dot { x := 0, y := 5 } { x := 12, y := 0 } = 0 /\
      segmentNormSq { x := 12, y := 0 } { x := -12, y := 0 } = 576 := by
  native_decide

theorem isosceles_7_24_certificate :
    segmentNormSq { x := 0, y := 7 } { x := 24, y := 0 } = 625 /\
      segmentNormSq { x := 0, y := 7 } { x := -24, y := 0 } = 625 /\
      dot { x := 0, y := 7 } { x := 24, y := 0 } = 0 /\
      segmentNormSq { x := 24, y := 0 } { x := -24, y := 0 } = 2304 := by
  native_decide

end RationalCircle.Stage
end ComputableAnalysis
