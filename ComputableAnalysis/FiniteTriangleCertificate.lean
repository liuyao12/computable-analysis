import ComputableAnalysis.Basic

namespace ComputableAnalysis

/-! A concrete finite rational witness for the triangle inequality (item 91). -/

theorem qabs_three_term_triangle_certificate :
    qabs ((-3 : Rat) + 4 + (-2)) <=
        qabs (-3 : Rat) + qabs 4 + qabs (-2 : Rat) /\
      qabs ((-3 : Rat) + 4 + (-2)) = 1 /\
      qabs (-3 : Rat) + qabs 4 + qabs (-2 : Rat) = 9 := by
  native_decide

end ComputableAnalysis
