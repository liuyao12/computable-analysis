import ComputableAnalysis.Basic

namespace ComputableAnalysis

/-! A concrete finite rational witness for the triangle inequality (item 91). -/

theorem qabs_three_term_triangle_certificate :
    qabs ((-3 : Rat) + 4 + (-2)) <=
        qabs (-3 : Rat) + qabs 4 + qabs (-2 : Rat) /\
      qabs ((-3 : Rat) + 4 + (-2)) = 1 /\
      qabs (-3 : Rat) + qabs 4 + qabs (-2 : Rat) = 9 := by
  native_decide

theorem qabs_five_term_triangle_certificate :
    qabs (ratListSum [-3, 4, -2, 7, -5]) <=
        ratListAbsSum [-3, 4, -2, 7, -5] /\
      qabs (ratListSum [-3, 4, -2, 7, -5]) = 1 /\
      ratListAbsSum [-3, 4, -2, 7, -5] = 21 := by
  native_decide

/-! A reusable error-budget form for two perturbed rational values. -/

theorem qabs_perturbed_sub_le
    {x y e f δ ε : Rat}
    (he : qabs e ≤ δ) (hf : qabs f ≤ ε) :
    qabs ((x + e) - (y + f)) ≤ qabs (x - y) + δ + ε := by
  calc
    qabs ((x + e) - (y + f)) = qabs ((x - y) + (e - f)) := by
      congr 1
      grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm,
        Rat.add_left_comm]
    _ ≤ qabs (x - y) + qabs (e - f) := qabs_add_le _ _
    _ ≤ qabs (x - y) + (qabs e + qabs f) := by
      exact (Rat.add_le_add_left).2 (qabs_sub_le e f)
    _ ≤ qabs (x - y) + (δ + ε) := by
      exact (Rat.add_le_add_left).2 (rat_add_le_add he hf)
    _ = qabs (x - y) + δ + ε := by
      grind [Rat.add_assoc]

end ComputableAnalysis
