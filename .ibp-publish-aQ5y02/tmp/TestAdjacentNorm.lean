import ComputableAnalysis.RationalCircle

namespace ComputableAnalysis.RationalCircle.Stage

example (S : Stage) (hS : 2 <= S.subdivisions) (k : Nat) :
    segmentNormSq (S.samplePoint k) (S.samplePoint (k + 1)) <= 1 := by
  let u := S.parameter k
  let v := S.parameter (k + 1)
  let h := 1 / (S.subdivisions : Rat)
  have hSpos : 0 < S.subdivisions := by omega
  have hstep : v - u = h := by
    dsimp [u, v, h]
    exact S.parameter_succ_sub k
  have hhpos : 0 < h := by
    dsimp [h]
    rw [Rat.div_def, Rat.one_mul]
    exact Rat.inv_pos.mpr ((Rat.natCast_pos).2 hSpos)
  have hhhalf : h <= (1 : Rat) / 2 := by
    dsimp [h]
    exact FTC.one_div_nat_antitone (by omega : 0 < 2) hSpos hS
  have hnum : 4 * h * h <= 1 := by
    have hsquare := sq_le_sq_of_nonneg_le (Rat.le_of_lt hhpos) hhhalf
    change h * h <= ((1 : Rat) / 2) * ((1 : Rat) / 2) at hsquare
    calc
      4 * h * h = 4 * (h * h) := by grind [Rat.mul_assoc]
      _ <= 4 * ((1 : Rat) / 2 * ((1 : Rat) / 2)) :=
        Rat.mul_le_mul_of_nonneg_left hsquare (by native_decide)
      _ = 1 := by native_decide
  have huone : 1 <= 1 + u * u := by
    have hsq := ratSquare_nonneg u
    grind
  have hvone : 1 <= 1 + v * v := by
    have hsq := ratSquare_nonneg v
    grind
  have hDpos : 0 < (1 + u * u) * (1 + v * v) :=
    Rat.mul_pos (one_add_square_pos u) (one_add_square_pos v)
  have hD : 1 <= (1 + u * u) * (1 + v * v) := by
    calc
      1 = 1 * 1 := by native_decide
      _ <= (1 + u * u) * 1 :=
        Rat.mul_le_mul_of_nonneg_right huone (by native_decide)
      _ <= (1 + u * u) * (1 + v * v) :=
        Rat.mul_le_mul_of_nonneg_left hvone (by grind)
  change segmentNormSq (point u) (point v) <= 1
  rw [point_segmentNormSq_formula]
  rw [hstep]
  apply Rat.le_of_mul_le_mul_right (c := (1 + u * u) * (1 + v * v))
  · rw [Rat.div_def]
    have hcancel : ((1 + u * u) * (1 + v * v))⁻¹ *
        ((1 + u * u) * (1 + v * v)) = 1 :=
      Rat.inv_mul_cancel _ (Rat.ne_of_gt hDpos)
    calc
      (4 * h * h * ((1 + u * u) * (1 + v * v))⁻¹) *
          ((1 + u * u) * (1 + v * v)) = 4 * h * h := by
        grind [Rat.mul_assoc, Rat.mul_comm]
      _ <= 1 := hnum
      _ <= 1 * ((1 + u * u) * (1 + v * v)) := by
        simpa using hD
  · exact hDpos

end ComputableAnalysis.RationalCircle.Stage
