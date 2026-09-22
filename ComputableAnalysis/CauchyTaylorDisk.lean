import ComputableAnalysis.CauchyTaylorCoefficients

/-! The radius-bearing public form of certified Cauchy series reconstruction.
The radius is a guaranteed disk of equality, not a claim that this is the
largest possible disk of holomorphic extension. -/

namespace ComputableAnalysis.CauchyTaylor

open QComplex

structure Disk where
  center : QComplex
  radius : Rat
  radius_pos : 0 < radius
  function : QComplex → ComplexRaw
  certificate : SeriesCertificate (fun w => function (add center (scaleRat radius w)))

namespace Disk

def coordinate (d : Disk) (z : QComplex) : QComplex :=
  scaleRat d.radius⁻¹ (sub z d.center)

theorem coordinate_inverse (d : Disk) (z : QComplex) :
    add d.center (scaleRat d.radius (d.coordinate z)) = z := by
  have hi := Rat.mul_inv_cancel d.radius (Rat.ne_of_gt d.radius_pos)
  cases z
  simp only [coordinate, scaleRat, sub, add, neg, QComplex.mk.injEq]
  constructor <;> grind only

theorem coordinate_norm_lt (d : Disk) {z : QComplex}
    (hz : normSq (sub z d.center) < d.radius*d.radius) : normSq (d.coordinate z) < 1 := by
  have hi := Rat.mul_inv_cancel d.radius (Rat.ne_of_gt d.radius_pos)
  have hp := Rat.mul_pos ((Rat.inv_pos).2 d.radius_pos) ((Rat.inv_pos).2 d.radius_pos)
  have hm := Rat.mul_lt_mul_of_pos_left hz hp
  have he : (d.radius⁻¹*d.radius⁻¹)*(d.radius*d.radius) = 1 := by
    calc
      _ = (d.radius*d.radius⁻¹)*(d.radius*d.radius⁻¹) := by grind only
      _ = 1 := by rw [hi, Rat.one_mul]
  simpa only [coordinate, normSq_scaleRat, he] using hm

/-- A rational radius between `|w|` and one, computed without square roots. -/
def innerRatio (d : Disk) (z : QComplex) : Rat := (1 + normSq (d.coordinate z)) / 2

theorem innerRatio_spec (d : Disk) {z : QComplex}
    (hz : normSq (sub z d.center) < d.radius*d.radius) :
    0 ≤ d.innerRatio z ∧ d.innerRatio z < 1 ∧ InDisk (d.coordinate z) (d.innerRatio z) := by
  have hs := d.coordinate_norm_lt hz
  have hn := normSq_nonneg (d.coordinate z)
  have hsq := rat_square_nonneg_basic (1 - normSq (d.coordinate z))
  unfold innerRatio InDisk
  constructor
  · grind
  constructor <;> grind

/-- Taylor/Cauchy moment series in the normalized coordinate `(z-a)/R`.
Its coefficients are the boundary moments; usual unnormalized coefficients
are these moments divided by `R^k`. No value of `function` is read at runtime. -/
def series (d : Disk) (z : QComplex) : ComplexRaw :=
  d.certificate.series (d.coordinate z) (d.innerRatio z)

theorem series_valid (d : Disk) {z : QComplex}
    (hz : normSq (sub z d.center) < d.radius*d.radius) : (d.series z).Valid := by
  have h := d.innerRatio_spec hz
  exact d.certificate.cauchy.series_valid h.1 h.2.1 h.2.2

/-- Exact equality throughout the certified open disk, with all approximation
schedules hidden inside the independent series computation. -/
theorem eq_series (d : Disk) {z : QComplex}
    (hz : normSq (sub z d.center) < d.radius*d.radius) :
    (d.function z).Equiv (d.series z) := by
  have h := d.innerRatio_spec hz
  have he := d.certificate.eq_series h.1 h.2.1 h.2.2
  rw [d.coordinate_inverse z] at he
  exact he

theorem realPart_eq_series (d : Disk) {z : QComplex}
    (hz : normSq (sub z d.center) < d.radius*d.radius) :
    (d.function z).realPart.Equiv (d.series z).realPart :=
  ComplexRaw.realPart_equiv (d.eq_series hz)

theorem imagPart_eq_series (d : Disk) {z : QComplex}
    (hz : normSq (sub z d.center) < d.radius*d.radius) :
    (d.function z).imagPart.Equiv (d.series z).imagPart :=
  ComplexRaw.imagPart_equiv (d.eq_series hz)

end Disk
end ComputableAnalysis.CauchyTaylor
