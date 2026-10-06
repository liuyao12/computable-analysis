import ComputableAnalysis.ModularForms.IntegerMatrices

/-! Rational identities underlying the represented upper-half-plane action.
These finite identities do not yet construct an action on represented inputs. -/
namespace ComputableAnalysis.ModularForms

namespace SL2Z

theorem determinant_rat (g : SL2Z) :
    (g.a : Rat)*(g.d : Rat)-(g.b : Rat)*(g.c : Rat)=1 := by
  exact_mod_cast g.determinant

/-- The affine numerator or denominator with integer coefficients. -/
def affine (a b : Int) (z : QComplex) : QComplex :=
  ⟨(a : Rat)*z.re+(b : Rat), (a : Rat)*z.im⟩

/-- The determinant controls the imaginary part before division. -/
theorem numerator_conjugate_imag (g : SL2Z) (z : QComplex) :
    (QComplex.mul (affine g.a g.b z) (QComplex.conj (affine g.c g.d z))).im =
      z.im := by
  have hd := g.determinant_rat
  change ((g.a : Rat)*z.re+(g.b : Rat))*(-((g.c : Rat)*z.im)) +
    ((g.a : Rat)*z.im)*((g.c : Rat)*z.re+(g.d : Rat))=z.im
  calc
    _ = ((g.a : Rat)*(g.d : Rat)-(g.b : Rat)*(g.c : Rat))*z.im := by grind
    _ = z.im := by rw [hd]; simp

private theorem square_nonnegative (x : Rat) : 0 ≤ x*x := by
  by_cases hx : 0 ≤ x
  · exact Rat.mul_nonneg hx hx
  · have hn : 0 ≤ -x := by grind
    have hh := Rat.mul_nonneg hn hn
    have he : (-x)*(-x)=x*x := by grind
    rw [he] at hh
    exact hh

private theorem square_positive (x : Rat) (hx : x ≠ 0) : 0 < x*x := by
  have hn := square_nonnegative x
  have he : x*x ≠ 0 := by
    intro h
    rcases Rat.mul_eq_zero.mp h with h | h <;> exact hx h
  exact Rat.lt_of_le_of_ne hn (Ne.symm he)

/-- The denominator is separated from zero at a rational upper-half-plane point. -/
theorem denominator_norm_positive (g : SL2Z) (z : QComplex) (hz : 0 < z.im) :
    0 < QComplex.normSq (affine g.c g.d z) := by
  have hd := g.determinant_rat
  change 0 < ((g.c : Rat)*z.re+(g.d : Rat))*((g.c : Rat)*z.re+(g.d : Rat)) +
    ((g.c : Rat)*z.im)*((g.c : Rat)*z.im)
  have hs₁ := square_nonnegative ((g.c : Rat)*z.re+(g.d : Rat))
  have hs₂ := square_nonnegative ((g.c : Rat)*z.im)
  by_cases hc : (g.c : Rat) = 0
  · have hn : (g.d : Rat) ≠ 0 := by
      intro h
      simp only [hc, h, Rat.mul_zero] at hd
      grind only
    have hp := square_positive (g.d : Rat) hn
    simpa only [hc, Rat.zero_mul, Rat.zero_add, Rat.add_zero] using hp
  · have hn : (g.c : Rat)*z.im ≠ 0 := by
      intro h
      rcases Rat.mul_eq_zero.mp h with h | h
      · exact hc h
      · exact (Rat.ne_of_gt hz) h
    have hp := square_positive ((g.c : Rat)*z.im) hn
    grind only

end SL2Z
end ComputableAnalysis.ModularForms
