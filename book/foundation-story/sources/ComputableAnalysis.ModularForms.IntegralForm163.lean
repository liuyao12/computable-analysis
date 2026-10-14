import ComputableAnalysis.ModularForms.ReducedForm163

/-! Positive integral forms and exact reduction moves at discriminant -163. -/
namespace ComputableAnalysis.ModularForms

private theorem square_nonnegative (v : Int) : 0 ≤ v*v := by
  by_cases h : 0 ≤ v
  · exact Int.mul_nonneg h h
  · exact Int.mul_nonneg_of_nonpos_of_nonpos (by omega) (by omega)

private theorem square_positive (v : Int) (hv : v ≠ 0) : 0 < v*v := by
  by_cases h : 0 < v
  · exact Int.mul_pos h h
  · exact Int.mul_pos_of_neg_of_neg (by omega) (by omega)

structure IntegralForm163 where
  a : Int
  b : Int
  c : Int
  positive : 0 < a
  discriminant : 4*a*c-b*b=163

def IntegralForm163.eval (f : IntegralForm163) (x y : Int) : Int :=
  f.a*x*x+f.b*x*y+f.c*y*y

theorem IntegralForm163.completed_square (f : IntegralForm163) (x y : Int) :
    4*f.a*f.eval x y=(2*f.a*x+f.b*y)*(2*f.a*x+f.b*y)+163*y*y := by
  have h := f.discriminant
  unfold eval
  grind

theorem IntegralForm163.eval_positive (f : IntegralForm163) (x y : Int)
    (hxy : x ≠ 0 ∨ y ≠ 0) : 0 < f.eval x y := by
  have ha := f.positive
  have hs := f.completed_square x y
  have hq : 0 ≤ (2*f.a*x+f.b*y)*(2*f.a*x+f.b*y) := square_nonnegative _
  have hy : 0 ≤ y*y := square_nonnegative _
  have hpos : 0 < (2*f.a*x+f.b*y)*(2*f.a*x+f.b*y)+163*y*y := by
    by_cases hzero : y=0
    · subst y
      have hx : x ≠ 0 := by omega
      have ha0 : f.a ≠ 0 := by omega
      have hp : 0 < (2*f.a*x)*(2*f.a*x) := by
        have hn : 2*f.a*x ≠ 0 := Int.mul_ne_zero (Int.mul_ne_zero (by decide) ha0) hx
        exact square_positive _ hn
      grind
    · have hypos : 0 < y*y := square_positive y hzero
      grind
  by_cases h : 0 < f.eval x y
  · exact h
  · have hm : 4*f.a*f.eval x y ≤ 0 :=
      Int.mul_nonpos_of_nonneg_of_nonpos (by omega) (by omega)
    omega

def IntegralForm163.translate (f : IntegralForm163) (n : Int) : IntegralForm163 where
  a := f.a
  b := f.b+2*f.a*n
  c := f.a*n*n+f.b*n+f.c
  positive := f.positive
  discriminant := by have h := f.discriminant; grind

theorem IntegralForm163.translate_eval (f : IntegralForm163) (n x y : Int) :
    (f.translate n).eval x y=f.eval (x+n*y) y := by
  unfold translate eval
  grind

def IntegralForm163.swap (f : IntegralForm163) : IntegralForm163 where
  a := f.c
  b := -f.b
  c := f.a
  positive := by
    have h := f.eval_positive 0 1 (by omega)
    unfold eval at h
    grind
  discriminant := by have h := f.discriminant; grind

theorem IntegralForm163.swap_eval (f : IntegralForm163) (x y : Int) :
    f.swap.eval x y=f.eval (-y) x := by unfold swap eval; grind

end ComputableAnalysis.ModularForms
