import ComputableAnalysis.ModularForms.IntegralForm163

/-! Executable normalization of the middle coefficient before reduction. -/
namespace ComputableAnalysis.ModularForms

def IntegralForm163.normalizingShift (f : IntegralForm163) : Int :=
  (f.a-f.b)/(2*f.a)

def IntegralForm163.normalize (f : IntegralForm163) : IntegralForm163 :=
  f.translate f.normalizingShift

theorem IntegralForm163.normalize_a (f : IntegralForm163) : f.normalize.a=f.a := rfl

theorem IntegralForm163.normalize_middle (f : IntegralForm163) :
    -f.normalize.a < f.normalize.b ∧ f.normalize.b ≤ f.normalize.a := by
  have ha := f.positive
  have hpos : 0 < 2*f.a := by omega
  have hlo := Int.emod_nonneg (f.a-f.b) (show 2*f.a ≠ 0 by omega)
  have hhi := Int.emod_lt_of_pos (f.a-f.b) hpos
  have he := Int.mul_ediv_add_emod (f.a-f.b) (2*f.a)
  change -f.a < f.b+2*f.a*((f.a-f.b)/(2*f.a)) ∧
    f.b+2*f.a*((f.a-f.b)/(2*f.a)) ≤ f.a
  omega

theorem IntegralForm163.normalize_eval (f : IntegralForm163) (x y : Int) :
    f.normalize.eval x y=f.eval (x+f.normalizingShift*y) y :=
  f.translate_eval f.normalizingShift x y

/-- Once ordering holds, normalization produces a fully reduced form. -/
def IntegralForm163.normalizedReduced (f : IntegralForm163) (h : f.normalize.a ≤ f.normalize.c) :
    ReducedForm163 where
  a := f.normalize.a
  b := f.normalize.b
  c := f.normalize.c
  positive := f.normalize.positive
  lower := by have h := f.normalize_middle; omega
  upper := f.normalize_middle.2
  ordered := h
  discriminant := f.normalize.discriminant
  boundary := by have h := f.normalize_middle; omega

theorem IntegralForm163.ordered_normalization_classification (f : IntegralForm163)
    (h : f.normalize.a ≤ f.normalize.c) :
    f.normalize.a=1 ∧ f.normalize.b=1 ∧ f.normalize.c=41 :=
  reducedForm163_classification (f.normalizedReduced h)

/-- Normalize, then swap if necessary. Every recursive swap strictly
decreases the positive leading coefficient. -/
def IntegralForm163.reduce (f : IntegralForm163) : ReducedForm163 :=
  if h : f.normalize.a ≤ f.normalize.c then f.normalizedReduced h
  else f.normalize.swap.reduce
termination_by f.a.toNat
decreasing_by
  have hpos := f.positive
  have hcpos := f.normalize.swap.positive
  change 0 < f.normalize.c at hcpos
  have ha := f.normalize_a
  change f.normalize.c.toNat < f.a.toNat
  omega

theorem IntegralForm163.reduce_eq_principal (f : IntegralForm163) :
    f.reduce=principalReducedForm163 := reducedForm163_unique f.reduce

end ComputableAnalysis.ModularForms
