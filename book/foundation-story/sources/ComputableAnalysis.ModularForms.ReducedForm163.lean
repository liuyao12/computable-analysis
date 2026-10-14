import ComputableAnalysis.ModularForms.IntegerMatrices

/-! Exact finite classification of reduced positive forms of discriminant
minus 163. This is arithmetic input for the CM argument, not a j-value theorem. -/
namespace ComputableAnalysis.ModularForms

/-- Reduction includes the usual nonnegative boundary convention. -/
structure ReducedForm163 where
  a : Int
  b : Int
  c : Int
  positive : 0 < a
  lower : -a ≤ b
  upper : b ≤ a
  ordered : a ≤ c
  discriminant : 4*a*c-b*b=163
  boundary : b = -a → 0 ≤ b

theorem reducedForm163_a_bound (f : ReducedForm163) : f.a ≤ 7 := by
  have ha : 0 ≤ f.a := by have h := f.positive; omega
  have hprod : 0 ≤ (f.a-f.b)*(f.a+f.b) :=
    Int.mul_nonneg (by have h := f.upper; omega) (by have h := f.lower; omega)
  have hac : 0 ≤ f.a*(f.c-f.a) := Int.mul_nonneg ha (by have h := f.ordered; omega)
  have hdisc := f.discriminant
  have hs : 3*f.a*f.a ≤ 163 := by grind
  by_cases h : f.a ≤ 7
  · exact h
  · exfalso
    have h8 : 8 ≤ f.a := by omega
    have hsq : 0 ≤ (f.a-8)*(f.a+8) := Int.mul_nonneg (by omega) (by omega)
    grind

/-- The unique reduced form under the nonnegative boundary convention. -/
theorem reducedForm163_classification (f : ReducedForm163) :
    f.a=1 ∧ f.b=1 ∧ f.c=41 := by
  have hbound := reducedForm163_a_bound f
  obtain ⟨a,b,c,hpos,hlo,hhi,hord,hdisc,hboundary⟩ := f
  change a ≤ 7 at hbound
  change a=1 ∧ b=1 ∧ c=41
  have ha : a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 5 ∨ a = 6 ∨ a = 7 := by omega
  have hb : b = (-7) ∨ b = (-6) ∨ b = (-5) ∨ b = (-4) ∨ b = (-3) ∨ b = (-2) ∨ b = (-1) ∨ b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 ∨ b = 5 ∨ b = 6 ∨ b = 7 := by omega
  rcases ha with ha0 | ha1 | ha2 | ha3 | ha4 | ha5 | ha6 <;> rcases hb with hb0 | hb1 | hb2 | hb3 | hb4 | hb5 | hb6 | hb7 | hb8 | hb9 | hb10 | hb11 | hb12 | hb13 | hb14 <;>
    subst a <;> subst b <;> omega

def principalReducedForm163 : ReducedForm163 :=
  ⟨1,1,41,by decide,by decide,by decide,by decide,by decide,by omega⟩

theorem reducedForm163_unique (f : ReducedForm163) : f = principalReducedForm163 := by
  have h := reducedForm163_classification f
  cases f
  simp only at h
  rcases h with ⟨ha,hb,hc⟩
  subst_vars
  rfl

end ComputableAnalysis.ModularForms
