import ComputableAnalysis.ModularForms.Form163Classes

/-! Executable primitivity witnesses for forms of discriminant -163. -/
namespace ComputableAnalysis.ModularForms

theorem IntegralForm163.reductionMatrix_represents_one (f : IntegralForm163) :
    f.eval f.reductionMatrix.a f.reductionMatrix.c = 1 := by
  have h := f.principal_change_of_variables 1 0
  simpa only [Int.mul_one, Int.mul_zero, Int.add_zero] using h

/-- The first column of the reduction matrix gives a coefficient Bezout witness. -/
theorem IntegralForm163.coefficient_bezout (f : IntegralForm163) :
    f.a*(f.reductionMatrix.a*f.reductionMatrix.a) +
      f.b*(f.reductionMatrix.a*f.reductionMatrix.c) +
      f.c*(f.reductionMatrix.c*f.reductionMatrix.c) = 1 := by
  have h := f.reductionMatrix_represents_one
  unfold eval at h
  grind

/-- Primitivity stated without choosing a gcd normalization convention. -/
def IntegralForm163.Primitive (f : IntegralForm163) : Prop :=
  ∀ d : Int, d ∣ f.a → d ∣ f.b → d ∣ f.c → d ∣ 1

theorem IntegralForm163.primitive (f : IntegralForm163) : f.Primitive := by
  intro d ha hb hc
  obtain ⟨u, hu⟩ := ha
  obtain ⟨v, hv⟩ := hb
  obtain ⟨w, hw⟩ := hc
  refine ⟨u*(f.reductionMatrix.a*f.reductionMatrix.a) +
    v*(f.reductionMatrix.a*f.reductionMatrix.c) +
    w*(f.reductionMatrix.c*f.reductionMatrix.c), ?_⟩
  have h := f.coefficient_bezout
  rw [hu, hv, hw] at h
  grind

end ComputableAnalysis.ModularForms
