import ComputableAnalysis.ModularForms.Form163Normalization

/-! An executable determinant-one matrix certifying the complete reduction. -/
namespace ComputableAnalysis.ModularForms

def translationMatrix (n : Int) : SL2Z := ⟨1,n,0,1,by grind⟩

def IntegralForm163.reductionMatrix (f : IntegralForm163) : SL2Z :=
  if h : f.normalize.a ≤ f.normalize.c then translationMatrix f.normalizingShift
  else SL2Z.multiply (translationMatrix f.normalizingShift)
    (SL2Z.multiply SL2Z.S f.normalize.swap.reductionMatrix)
termination_by f.a.toNat
decreasing_by
  have hpos := f.positive
  have hcpos := f.normalize.swap.positive
  change 0 < f.normalize.c at hcpos
  have ha := f.normalize_a
  change f.normalize.c.toNat < f.a.toNat
  omega

theorem IntegralForm163.reductionMatrix_eval (f : IntegralForm163) (x y : Int) :
    f.eval (f.reductionMatrix.a*x+f.reductionMatrix.b*y)
      (f.reductionMatrix.c*x+f.reductionMatrix.d*y) =
      f.reduce.a*x*x+f.reduce.b*x*y+f.reduce.c*y*y := by
  by_cases h : f.normalize.a ≤ f.normalize.c
  · rw [reductionMatrix,reduce]
    simp only [dif_pos h,translationMatrix,Int.one_mul,Int.zero_mul,Int.zero_add]
    change f.eval (x+f.normalizingShift*y) y =
      f.normalize.a*x*x+f.normalize.b*x*y+f.normalize.c*y*y
    exact (f.normalize_eval x y).symm
  · have ih := f.normalize.swap.reductionMatrix_eval x y
    rw [reductionMatrix,reduce]
    simp only [dif_neg h]
    let r := f.normalize.swap.reductionMatrix
    have he := f.normalize_eval (-(r.c*x+r.d*y)) (r.a*x+r.b*y)
    have hs := f.normalize.swap_eval (r.a*x+r.b*y) (r.c*x+r.d*y)
    change f.eval
      ((SL2Z.multiply (translationMatrix f.normalizingShift) (SL2Z.multiply SL2Z.S r)).a*x+
        (SL2Z.multiply (translationMatrix f.normalizingShift) (SL2Z.multiply SL2Z.S r)).b*y)
      ((SL2Z.multiply (translationMatrix f.normalizingShift) (SL2Z.multiply SL2Z.S r)).c*x+
        (SL2Z.multiply (translationMatrix f.normalizingShift) (SL2Z.multiply SL2Z.S r)).d*y) = _
    simp only [SL2Z.multiply,translationMatrix,SL2Z.S]
    have hx : (1*(0*r.a+(-1)*r.c)+f.normalizingShift*(1*r.a+0*r.c))*x+
        (1*(0*r.b+(-1)*r.d)+f.normalizingShift*(1*r.b+0*r.d))*y =
        -(r.c*x+r.d*y)+f.normalizingShift*(r.a*x+r.b*y) := by grind
    have hy : (0*(0*r.a+(-1)*r.c)+1*(1*r.a+0*r.c))*x+
        (0*(0*r.b+(-1)*r.d)+1*(1*r.b+0*r.d))*y = r.a*x+r.b*y := by grind
    rw [hx,hy,← he,← hs]
    exact ih
termination_by f.a.toNat
decreasing_by
  have hpos := f.positive
  have hcpos := f.normalize.swap.positive
  change 0 < f.normalize.c at hcpos
  have ha := f.normalize_a
  change f.normalize.c.toNat < f.a.toNat
  omega

theorem IntegralForm163.principal_change_of_variables (f : IntegralForm163) (x y : Int) :
    f.eval (f.reductionMatrix.a*x+f.reductionMatrix.b*y)
      (f.reductionMatrix.c*x+f.reductionMatrix.d*y) = x*x+x*y+41*y*y := by
  have h := f.reductionMatrix_eval x y
  rw [f.reduce_eq_principal] at h
  simpa only [principalReducedForm163,Int.one_mul] using h

/-- Every positive integral form at this discriminant is properly equivalent
to the principal form, witnessed by an executable determinant-one matrix. -/
theorem IntegralForm163.exists_principal_matrix (f : IntegralForm163) :
    ∃ g : SL2Z, ∀ x y : Int,
      f.eval (g.a*x+g.b*y) (g.c*x+g.d*y)=x*x+x*y+41*y*y :=
  ⟨f.reductionMatrix,f.principal_change_of_variables⟩

end ComputableAnalysis.ModularForms
