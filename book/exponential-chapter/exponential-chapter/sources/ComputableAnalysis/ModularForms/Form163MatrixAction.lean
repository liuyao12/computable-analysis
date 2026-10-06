import ComputableAnalysis.ModularForms.Form163ReductionMatrix

/-! Proper matrix action on integral forms of discriminant -163. -/
namespace ComputableAnalysis.ModularForms

def IntegralForm163.transform (f : IntegralForm163) (g : SL2Z) : IntegralForm163 where
  a := f.eval g.a g.c
  b := 2*f.a*g.a*g.b+f.b*(g.a*g.d+g.b*g.c)+2*f.c*g.c*g.d
  c := f.eval g.b g.d
  positive := by
    apply f.eval_positive
    have hd := g.determinant
    by_cases ha : g.a=0
    · right
      intro hc
      rw [ha,hc] at hd
      omega
    · exact Or.inl ha
  discriminant := by
    have hf := f.discriminant
    have hg := g.determinant
    unfold eval
    have h :
        4*(f.a*g.a*g.a+f.b*g.a*g.c+f.c*g.c*g.c)*
          (f.a*g.b*g.b+f.b*g.b*g.d+f.c*g.d*g.d)-
          (2*f.a*g.a*g.b+f.b*(g.a*g.d+g.b*g.c)+2*f.c*g.c*g.d)*
          (2*f.a*g.a*g.b+f.b*(g.a*g.d+g.b*g.c)+2*f.c*g.c*g.d) =
        (4*f.a*f.c-f.b*f.b)*(g.a*g.d-g.b*g.c)*(g.a*g.d-g.b*g.c) := by grind
    rw [h,hf,hg]
    decide

theorem IntegralForm163.transform_eval (f : IntegralForm163) (g : SL2Z) (x y : Int) :
    (f.transform g).eval x y=f.eval (g.a*x+g.b*y) (g.c*x+g.d*y) := by
  unfold transform eval
  grind

def principalIntegralForm163 : IntegralForm163 := ⟨1,1,41,by decide,by decide⟩

theorem IntegralForm163.ext (f h : IntegralForm163)
    (ha : f.a=h.a) (hb : f.b=h.b) (hc : f.c=h.c) : f=h := by
  cases f
  cases h
  simp_all

theorem IntegralForm163.ext_eval (f h : IntegralForm163)
    (he : ∀ x y : Int, f.eval x y=h.eval x y) : f=h := by
  have ha := he 1 0
  have hc := he 0 1
  have hb := he 1 1
  unfold eval at ha hb hc
  apply IntegralForm163.ext <;> omega

theorem IntegralForm163.transform_identity (f : IntegralForm163) :
    f.transform SL2Z.identity=f := by
  apply IntegralForm163.ext_eval
  intro x y
  rw [transform_eval]
  simp only [SL2Z.identity,Int.one_mul,Int.zero_mul,Int.add_zero,Int.zero_add]

theorem IntegralForm163.transform_compose (f : IntegralForm163) (g h : SL2Z) :
    (f.transform g).transform h=f.transform (SL2Z.multiply g h) := by
  apply IntegralForm163.ext_eval
  intro x y
  rw [transform_eval,transform_eval,transform_eval]
  simp only [SL2Z.multiply]
  congr 1 <;> grind

theorem IntegralForm163.reductionMatrix_transform (f : IntegralForm163) :
    f.transform f.reductionMatrix=principalIntegralForm163 := by
  have h (x y : Int) := (f.transform_eval f.reductionMatrix x y).trans
    (f.principal_change_of_variables x y)
  have ha := h 1 0
  have hc := h 0 1
  have hb := h 1 1
  unfold eval at ha hb hc
  apply IntegralForm163.ext
  · change (f.transform f.reductionMatrix).a=1
    omega
  · change (f.transform f.reductionMatrix).b=1
    omega
  · change (f.transform f.reductionMatrix).c=41
    omega

end ComputableAnalysis.ModularForms
