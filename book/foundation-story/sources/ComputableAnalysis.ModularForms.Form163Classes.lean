import ComputableAnalysis.ModularForms.Form163MatrixAction

/-! Proper equivalence classes of positive integral forms of discriminant -163. -/
namespace ComputableAnalysis.ModularForms

/-- Proper equivalence uses an actual determinant-one integral change of variables. -/
def IntegralForm163.ProperEquivalent (f h : IntegralForm163) : Prop :=
  ∃ g : SL2Z, f.transform g = h

theorem IntegralForm163.properEquivalent_refl (f : IntegralForm163) :
    f.ProperEquivalent f := ⟨SL2Z.identity, f.transform_identity⟩

theorem IntegralForm163.properEquivalent_symm {f h : IntegralForm163}
    (he : f.ProperEquivalent h) : h.ProperEquivalent f := by
  obtain ⟨g, hg⟩ := he
  refine ⟨SL2Z.inverse g, ?_⟩
  rw [← hg, transform_compose, SL2Z.multiply_inverse, transform_identity]

theorem IntegralForm163.properEquivalent_trans {f h k : IntegralForm163}
    (hfh : f.ProperEquivalent h) (hhk : h.ProperEquivalent k) :
    f.ProperEquivalent k := by
  obtain ⟨g, hg⟩ := hfh
  obtain ⟨m, hm⟩ := hhk
  refine ⟨SL2Z.multiply g m, ?_⟩
  rw [← transform_compose, hg, hm]

/-- An executable matrix taking any supplied form to any other supplied form. -/
def IntegralForm163.equivalenceMatrix (f h : IntegralForm163) : SL2Z :=
  SL2Z.multiply f.reductionMatrix (SL2Z.inverse h.reductionMatrix)

theorem IntegralForm163.equivalenceMatrix_transform (f h : IntegralForm163) :
    f.transform (f.equivalenceMatrix h) = h := by
  unfold equivalenceMatrix
  rw [← transform_compose, reductionMatrix_transform]
  rw [← h.reductionMatrix_transform, transform_compose,
    SL2Z.multiply_inverse, transform_identity]

theorem IntegralForm163.properEquivalent_all (f h : IntegralForm163) :
    f.ProperEquivalent h := ⟨f.equivalenceMatrix h, f.equivalenceMatrix_transform h⟩

def integralForm163Setoid : Setoid IntegralForm163 where
  r := IntegralForm163.ProperEquivalent
  iseqv := ⟨IntegralForm163.properEquivalent_refl,
    IntegralForm163.properEquivalent_symm, IntegralForm163.properEquivalent_trans⟩

/-- The quotient is by proved integral matrix equivalence, not an analytic completion. -/
def ProperFormClass163 := Quotient integralForm163Setoid

def principalFormClass163 : ProperFormClass163 :=
  Quotient.mk integralForm163Setoid principalIntegralForm163

theorem properFormClass163_eq_principal (c : ProperFormClass163) :
    c = principalFormClass163 := by
  refine Quotient.inductionOn c ?_
  intro f
  exact Quotient.sound (f.properEquivalent_all principalIntegralForm163)

instance : Subsingleton ProperFormClass163 where
  allEq c d := (properFormClass163_eq_principal c).trans
    (properFormClass163_eq_principal d).symm

end ComputableAnalysis.ModularForms
