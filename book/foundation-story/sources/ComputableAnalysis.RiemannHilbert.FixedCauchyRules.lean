import ComputableAnalysis.RiemannHilbert.CauchyLocalReconstruction

/-! Executable, kernel-checked Cauchy data for every fixed finite rational
rule. These are concrete rational functions, not a general Cauchy formula. -/
namespace ComputableAnalysis.RiemannHilbert.FixedCauchyRules
open CauchyTaylor QComplex
set_option autoImplicit false

def certificate (ps : Rule) : SeriesCertificate (fun z => ComplexRaw.ofQComplex (cauchySample ps z)) where
  cauchy := {
    rules := fun _ => ps
    massBound := mass ps
    mass_nonneg := mass_nonneg ps
    mass_le := fun _ => Rat.le_refl
    quadratureBound := fun _ => 0
    quadrature_nonneg := fun _ => Rat.le_refl
    valid := fun _ _ _ _ _ => ComplexRaw.ofQComplex_valid _
    encloses := by
      intro z r hr hr1 hz n
      simp only [QBox.NestedIn,QBox.expand,QBox.point,ComplexRaw.ofQComplex,
        CertifiedComplexApproximation.rate,QComplex.le_def,Rat.div_def,
        Rat.zero_mul,Rat.sub_eq_add_neg,Rat.neg_zero,Rat.add_zero]
      grind only }
  moments := {
    bound := fun _ => 0
    nonneg := fun _ => Rat.le_refl
    future := by
      intro k i j hij
      simp only [normBound,sub,add,neg,CertifiedComplexApproximation.rate,Rat.div_def,Rat.zero_mul]
      simp [qabs,Rat.add_neg_cancel,Rat.add_zero] }

theorem coefficient_agreement (ps : Rule) (k : Nat) :
    ((certificate ps).coefficient k).Equiv (ComplexRaw.ofQComplex (coefficientSample ps k)) := by
  intro n
  apply (ComplexRaw.compareAt_overlap_iff _ _ n n).2
  have h := (certificate ps).moments.coefficient_contains_sample k n
  exact ⟨h.1,h.2⟩

def reciprocalRule : Rule := [⟨one,by decide +kernel,one⟩]

theorem reciprocal_sample (z : QComplex) : cauchySample reciprocalRule z=kernel z := by
  simp only [cauchySample,reciprocalRule,List.foldr_cons,List.foldr_nil,
    mul_one_cert,one_mul_cert,add_zero_cert]

theorem reciprocal_coefficient (k : Nat) : coefficientSample reciprocalRule k=one := by
  have hp : natPow one k=one := by
    induction k with
    | zero => rfl
    | succ k ih => rw [natPow,ih,mul_one_cert]
  simp only [coefficientSample,reciprocalRule,List.foldr_cons,List.foldr_nil,
    hp,one_mul_cert,add_zero_cert]

end ComputableAnalysis.RiemannHilbert.FixedCauchyRules
