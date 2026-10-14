import ComputableAnalysis.ModularForms.CMOrbitLatticePowers163
import ComputableAnalysis.ModularForms.LatticeFiniteReindexing

/-! Fixed-factor distribution over executable finite represented sums. -/
namespace ComputableAnalysis.ModularForms
open RiemannHilbert

private theorem mappedSum_valid {α : Type} (f : α → ComplexRaw) (hf : ∀ a, (f a).Valid)
    (as : List α) : (LocalODE.sum (as.map f)).Valid := by
  apply LocalODE.sum_valid
  intro z hz
  obtain ⟨a,_,rfl⟩ := List.mem_map.mp hz
  exact hf a

theorem representedSum_factor {α : Type} (c : ComplexRaw) (hc : c.Valid)
    (f : α → ComplexRaw) (hf : ∀ a, (f a).Valid) (as : List α) :
    (LocalODE.sum (as.map (fun a => ComplexRaw.mul c (f a)))).Equiv
      (ComplexRaw.mul c (LocalODE.sum (as.map f))) := by
  induction as with
  | nil =>
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := ComplexRaw.ofQComplex_valid _)
      (hright := ComplexRaw.mul_valid hc (ComplexRaw.ofQComplex_valid _))
    change (0:ScalarAlgebra.Value)=ComplexRawQuotient.ofRaw c hc*0
    grind
  | cons a as ih =>
    have hv := mappedSum_valid f hf as
    have hm := mappedSum_valid (fun a => ComplexRaw.mul c (f a))
      (fun a => ComplexRaw.mul_valid hc (hf a)) as
    have hi := ComplexRawQuotient.ofRaw_eq_ofRaw
      (hleft := hm) (hright := ComplexRaw.mul_valid hc hv) ih
    rw [ComplexRawQuotient.ofRaw_mul _ _ hc hv] at hi
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := ComplexRaw.add_valid (ComplexRaw.mul_valid hc (hf a)) hm)
      (hright := ComplexRaw.mul_valid hc (ComplexRaw.add_valid (hf a) hv))
    change ComplexRawQuotient.ofRaw c hc*ComplexRawQuotient.ofRaw (f a) (hf a)+
      ComplexRawQuotient.ofRaw (LocalODE.sum (as.map (fun a => ComplexRaw.mul c (f a)))) hm=
      ComplexRawQuotient.ofRaw c hc*(ComplexRawQuotient.ofRaw (f a) (hf a)+
        ComplexRawQuotient.ofRaw (LocalODE.sum (as.map f)) hv)
    grind

theorem representedSum_map_equiv {α : Type} (as : List α) (f g : α → ComplexRaw)
    (he : ∀ a, (f a).Equiv (g a)) :
    (LocalODE.sum (as.map f)).Equiv (LocalODE.sum (as.map g)) := by
  induction as with
  | nil => exact ComplexRaw.equiv_refl _ (ComplexRaw.ofQComplex_valid _)
  | cons a as ih => exact ComplexRaw.add_equiv (he a) ih

end ComputableAnalysis.ModularForms
