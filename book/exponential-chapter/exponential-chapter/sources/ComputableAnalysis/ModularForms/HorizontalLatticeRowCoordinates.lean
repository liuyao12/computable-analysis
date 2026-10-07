import ComputableAnalysis.ModularForms.HorizontalLatticePointValues
import ComputableAnalysis.ModularForms.SymmetricLatticeCoordinates

/-! Symmetric coordinate assembly of the actual horizontal row, with the origin omitted. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory QuadraticOrder163

private theorem mapped_valid {α : Type} (f : α → ComplexRaw) (hf : ∀ a, (f a).Valid) (xs : List α) :
    (LocalODE.sum (xs.map f)).Valid := by
  apply LocalODE.sum_valid
  intro z hz
  obtain ⟨a,_,rfl⟩ := List.mem_map.mp hz
  exact hf a

private def sumClass {α : Type} (f : α → ComplexRaw) (hf : ∀ a, (f a).Valid) (xs : List α) : ScalarAlgebra.Value :=
  ComplexRawQuotient.ofRaw (LocalODE.sum (xs.map f)) (mapped_valid f hf xs)

private theorem filter_zero_class {α : Type} (f : α → ComplexRaw) (hf : ∀ a, (f a).Valid)
    (keep : α → Bool) (hzero : ∀ a, keep a=false → (f a).Equiv ComplexRaw.zero) (xs : List α) :
    sumClass f hf xs=sumClass f hf (xs.filter keep) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    cases hk : keep a with
    | false =>
      simp only [List.filter_cons,hk,Bool.false_eq_true,if_false]
      have ha := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := hf a) (hright := ofQComplex_valid _) (hzero a hk)
      change ComplexRawQuotient.ofRaw (f a) (hf a)+sumClass f hf xs=sumClass f hf (xs.filter keep)
      change ComplexRawQuotient.ofRaw (f a) (hf a)=0 at ha
      rw [ha,ih]
      exact ComplexRawQuotient.zero_add _
    | true =>
      simp only [List.filter_cons,hk,if_true]
      change ComplexRawQuotient.ofRaw (f a) (hf a)+sumClass f hf xs=
        ComplexRawQuotient.ofRaw (f a) (hf a)+sumClass f hf (xs.filter keep)
      rw [ih]

/-- The actual filtered horizontal row agrees with its symmetric coordinate sum;
the omitted origin contributes the proved zero term. -/
theorem upperLatticeFiniteRow_horizontal_class (z : Scalar) (hz : InUpperHalfPlane z.val) (k N : Nat) :
    ComplexRawQuotient.ofRaw (upperLatticeFiniteRow z hz k N 0).val
      (upperLatticeFiniteRow z hz k N 0).property=
      symmetricLatticeSum (fun x => ComplexRawQuotient.ofRaw (upperPointPower z hz k ⟨x,0⟩)
        (upperPointPower_valid z hz k ⟨x,0⟩)) N := by
  let f := upperPointPower z hz k
  have hf := upperPointPower_valid z hz k
  let keep := fun u : QuadraticOrder163 => decide (u≠QuadraticOrder163.zero)
  have hzero u (hu : keep u=false) : (f u).Equiv ComplexRaw.zero := by
    have he : u=QuadraticOrder163.zero := by
      apply Classical.byContradiction
      intro hn
      have hh : keep u=true := by
        simp only [keep,decide_eq_true_eq]
        exact hn
      rw [hh] at hu
      contradiction
    subst u
    simp only [f,upperPointPower,dif_neg (show ¬QuadraticOrder163.zero≠QuadraticOrder163.zero from fun h => h rfl)]
    exact equiv_refl _ (ofQComplex_valid _)
  have h := filter_zero_class f hf keep hzero ((latticeCoordinates N).map (fun x => (⟨x,0⟩ : QuadraticOrder163)))
  have he := h.symm
  rw [sumClass] at he
  change ComplexRawQuotient.ofRaw (upperLatticeFiniteRow z hz k N 0).val
      (upperLatticeFiniteRow z hz k N 0).property=
    ComplexRawQuotient.ofRaw (LocalODE.sum (((latticeCoordinates N).map (fun x => (⟨x,0⟩ : QuadraticOrder163))).map f))
      (mapped_valid f hf _) at he
  simp only [List.map_map] at he
  exact he.trans (representedSum_latticeCoordinates (fun x => f ⟨x,0⟩) (fun x => hf ⟨x,0⟩) N)

end ComputableAnalysis.ModularForms
