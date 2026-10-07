import ComputableAnalysis.ModularForms.RepresentedSumAppend

/-! Finite row assembly for the executable represented complex sum. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert

private theorem sumMap_valid {α : Type} (f : α → ComplexRaw)
    (hf : ∀ a, (f a).Valid) (xs : List α) :
    (LocalODE.sum (xs.map f)).Valid := by
  apply LocalODE.sum_valid
  intro z hz
  obtain ⟨a,_,rfl⟩ := List.mem_map.mp hz
  exact hf a

/-- Summing finite rows agrees with summing their concatenated list of terms. -/
theorem representedSum_rows {α β : Type} (f : β → ComplexRaw)
    (hf : ∀ b, (f b).Valid) (rows : α → List β) (xs : List α) :
    (LocalODE.sum ((xs.flatMap rows).map f)).Equiv
      (LocalODE.sum (xs.map (fun a => LocalODE.sum ((rows a).map f)))) := by
  induction xs with
  | nil => exact equiv_refl _ (ofQComplex_valid _)
  | cons a xs ih =>
    simp only [List.flatMap_cons,List.map_append,List.map_cons]
    have ha : ∀ z ∈ (rows a).map f, z.Valid := by
      intro z hz
      obtain ⟨b,_,rfl⟩ := List.mem_map.mp hz
      exact hf b
    have hb : ∀ z ∈ (xs.flatMap rows).map f, z.Valid := by
      intro z hz
      obtain ⟨b,_,rfl⟩ := List.mem_map.mp hz
      exact hf b
    exact equiv_trans
      (LocalODE.sum_valid _ (by
        intro z hz
        rcases List.mem_append.mp hz with h|h
        · exact ha z h
        · exact hb z h))
      (add_valid (LocalODE.sum_valid _ ha) (LocalODE.sum_valid _ hb))
      (add_valid (LocalODE.sum_valid _ ha)
        (sumMap_valid (fun a => LocalODE.sum ((rows a).map f))
          (fun a => sumMap_valid f hf (rows a)) xs))
      (representedSum_append _ _ ha hb)
      (add_equiv (equiv_refl _ (LocalODE.sum_valid _ ha)) ih)

end ComputableAnalysis.ModularForms
