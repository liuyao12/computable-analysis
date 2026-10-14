import ComputableAnalysis.ModularForms.FiniteSumSplit

/-! Exact subtraction of selected terms from an executable finite represented sum. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert

private theorem mapped_valid {α : Type} (f : α → ComplexRaw)
    (hf : ∀ a, (f a).Valid) (xs : List α) : (LocalODE.sum (xs.map f)).Valid := by
  apply LocalODE.sum_valid
  intro z hz
  obtain ⟨a,_,rfl⟩ := List.mem_map.mp hz
  exact hf a

theorem representedSum_filter_difference {α : Type} (f : α → ComplexRaw)
    (hf : ∀ a, (f a).Valid) (keep : α → Bool) (xs : List α) :
    (sub (LocalODE.sum (xs.map f)) (LocalODE.sum ((xs.filter keep).map f))).Equiv
      (LocalODE.sum ((xs.filter (fun a => !keep a)).map f)) := by
  have he := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mapped_valid f hf xs)
    (hright := add_valid (mapped_valid f hf (xs.filter keep))
      (mapped_valid f hf (xs.filter (fun a => !keep a))))
    (representedSum_split f hf keep xs)
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := sub_valid (mapped_valid f hf xs) (mapped_valid f hf (xs.filter keep)))
    (hright := mapped_valid f hf (xs.filter (fun a => !keep a)))
  let F := ComplexRawQuotient.ofRaw (LocalODE.sum (xs.map f)) (mapped_valid f hf xs)
  let P := ComplexRawQuotient.ofRaw (LocalODE.sum ((xs.filter keep).map f)) (mapped_valid f hf _)
  let Q := ComplexRawQuotient.ofRaw (LocalODE.sum ((xs.filter (fun a => !keep a)).map f)) (mapped_valid f hf _)
  change F=P+Q at he
  change F-P=Q
  generalize F=f,P=p,Q=q at he ⊢
  grind only

end ComputableAnalysis.ModularForms
