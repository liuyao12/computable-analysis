import ComputableAnalysis.ModularForms.FiniteSumSplit

/-! Cancellation of common terms in represented finite sums. -/
namespace ComputableAnalysis.ModularForms
open RiemannHilbert

private def finiteValue {α : Type} (f : α → ComplexRaw) (hf : ∀ a, (f a).Valid)
    (as : List α) : ScalarAlgebra.Value :=
  ComplexRawQuotient.ofRaw (LocalODE.sum (as.map f))
    (LocalODE.sum_valid _ (by
      intro z hz; obtain ⟨a,_,rfl⟩ := List.mem_map.mp hz; exact hf a))

private theorem finiteValue_split {α : Type} (f : α → ComplexRaw) (hf : ∀ a, (f a).Valid)
    (keep : α → Bool) (as : List α) :
    finiteValue f hf as=finiteValue f hf (as.filter keep)+
      finiteValue f hf (as.filter (fun a => !keep a)) := by
  have hv (xs : List α) : (LocalODE.sum (xs.map f)).Valid := by
    apply LocalODE.sum_valid
    intro z hz
    obtain ⟨a,_,rfl⟩ := List.mem_map.mp hz
    exact hf a
  exact ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := hv as) (hright := ComplexRaw.add_valid (hv _) (hv _))
    (representedSum_split f hf keep as)

/-- Common terms cancel; only the terms absent from the other list remain. -/
theorem representedSum_difference {α : Type} [DecidableEq α]
    (f : α → ComplexRaw) (hf : ∀ a, (f a).Valid)
    (as bs : List α) (ha : as.Nodup) (hb : bs.Nodup) :
    (ComplexRaw.sub (LocalODE.sum (as.map f)) (LocalODE.sum (bs.map f))).Equiv
      (ComplexRaw.sub
        (LocalODE.sum ((as.filter (fun a => !decide (a ∈ bs))).map f))
        (LocalODE.sum ((bs.filter (fun a => !decide (a ∈ as))).map f))) := by
  have hv (xs : List α) : (LocalODE.sum (xs.map f)).Valid := by
    apply LocalODE.sum_valid
    intro z hz
    obtain ⟨a,_,rfl⟩ := List.mem_map.mp hz
    exact hf a
  have h1 := finiteValue_split f hf (fun a => decide (a ∈ bs)) as
  have h2 := finiteValue_split f hf (fun a => decide (a ∈ as)) bs
  have hc : finiteValue f hf (as.filter (fun a => decide (a ∈ bs)))=
      finiteValue f hf (bs.filter (fun a => decide (a ∈ as))) :=
    ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := hv _) (hright := hv _)
      (representedSum_commonTerms f hf as bs ha hb)
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := ComplexRaw.sub_valid (hv as) (hv bs))
    (hright := ComplexRaw.sub_valid (hv _) (hv _))
  change finiteValue f hf as+ -finiteValue f hf bs=
    finiteValue f hf (as.filter (fun a => !decide (a ∈ bs)))+
      -finiteValue f hf (bs.filter (fun a => !decide (a ∈ as)))
  grind

end ComputableAnalysis.ModularForms
