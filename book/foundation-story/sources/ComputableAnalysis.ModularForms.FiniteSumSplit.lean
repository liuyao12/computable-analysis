import ComputableAnalysis.ModularForms.LatticeFiniteReindexing

/-! Exact decomposition of represented finite sums into selected and omitted terms. -/
namespace ComputableAnalysis.ModularForms
open RiemannHilbert

private def sumValue {α : Type} (f : α → ScalarAlgebra.Value) : List α → ScalarAlgebra.Value
  | [] => 0
  | a::as => f a+sumValue f as

private theorem sumValue_filter {α : Type} (f : α → ScalarAlgebra.Value)
    (keep : α → Bool) (as : List α) :
    sumValue f as=sumValue f (as.filter keep)+sumValue f (as.filter (fun a => !keep a)) := by
  induction as with
  | nil => change 0=0+0; grind
  | cons a as ih =>
    cases he : keep a <;> simp only [List.filter_cons,he,Bool.not_false,Bool.not_true,
      Bool.false_eq_true,if_false,if_true,sumValue] <;> grind

private theorem sumValue_raw {α : Type} (f : α → ComplexRaw) (hf : ∀ a, (f a).Valid)
    (as : List α) : ComplexRawQuotient.ofRaw (LocalODE.sum (as.map f))
      (LocalODE.sum_valid _ (by intro z hz; obtain ⟨a,_,rfl⟩ := List.mem_map.mp hz; exact hf a))=
      sumValue (fun a => ComplexRawQuotient.ofRaw (f a) (hf a)) as := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    change ComplexRawQuotient.ofRaw (f a) (hf a)+
      ComplexRawQuotient.ofRaw (LocalODE.sum (as.map f))
        (LocalODE.sum_valid _ (by intro z hz; obtain ⟨a,_,rfl⟩ := List.mem_map.mp hz; exact hf a))=_
    rw [ih]
    rfl

/-- Executable filtering splits a finite sum exactly, without assumptions about
which terms the mask selects. -/
theorem representedSum_split {α : Type} (f : α → ComplexRaw) (hf : ∀ a, (f a).Valid)
    (keep : α → Bool) (as : List α) :
    (LocalODE.sum (as.map f)).Equiv
      (ComplexRaw.add (LocalODE.sum ((as.filter keep).map f))
        (LocalODE.sum ((as.filter (fun a => !keep a)).map f))) := by
  have hv (xs : List α) : (LocalODE.sum (xs.map f)).Valid := by
    apply LocalODE.sum_valid
    intro z hz
    obtain ⟨a,_,rfl⟩ := List.mem_map.mp hz
    exact hf a
  apply ComplexRawQuotient.equiv_of_ofRaw_eq (hleft := hv as)
    (hright := ComplexRaw.add_valid (hv _) (hv _))
  rw [ComplexRawQuotient.ofRaw_add _ _ (hv _) (hv _)]
  rw [sumValue_raw f hf as,sumValue_raw f hf (as.filter keep),
    sumValue_raw f hf (as.filter (fun a => !keep a))]
  exact sumValue_filter _ keep as

/-- Intersections listed in either source order have identical multiplicities. -/
theorem commonTerms_perm {α : Type} [DecidableEq α] (as bs : List α)
    (ha : as.Nodup) (hb : bs.Nodup) :
    (as.filter (fun a => decide (a ∈ bs))).Perm
      (bs.filter (fun a => decide (a ∈ as))) := by
  apply (List.perm_ext_iff_of_nodup
    (List.Nodup.sublist List.filter_sublist ha)
    (List.Nodup.sublist List.filter_sublist hb)).mpr
  intro a
  simp only [List.mem_filter,decide_eq_true_eq]
  exact And.comm

/-- Common terms of duplicate-free lists have exactly the same represented sum. -/
theorem representedSum_commonTerms {α : Type} [DecidableEq α]
    (f : α → ComplexRaw) (hf : ∀ a, (f a).Valid)
    (as bs : List α) (ha : as.Nodup) (hb : bs.Nodup) :
    (LocalODE.sum ((as.filter (fun a => decide (a ∈ bs))).map f)).Equiv
      (LocalODE.sum ((bs.filter (fun a => decide (a ∈ as))).map f)) :=
  representedSum_reindex f hf (commonTerms_perm as bs ha hb)

end ComputableAnalysis.ModularForms
