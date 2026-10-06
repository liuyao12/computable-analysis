import ComputableAnalysis.ModularForms.FiniteSumSplit

/-! Concatenation law for executable finite represented sums. -/
namespace ComputableAnalysis.ModularForms
open RiemannHilbert

private def listValue (zs : List ComplexRaw) (hz : ∀ z ∈ zs, z.Valid) : ScalarAlgebra.Value :=
  ComplexRawQuotient.ofRaw (LocalODE.sum zs) (LocalODE.sum_valid zs hz)

private theorem listValue_append (as bs : List ComplexRaw)
    (ha : ∀ z ∈ as, z.Valid) (hb : ∀ z ∈ bs, z.Valid) :
    listValue (as++bs) (by intro z hz; rcases List.mem_append.mp hz with h|h; exact ha z h; exact hb z h)=
      listValue as ha+listValue bs hb := by
  induction as with
  | nil => change listValue bs hb=0+listValue bs hb; grind
  | cons a as ih =>
    have hav := ha a (by simp)
    have hat : ∀ z ∈ as, z.Valid := by intro z hz; exact ha z (by simp [hz])
    change ComplexRawQuotient.ofRaw a hav+listValue (as++bs)
      (by intro z hz; rcases List.mem_append.mp hz with h|h; exact hat z h; exact hb z h) =
      (ComplexRawQuotient.ofRaw a hav+listValue as hat)+listValue bs hb
    rw [ih hat]
    grind

theorem representedSum_append (as bs : List ComplexRaw)
    (ha : ∀ z ∈ as, z.Valid) (hb : ∀ z ∈ bs, z.Valid) :
    (LocalODE.sum (as++bs)).Equiv (ComplexRaw.add (LocalODE.sum as) (LocalODE.sum bs)) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := LocalODE.sum_valid _ (by
      intro z hz; rcases List.mem_append.mp hz with h|h; exact ha z h; exact hb z h))
    (hright := ComplexRaw.add_valid (LocalODE.sum_valid _ ha) (LocalODE.sum_valid _ hb))
  exact listValue_append as bs ha hb

end ComputableAnalysis.ModularForms
