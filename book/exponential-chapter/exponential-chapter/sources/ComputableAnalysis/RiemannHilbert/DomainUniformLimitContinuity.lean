import ComputableAnalysis.RiemannHilbert.DomainHolomorphicAlgebra

/-! Continuity of supplied represented limits with uniform shrinking prefix errors. -/
namespace ComputableAnalysis.RiemannHilbert.DomainFunctions
open ComplexRaw FunctionTheory

noncomputable def continuousOn_of_uniform_prefixes {D : Scalar → Prop}
    (f : ∀ z, D z → Scalar) (p : Nat → ∀ z, D z → Scalar)
    (hp : ∀ N, ContinuousOn D (p N)) (r : Nat → Rat) (hr : ShrinksToZero r)
    (hclose : ∀ N z hz, Small (sub (f z hz).val (p N z hz).val) (r N)) :
    ContinuousOn D f where
  delta a ha eps :=
    let N := Classical.choose (hr (halfError (halfError eps)))
    (hp N).delta a ha (halfError eps)
  estimate a ha eps z hz hd := by
    let N := Classical.choose (hr (halfError (halfError eps)))
    have hn : r N≤(halfError (halfError eps)).val :=
      Classical.choose_spec (hr (halfError (halfError eps))) N (Nat.le_refl N)
    have hleft := (hclose N z hz).mono hn
    have hright := RepresentedCauchySum.small_sub_symm _ _ _ ((hclose N a ha).mono hn)
    have hmiddle := (hp N).estimate a ha (halfError eps) z hz hd
    have hs := LocalODE.small_add hleft (LocalODE.small_add hmiddle hright)
    have he : (add (sub (f z hz).val (p N z hz).val)
        (add (sub (p N z hz).val (p N a ha).val) (sub (p N a ha).val (f a ha).val))).Equiv
        (sub (f z hz).val (f a ha).val) := by
      apply ComplexRawQuotient.equiv_of_ofRaw_eq
        (hleft := add_valid (sub_valid (f z hz).property (p N z hz).property)
          (add_valid (sub_valid (p N z hz).property (p N a ha).property)
            (sub_valid (p N a ha).property (f a ha).property)))
        (hright := sub_valid (f z hz).property (f a ha).property)
      let F := ComplexRawQuotient.ofRaw (f z hz).val (f z hz).property
      let G := ComplexRawQuotient.ofRaw (f a ha).val (f a ha).property
      let P := ComplexRawQuotient.ofRaw (p N z hz).val (p N z hz).property
      let Q := ComplexRawQuotient.ofRaw (p N a ha).val (p N a ha).property
      change (F-P)+((P-Q)+(Q-G))=F-G
      grind only
    have hb := Small.congr
      (add_valid (sub_valid (f z hz).property (p N z hz).property)
        (add_valid (sub_valid (p N z hz).property (p N a ha).property)
          (sub_valid (p N a ha).property (f a ha).property)))
      (sub_valid (f z hz).property (f a ha).property) he hs
    apply hb.mono
    have hhalf := halfError_identity eps
    have hquarter := halfError_identity (halfError eps)
    grind only

end ComputableAnalysis.RiemannHilbert.DomainFunctions
