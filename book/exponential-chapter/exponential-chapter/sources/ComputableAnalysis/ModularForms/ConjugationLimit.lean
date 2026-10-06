import ComputableAnalysis.ModularForms.RepresentedSumConjugation

/-! Passing shrinking finite conjugation errors to exact represented limits. -/
namespace ComputableAnalysis.ModularForms
open RiemannHilbert FunctionTheory ComplexRaw

private theorem small_conjugate_sub (z w : ComplexRaw) (B : Rat)
    (h : Small (sub z w) B) : Small (sub (conj z) (conj w)) B := by
  refine ⟨?_,?_,?_,?_⟩
  · intro n m
    have hh := h.1 n m
    simpa [sub,add,neg,conj,QBox.add,QBox.neg,QBox.conj,QComplex.add,ComplexRaw.realPart,ComplexRaw.imagPart] using hh
  · intro n m
    have hh := h.2.1 n m
    simpa [sub,add,neg,conj,QBox.add,QBox.neg,QBox.conj,QComplex.add,ComplexRaw.realPart,ComplexRaw.imagPart] using hh
  · intro n m
    have hh := h.2.2.2 m n
    simp [sub,add,neg,conj,QBox.add,QBox.neg,QBox.conj,QComplex.add,ComplexRaw.realPart,ComplexRaw.imagPart] at hh ⊢
    grind
  · intro n m
    have hh := h.2.2.1 m n
    simp [sub,add,neg,conj,QBox.add,QBox.neg,QBox.conj,QComplex.add,ComplexRaw.realPart,ComplexRaw.imagPart] at hh ⊢
    grind

/-- A represented limit is real when its valid finite approximants have
shrinking conjugation error. All equality is derived from quantitative bounds. -/
theorem conjugation_limit (F : ComplexRaw) (hF : F.Valid)
    (p : Nat → ComplexRaw) (hp : ∀ n, (p n).Valid)
    (tail error : Nat → Rat) (ht : ShrinksToZero tail) (he : ShrinksToZero error)
    (hc : ∀ n, Small (sub F (p n)) (tail n))
    (hr : ∀ n, Small (sub (p n) (conj (p n))) (error n)) :
    F.Equiv (conj F) := by
  apply SeriesLimitLaws.equiv_of_small_sub_zero
  apply SeriesLimitLaws.small_closed (sub F (conj F)) 0
    (fun n => (tail n+error n)+tail n)
    (RepresentedCauchySum.sum_shrinks _ _
      (RepresentedCauchySum.sum_shrinks _ _ ht he) ht)
  intro n
  have hlast := small_conjugate_sub (p n) F (tail n)
    (RepresentedCauchySum.small_sub_symm F (p n) (tail n) (hc n))
  have hb := LocalODE.small_add (LocalODE.small_add (hc n) (hr n)) hlast
  have hv := SeriesLimitLaws.difference_via F (conj F) (p n) (conj (p n))
    hF (conj_valid _ hF) (hp n) (conj_valid _ (hp n))
  have hs := Small.congr
    (add_valid (add_valid (sub_valid hF (hp n)) (sub_valid (hp n) (conj_valid _ (hp n))))
      (sub_valid (conj_valid _ (hp n)) (conj_valid _ hF)))
    (sub_valid hF (conj_valid _ hF)) (equiv_symm hv) hb
  simpa only [Rat.zero_add] using hs

end ComputableAnalysis.ModularForms
