import ComputableAnalysis.ModularForms.ExponentialRationalPrefix
import ComputableAnalysis.ModularForms.ConjugationLimit

/-! Conjugation of exponential prefixes and exact conjugate-limit comparisons. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

theorem conjugateDifference_small (z w : ComplexRaw) (B : Rat)
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


theorem rationalExp_power_conjugate (z : QComplex) (n : Nat) :
    QComplex.conj (QComplex.pow z n)=QComplex.pow (QComplex.conj z) n := by
  induction n with
  | zero => change QComplex.conj QComplex.one=QComplex.one; decide +kernel
  | succ n ih => simp only [QComplex.pow,QComplex.conj_mul,ih]

theorem rationalExp_term_conjugate (z : QComplex) (n : Nat) :
    QComplex.conj (ComplexSeries.expTerm z n)=ComplexSeries.expTerm (QComplex.conj z) n := by
  unfold ComplexSeries.expTerm
  rw [← rationalExp_power_conjugate z n]
  unfold QComplex.divRat QComplex.conj
  congr 1
  grind only

theorem rationalExp_prefix_conjugate (z : QComplex) (N : Nat) :
    QComplex.conj (ComplexExponentialApproximation.expPrefix z N)=
      ComplexExponentialApproximation.expPrefix (QComplex.conj z) N := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [ComplexExponentialApproximation.expPrefix_succ,QComplex.conj_add,ih,
      rationalExp_term_conjugate,ComplexExponentialApproximation.expPrefix_succ]

theorem conjugateLimit_comparison (F G : ComplexRaw) (hF : F.Valid) (hG : G.Valid)
    (p q : Nat → ComplexRaw) (hp : ∀ n, (p n).Valid) (hq : ∀ n, (q n).Valid)
    (e d : Nat → Rat) (he : ShrinksToZero e) (hd : ShrinksToZero d)
    (hen : ∀ n, 0≤e n) (hdn : ∀ n, 0≤d n)
    (hFp : ∀ n, Small (sub F (p n)) (e n))
    (hGq : ∀ n, Small (sub G (q n)) (d n))
    (hconj : ∀ n, (conj (p n)).Equiv (q n)) : (conj F).Equiv G := by
  let v := fun n => conj (p n)
  have hv : ∀ n, (v n).Valid := fun n => conj_valid _ (hp n)
  apply RepresentedCauchySum.unique v hv (fun n => e n+d n)
    (RepresentedCauchySum.sum_shrinks _ _ he hd) _ _ (conj_valid _ hF) hG
  · intro n
    exact (conjugateDifference_small F (p n) (e n) (hFp n)).mono (by have := hdn n; grind only)
  · intro n
    have h := Small.congr (sub_valid hG (hq n)) (sub_valid hG (hv n))
      (FunctionTheory.sub_congr (equiv_refl _ hG) (equiv_symm (hconj n))) (hGq n)
    exact h.mono (by have := hen n; grind only)

end ComputableAnalysis.ModularForms
