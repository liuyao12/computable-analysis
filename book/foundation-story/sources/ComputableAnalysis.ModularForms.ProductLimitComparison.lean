import ComputableAnalysis.RiemannHilbert.SeriesLimitLaws

/-! A product comparison law from supplied valid prefixes and shrinking
errors. The finite product discrepancy must be proved separately. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert LocalODE SeriesLimitLaws

theorem product_limit_comparison (F G H : ComplexRaw)
    (hF : F.Valid) (hG : G.Valid) (hH : H.Valid)
    (p q d : Nat → ComplexRaw)
    (hp : ∀ N, (p N).Valid) (hq : ∀ N, (q N).Valid) (hd : ∀ N, (d N).Valid)
    (e u v w : Nat → Rat)
    (he : ShrinksToZero e) (hu : ShrinksToZero u)
    (hv : ShrinksToZero v) (hw : ShrinksToZero w)
    (he0 : ∀ N, 0 ≤ e N) (hu0 : ∀ N, 0 ≤ u N)
    (A B : Rat) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hpA : ∀ N, Small (p N) A) (hGB : Small G B)
    (hFp : ∀ N, Small (sub F (p N)) (e N))
    (hGq : ∀ N, Small (sub G (q N)) (u N))
    (hHd : ∀ N, Small (sub H (d N)) (v N))
    (hpd : ∀ N, Small (sub (mul (p N) (q N)) (d N)) (w N)) :
    (mul F G).Equiv H := by
  let E : Nat → Rat := fun N => (2*B)*(e N)+(2*A)*(u N)
  have hE : ShrinksToZero E := by
    exact RepresentedCauchySum.sum_shrinks _ _
      (shrinks_scale e he (2*B) (Rat.mul_nonneg (by decide +kernel) hB))
      (shrinks_scale u hu (2*A) (Rat.mul_nonneg (by decide +kernel) hA))
  have hclose (N : Nat) : Small (sub (mul F G) (mul (p N) (q N))) (E N) := by
    have ht := product_close F G (p N) (q N) hF hG (hp N) (hq N)
      (e N) (u N) A B (he0 N) (hu0 N) hA hB (hFp N) (hGq N) (hpA N) hGB
    have hi : 2*(e N)*B+2*A*(u N)=E N := by dsimp [E]; grind
    rw [hi] at ht
    exact ht
  apply equiv_of_small_sub_zero
  apply small_closed (sub (mul F G) H) 0
    (fun N => E N+w N+v N)
    (RepresentedCauchySum.sum_shrinks _ _
      (RepresentedCauchySum.sum_shrinks _ _ hE hw) hv)
  intro N
  have hs := small_add (small_add (hclose N) (hpd N)) (small_neg (hHd N))
  have heq : (add (add (sub (mul F G) (mul (p N) (q N)))
      (sub (mul (p N) (q N)) (d N))) (neg (sub H (d N)))).Equiv
      (sub (mul F G) H) := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := add_valid (add_valid
        (sub_valid (mul_valid hF hG) (mul_valid (hp N) (hq N)))
        (sub_valid (mul_valid (hp N) (hq N)) (hd N)))
        (neg_valid (sub_valid hH (hd N))))
      (hright := sub_valid (mul_valid hF hG) hH)
    change ((ComplexRawQuotient.ofRaw F hF * ComplexRawQuotient.ofRaw G hG -
      ComplexRawQuotient.ofRaw (p N) (hp N) * ComplexRawQuotient.ofRaw (q N) (hq N)) +
      (ComplexRawQuotient.ofRaw (p N) (hp N) * ComplexRawQuotient.ofRaw (q N) (hq N) -
        ComplexRawQuotient.ofRaw (d N) (hd N))) +
      -(ComplexRawQuotient.ofRaw H hH - ComplexRawQuotient.ofRaw (d N) (hd N)) =
      ComplexRawQuotient.ofRaw F hF * ComplexRawQuotient.ofRaw G hG - ComplexRawQuotient.ofRaw H hH
    grind
  have hb := Small.congr
    (add_valid (add_valid
      (sub_valid (mul_valid hF hG) (mul_valid (hp N) (hq N)))
      (sub_valid (mul_valid (hp N) (hq N)) (hd N))) (neg_valid (sub_valid hH (hd N))))
    (sub_valid (mul_valid hF hG) hH) heq hs
  simpa only [Rat.zero_add] using hb

end ComputableAnalysis.ModularForms
