import ComputableAnalysis.RiemannHilbert.ScalarAlgebra
import ComputableAnalysis.RiemannHilbert.RepresentedCauchySum

/-! Passing explicit finite error bounds to represented limits. -/
namespace ComputableAnalysis.RiemannHilbert.SeriesLimitLaws
open ComplexRaw FunctionTheory LocalODE

theorem small_neg {z : ComplexRaw} {B : Rat} (h : Small z B) : Small (neg z) B := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n m; have hh := h.2.1 m n
    change (z.compute m).lo.re ≤ B at hh
    change -B ≤ -(z.compute m).lo.re
    exact Rat.neg_le_neg hh
  · intro n m; have hh := h.1 m n
    change -B ≤ (z.compute n).hi.re at hh
    change -(z.compute n).hi.re ≤ B
    grind
  · intro n m; have hh := h.2.2.2 m n
    change (z.compute m).lo.im ≤ B at hh
    change -B ≤ -(z.compute m).lo.im
    exact Rat.neg_le_neg hh
  · intro n m; have hh := h.2.2.1 m n
    change -B ≤ (z.compute n).hi.im at hh
    change -(z.compute n).hi.im ≤ B
    grind

theorem small_sub {z w : ComplexRaw} {B D : Rat} (hz : Small z B) (hw : Small w D) :
    Small (sub z w) (B+D) := small_add hz (small_neg hw)

theorem small_closed (z : ComplexRaw) (B : Rat) (e : Nat → Rat)
    (he : ShrinksToZero e) (h : ∀ N, Small z (B+e N)) : Small z B := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n m
    have hh : -(z.compute m).hi.re ≤ B := RepresentedCauchySum.le_of_shrinking_error e he _ _ (by
      intro N
      have ht := (h N).1 n m
      change -(B+e N) ≤ (z.compute m).hi.re at ht
      grind)
    change -B ≤ (z.compute m).hi.re
    grind
  · intro n m
    exact RepresentedCauchySum.le_of_shrinking_error e he _ _
      (fun N => (h N).2.1 n m)
  · intro n m
    have hh : -(z.compute m).hi.im ≤ B := RepresentedCauchySum.le_of_shrinking_error e he _ _ (by
      intro N
      have ht := (h N).2.2.1 n m
      change -(B+e N) ≤ (z.compute m).hi.im at ht
      grind)
    change -B ≤ (z.compute m).hi.im
    grind
  · intro n m
    exact RepresentedCauchySum.le_of_shrinking_error e he _ _
      (fun N => (h N).2.2.2 n m)

theorem add_difference (z p : ComplexRaw) (hz : z.Valid) (hp : p.Valid) :
    (add p (sub z p)).Equiv z := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := add_valid hp (sub_valid hz hp)) (hright := hz)
  change ComplexRawQuotient.ofRaw p hp +
    (ComplexRawQuotient.ofRaw z hz-ComplexRawQuotient.ofRaw p hp) = ComplexRawQuotient.ofRaw z hz
  grind

/-- A uniform bound on valid approximations survives their explicit errors. -/
theorem small_of_prefix_bound (z : ComplexRaw) (hz : z.Valid) (p : Nat → ComplexRaw)
    (hp : ∀ N, (p N).Valid) (B : Rat) (e : Nat → Rat) (he : ShrinksToZero e)
    (hclose : ∀ N, Small (sub z (p N)) (e N))
    (hbound : ∀ N, Small (p N) B) : Small z B := by
  apply small_closed z B e he
  intro N
  exact Small.congr (add_valid (hp N) (sub_valid hz (hp N))) hz
    (add_difference z (p N) hz (hp N)) (small_add (hbound N) (hclose N))

def remainder (F G D h : ComplexRaw) : ComplexRaw := sub (sub F G) (mul D h)

theorem remainder_valid (F G D h : ComplexRaw)
    (hF : F.Valid) (hG : G.Valid) (hD : D.Valid) (hh : h.Valid) :
    (remainder F G D h).Valid := sub_valid (sub_valid hF hG) (mul_valid hD hh)

theorem remainder_difference (F G D p q r h : ComplexRaw)
    (hF : F.Valid) (hG : G.Valid) (hD : D.Valid)
    (hp : p.Valid) (hq : q.Valid) (hr : r.Valid) (hh : h.Valid) :
    (sub (remainder F G D h) (remainder p q r h)).Equiv
      (sub (sub (sub F p) (sub G q)) (mul (sub D r) h)) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := sub_valid (remainder_valid F G D h hF hG hD hh) (remainder_valid p q r h hp hq hr hh))
    (hright := sub_valid (sub_valid (sub_valid hF hp) (sub_valid hG hq)) (mul_valid (sub_valid hD hr) hh))
  change
    ((ComplexRawQuotient.ofRaw F hF-ComplexRawQuotient.ofRaw G hG)-
       ComplexRawQuotient.ofRaw D hD*ComplexRawQuotient.ofRaw h hh) -
    ((ComplexRawQuotient.ofRaw p hp-ComplexRawQuotient.ofRaw q hq)-
       ComplexRawQuotient.ofRaw r hr*ComplexRawQuotient.ofRaw h hh) =
    ((ComplexRawQuotient.ofRaw F hF-ComplexRawQuotient.ofRaw p hp)-
       (ComplexRawQuotient.ofRaw G hG-ComplexRawQuotient.ofRaw q hq)) -
    ((ComplexRawQuotient.ofRaw D hD-ComplexRawQuotient.ofRaw r hr)*ComplexRawQuotient.ofRaw h hh)
  grind

theorem remainder_close (F G D p q r h : ComplexRaw)
    (hF : F.Valid) (hG : G.Valid) (hD : D.Valid)
    (hp : p.Valid) (hq : q.Valid) (hr : r.Valid) (hh : h.Valid)
    (E U V H : Rat) (hV : 0 ≤ V) (hH : 0 ≤ H)
    (hFp : Small (sub F p) E) (hGq : Small (sub G q) U)
    (hDr : Small (sub D r) V) (hhH : Small h H) :
    Small (sub (remainder F G D h) (remainder p q r h)) (E+U+2*V*H) := by
  have hs := small_sub (small_sub hFp hGq)
    (Small.mul (sub_valid hD hr) hh hV hH hDr hhH)
  exact Small.congr
    (sub_valid (sub_valid (sub_valid hF hp) (sub_valid hG hq)) (mul_valid (sub_valid hD hr) hh))
    (sub_valid (remainder_valid F G D h hF hG hD hh) (remainder_valid p q r h hp hq hr hh))
    (equiv_symm (remainder_difference F G D p q r h hF hG hD hp hq hr hh)) hs


theorem shrinks_shift (e : Nat → Rat) (he : ShrinksToZero e) (k : Nat) :
    ShrinksToZero (fun n => e (n+k)) := by
  intro eps
  obtain ⟨N,hN⟩ := he eps
  exact ⟨N, fun n hn => hN (n+k) (by omega)⟩

theorem shrinks_scale (e : Nat → Rat) (he : ShrinksToZero e) (s : Rat) (hs : 0 ≤ s) :
    ShrinksToZero (fun n => s*e n) := by
  intro eps
  have hd : 0 < s+1 := by grind
  let eta : QPos := ⟨eps.val/(s+1), by
    rw [Rat.div_def]
    exact Rat.mul_pos eps.property ((Rat.inv_pos).2 hd)⟩
  obtain ⟨N,hN⟩ := he eta
  refine ⟨N, ?_⟩
  intro n hn
  have hb := Rat.mul_le_mul_of_nonneg_left (hN n hn) hs
  have hne : s+1 ≠ 0 := Rat.ne_of_gt hd
  have heq : (s+1)*eta.val = eps.val := by
    dsimp [eta]
    rw [Rat.mul_comm]
    exact Rat.div_mul_cancel hne
  have hle := Rat.mul_le_mul_of_nonneg_right (show s ≤ s+1 by grind) (Rat.le_of_lt eta.property)
  exact Rat.le_trans hb (heq ▸ hle)


theorem addition_difference (F G p q : ComplexRaw)
    (hF : F.Valid) (hG : G.Valid) (hp : p.Valid) (hq : q.Valid) :
    (sub (add F p) (add G q)).Equiv (add (sub F G) (sub p q)) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := sub_valid (add_valid hF hp) (add_valid hG hq))
    (hright := add_valid (sub_valid hF hG) (sub_valid hp hq))
  change
    (ComplexRawQuotient.ofRaw F hF+ComplexRawQuotient.ofRaw p hp)-
      (ComplexRawQuotient.ofRaw G hG+ComplexRawQuotient.ofRaw q hq) =
    (ComplexRawQuotient.ofRaw F hF-ComplexRawQuotient.ofRaw G hG)+
      (ComplexRawQuotient.ofRaw p hp-ComplexRawQuotient.ofRaw q hq)
  grind

theorem difference_difference (F G p q : ComplexRaw)
    (hF : F.Valid) (hG : G.Valid) (hp : p.Valid) (hq : q.Valid) :
    (sub (sub F G) (sub p q)).Equiv (sub (sub F p) (sub G q)) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := sub_valid (sub_valid hF hG) (sub_valid hp hq))
    (hright := sub_valid (sub_valid hF hp) (sub_valid hG hq))
  change
    (ComplexRawQuotient.ofRaw F hF-ComplexRawQuotient.ofRaw G hG)-
      (ComplexRawQuotient.ofRaw p hp-ComplexRawQuotient.ofRaw q hq) =
    (ComplexRawQuotient.ofRaw F hF-ComplexRawQuotient.ofRaw p hp)-
      (ComplexRawQuotient.ofRaw G hG-ComplexRawQuotient.ofRaw q hq)
  grind

theorem difference_close (F G p q : ComplexRaw)
    (hF : F.Valid) (hG : G.Valid) (hp : p.Valid) (hq : q.Valid)
    (E U : Rat) (hFp : Small (sub F p) E) (hGq : Small (sub G q) U) :
    Small (sub (sub F G) (sub p q)) (E+U) :=
  Small.congr (sub_valid (sub_valid hF hp) (sub_valid hG hq))
    (sub_valid (sub_valid hF hG) (sub_valid hp hq))
    (equiv_symm (difference_difference F G p q hF hG hp hq)) (small_sub hFp hGq)


theorem product_difference (F G p q : ComplexRaw)
    (hF : F.Valid) (hG : G.Valid) (hp : p.Valid) (hq : q.Valid) :
    (sub (mul F G) (mul p q)).Equiv
      (add (mul (sub F p) G) (mul p (sub G q))) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := sub_valid (mul_valid hF hG) (mul_valid hp hq))
    (hright := add_valid (mul_valid (sub_valid hF hp) hG) (mul_valid hp (sub_valid hG hq)))
  change ComplexRawQuotient.ofRaw F hF*ComplexRawQuotient.ofRaw G hG -
    ComplexRawQuotient.ofRaw p hp*ComplexRawQuotient.ofRaw q hq =
    (ComplexRawQuotient.ofRaw F hF-ComplexRawQuotient.ofRaw p hp)*ComplexRawQuotient.ofRaw G hG+
    ComplexRawQuotient.ofRaw p hp*(ComplexRawQuotient.ofRaw G hG-ComplexRawQuotient.ofRaw q hq)
  grind

theorem product_close (F G p q : ComplexRaw)
    (hF : F.Valid) (hG : G.Valid) (hp : p.Valid) (hq : q.Valid)
    (E U A B : Rat) (hE : 0 ≤ E) (hU : 0 ≤ U) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hFp : Small (sub F p) E) (hGq : Small (sub G q) U) (hpA : Small p A) (hGB : Small G B) :
    Small (sub (mul F G) (mul p q)) (2*E*B+2*A*U) :=
  Small.congr
    (add_valid (mul_valid (sub_valid hF hp) hG) (mul_valid hp (sub_valid hG hq)))
    (sub_valid (mul_valid hF hG) (mul_valid hp hq))
    (equiv_symm (product_difference F G p q hF hG hp hq))
    (small_add (Small.mul (sub_valid hF hp) hG hE hB hFp hGB)
      (Small.mul hp (sub_valid hG hq) hA hU hpA hGq))

theorem difference_via (F G p q : ComplexRaw)
    (hF : F.Valid) (hG : G.Valid) (hp : p.Valid) (hq : q.Valid) :
    (sub F G).Equiv (add (add (sub F p) (sub p q)) (sub q G)) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := sub_valid hF hG)
    (hright := add_valid (add_valid (sub_valid hF hp) (sub_valid hp hq)) (sub_valid hq hG))
  change ComplexRawQuotient.ofRaw F hF-ComplexRawQuotient.ofRaw G hG =
    ((ComplexRawQuotient.ofRaw F hF-ComplexRawQuotient.ofRaw p hp)+
     (ComplexRawQuotient.ofRaw p hp-ComplexRawQuotient.ofRaw q hq))+
     (ComplexRawQuotient.ofRaw q hq-ComplexRawQuotient.ofRaw G hG)
  grind

/-- Exact value equality follows from a proved zero difference bound. -/
theorem equiv_of_small_sub_zero (z w : ComplexRaw) (h : Small (sub z w) 0) : z.Equiv w := by
  intro n
  apply (compareAt_overlap_iff z w n n).2
  have h1 := h.1 n n
  have h2 := h.2.1 n n
  have h3 := h.2.2.1 n n
  have h4 := h.2.2.2 n n
  change (0 : Rat) ≤ (z.compute n).hi.re + -(w.compute n).lo.re at h1
  change (z.compute n).lo.re + -(w.compute n).hi.re ≤ (0 : Rat) at h2
  change (0 : Rat) ≤ (z.compute n).hi.im + -(w.compute n).lo.im at h3
  change (z.compute n).lo.im + -(w.compute n).hi.im ≤ (0 : Rat) at h4
  change ((z.compute n).lo.re ≤ (w.compute n).hi.re ∧ (z.compute n).lo.im ≤ (w.compute n).hi.im) ∧
    ((w.compute n).lo.re ≤ (z.compute n).hi.re ∧ (w.compute n).lo.im ≤ (z.compute n).hi.im)
  grind

end ComputableAnalysis.RiemannHilbert.SeriesLimitLaws
