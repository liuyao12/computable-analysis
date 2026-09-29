import ComputableAnalysis.Holomorphic

/-! Rational-radius neighborhood algebra for represented complex points. -/
namespace ComputableAnalysis.FunctionTheory
open ComplexRaw

theorem Small.sub_self (a : ComplexRaw) (ha : a.Valid) {r : Rat} (hr : 0 ≤ r) :
    Small (sub a a) r := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n m
    have h := (valid_ordered ha m).1
    change -r ≤ (a.compute m).hi.re + -(a.compute m).lo.re
    grind
  · intro n m
    have h := (valid_ordered ha n).1
    change (a.compute n).lo.re + -(a.compute n).hi.re ≤ r
    grind
  · intro n m
    have h := (valid_ordered ha m).2
    change -r ≤ (a.compute m).hi.im + -(a.compute m).lo.im
    grind
  · intro n m
    have h := (valid_ordered ha n).2
    change (a.compute n).lo.im + -(a.compute n).hi.im ≤ r
    grind

theorem Small.add {z w : ComplexRaw} {r s : Rat}
    (h : Small z r) (k : Small w s) : Small (add z w) (r+s) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro n m
  · have hz := h.1 n m; have hw := k.1 n m
    change -r ≤ (z.compute m).hi.re at hz
    change -s ≤ (w.compute m).hi.re at hw
    change -(r+s) ≤ (z.compute m).hi.re + (w.compute m).hi.re
    grind
  · have hz := h.2.1 n m; have hw := k.2.1 n m
    change (z.compute n).lo.re ≤ r at hz
    change (w.compute n).lo.re ≤ s at hw
    change (z.compute n).lo.re + (w.compute n).lo.re ≤ r+s
    grind
  · have hz := h.2.2.1 n m; have hw := k.2.2.1 n m
    change -r ≤ (z.compute m).hi.im at hz
    change -s ≤ (w.compute m).hi.im at hw
    change -(r+s) ≤ (z.compute m).hi.im + (w.compute m).hi.im
    grind
  · have hz := h.2.2.2 n m; have hw := k.2.2.2 n m
    change (z.compute n).lo.im ≤ r at hz
    change (w.compute n).lo.im ≤ s at hw
    change (z.compute n).lo.im + (w.compute n).lo.im ≤ r+s
    grind

theorem Small.sub_symm {a b : ComplexRaw} {r : Rat}
    (h : Small (sub a b) r) : Small (sub b a) r := by
  rcases h with ⟨h1,h2,h3,h4⟩
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro n m
  · have h := h2 m n
    change (a.compute m).lo.re + -(b.compute m).hi.re ≤ r at h
    change -r ≤ (b.compute m).hi.re + -(a.compute m).lo.re
    grind
  · have h := h1 m n
    change -r ≤ (a.compute n).hi.re + -(b.compute n).lo.re at h
    change (b.compute n).lo.re + -(a.compute n).hi.re ≤ r
    grind
  · have h := h4 m n
    change (a.compute m).lo.im + -(b.compute m).hi.im ≤ r at h
    change -r ≤ (b.compute m).hi.im + -(a.compute m).lo.im
    grind
  · have h := h3 m n
    change -r ≤ (a.compute n).hi.im + -(b.compute n).lo.im at h
    change (b.compute n).lo.im + -(a.compute n).hi.im ≤ r
    grind

theorem sub_telescope (a b c : ComplexRaw) (ha : a.Valid) (hb : b.Valid)
    (hc : c.Valid) : (add (sub a b) (sub b c)).Equiv (sub a c) := by
  intro n
  apply (compareAt_overlap_iff _ _ n n).2
  have ha' := valid_ordered ha n
  have hb' := valid_ordered hb n
  have hc' := valid_ordered hc n
  simp only [QBox.Ordered, QComplex.le_def] at ha' hb' hc'
  simp only [sub, add, neg, QBox.add, QBox.neg, QBox.Overlaps,
    QComplex.add, QComplex.neg, QComplex.le_def]
  constructor <;> constructor <;> grind

theorem Small.sub_triangle {a b c : ComplexRaw} {r s : Rat}
    (ha : a.Valid) (hb : b.Valid) (hc : c.Valid)
    (h : Small (sub a b) r) (k : Small (sub b c) s) :
    Small (sub a c) (r+s) :=
  Small.congr (add_valid (sub_valid ha hb) (sub_valid hb hc)) (sub_valid ha hc)
    (sub_telescope a b c ha hb hc) (h.add k)

end ComputableAnalysis.FunctionTheory
