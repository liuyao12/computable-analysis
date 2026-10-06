import ComputableAnalysis.RiemannHilbert.UnitIntervalScalarAlgebra

/-! Actual scalar path concatenation on all represented real parameters.
The formula evaluates both clamped parameters and cancels the common
endpoint. Exact branch laws and continuity are proved, rather than assumed. -/
namespace ComputableAnalysis.RiemannHilbert.ScalarPathConcatenation
open ComplexRaw FunctionTheory DomainFunctions UnitInterval

def value (f g : Point → Scalar) (c : Scalar) (t : Point) : Scalar :=
  scalarSum (scalarSum (f (leftParameter t)) (g (rightParameter t))) (scalarNeg c)

theorem value_congr {f f' g g' : Point → Scalar} {c c' : Scalar} {s t : Point}
    (hf : f (leftParameter s) ≈ f' (leftParameter t))
    (hg : g (rightParameter s) ≈ g' (rightParameter t)) (hc : c ≈ c') :
    value f g c s ≈ value f' g' c' t := add_equiv (add_equiv hf hg) (neg_equiv hc)

theorem point_congr (f g : Point → Scalar) (c : Scalar)
    (hf : ∀ s t, s ≈ t → f s ≈ f t) (hg : ∀ s t, s ≈ t → g s ≈ g t) :
    ∀ s t, s ≈ t → value f g c s ≈ value f g c t := fun s t hst =>
  value_congr (hf _ _ (leftParameter_congr hst)) (hg _ _ (rightParameter_congr hst)) (Setoid.refl c)

theorem continuous (f g : Point → Scalar) (c : Scalar)
    (hfc : ∀ s t, s ≈ t → f s ≈ f t) (hgc : ∀ s t, s ≈ t → g s ≈ g t)
    (hf : ScalarContinuous f) (hg : ScalarContinuous g) : ScalarContinuous (value f g c) :=
  ((hf.precompose leftParameterContinuousData.continuous).add
    (hg.precompose rightParameterContinuousData.continuous)
    (fun _ _ h => hfc _ _ (leftParameter_congr h)) (fun _ _ h => hgc _ _ (rightParameter_congr h))).add
    (constantContinuousData (scalarNeg c)).continuous
    (fun _ _ h => add_equiv (hfc _ _ (leftParameter_congr h)) (hgc _ _ (rightParameter_congr h)))
    (fun _ _ _ => Setoid.refl _)

def continuousData (f g : Point → Scalar) (c : Scalar)
    (hf : ScalarContinuousData f) (hg : ScalarContinuousData g) : ScalarContinuousData (value f g c) :=
  ((hf.precompose leftParameter leftParameterContinuousData).add
    (hg.precompose rightParameter rightParameterContinuousData)).add (constantContinuousData (scalarNeg c))

private theorem cancel_right (a b c : Scalar) (hbc : b ≈ c) : scalarSum (scalarSum a b) (scalarNeg c) ≈ a := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (scalarSum (scalarSum a b) (scalarNeg c)).property) (hright := a.property)
  have h := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := b.property) (hright := c.property) hbc
  let A := ComplexRawQuotient.ofRaw a.val a.property
  let B := ComplexRawQuotient.ofRaw b.val b.property
  let C := ComplexRawQuotient.ofRaw c.val c.property
  change B=C at h
  change (A+B)+ -C=A
  grind only

private theorem cancel_left (a b c : Scalar) (hac : a ≈ c) : scalarSum (scalarSum a b) (scalarNeg c) ≈ b := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (scalarSum (scalarSum a b) (scalarNeg c)).property) (hright := b.property)
  have h := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := a.property) (hright := c.property) hac
  let A := ComplexRawQuotient.ofRaw a.val a.property
  let B := ComplexRawQuotient.ofRaw b.val b.property
  let C := ComplexRawQuotient.ofRaw c.val c.property
  change A=C at h
  change (A+B)+ -C=B
  grind only

theorem first_piece (f g : Point → Scalar) (c : Scalar)
    (hf : ∀ s t, s ≈ t → f s ≈ f t) (hg : ∀ s t, s ≈ t → g s ≈ g t)
    (hg0 : g zero ≈ c) (t : Point) (ht : t.value.Le (RealRaw.ofRat (1/2))) :
    value f g c t ≈ f (doubled t ht) :=
  Setoid.trans (cancel_right _ _ c (Setoid.trans (hg _ _ (rightParameter_on_first t ht)) hg0))
    (hf _ _ (leftParameter_on_first t ht))

theorem second_piece (f g : Point → Scalar) (c : Scalar)
    (hf : ∀ s t, s ≈ t → f s ≈ f t) (hg : ∀ s t, s ≈ t → g s ≈ g t)
    (hf1 : f one ≈ c) (t : Point) (ht : (RealRaw.ofRat (1/2)).Le t.value) :
    value f g c t ≈ g (secondHalf t ht) :=
  Setoid.trans (cancel_left _ _ c (Setoid.trans (hf _ _ (leftParameter_on_second t ht)) hf1))
    (hg _ _ (rightParameter_on_second t ht))

theorem source (f g : Point → Scalar) (p c : Scalar)
    (hf : ∀ s t, s ≈ t → f s ≈ f t) (hg : ∀ s t, s ≈ t → g s ≈ g t)
    (hf0 : f zero ≈ p) (hg0 : g zero ≈ c) : value f g c zero ≈ p :=
  Setoid.trans (cancel_right _ _ c (Setoid.trans (hg _ _ rightParameter_zero) hg0))
    (Setoid.trans (hf _ _ leftParameter_zero) hf0)

theorem target (f g : Point → Scalar) (c q : Scalar)
    (hf : ∀ s t, s ≈ t → f s ≈ f t) (hg : ∀ s t, s ≈ t → g s ≈ g t)
    (hf1 : f one ≈ c) (hg1 : g one ≈ q) : value f g c one ≈ q :=
  Setoid.trans (cancel_left _ _ c (Setoid.trans (hf _ _ leftParameter_one) hf1))
    (Setoid.trans (hg _ _ rightParameter_one) hg1)

theorem midpoint_value (f g : Point → Scalar) (c : Scalar)
    (hf : ∀ s t, s ≈ t → f s ≈ f t) (hg : ∀ s t, s ≈ t → g s ≈ g t)
    (hf1 : f one ≈ c) (hg0 : g zero ≈ c) : value f g c midpoint ≈ c :=
  Setoid.trans (cancel_right _ _ c (Setoid.trans (hg _ _ rightParameter_midpoint) hg0))
    (Setoid.trans (hf _ _ leftParameter_midpoint) hf1)

theorem image (f g : Point → Scalar) (c : Scalar)
    (hf : ∀ s t, s ≈ t → f s ≈ f t) (hg : ∀ s t, s ≈ t → g s ≈ g t)
    (hf1 : f one ≈ c) (hg0 : g zero ≈ c) (D : Scalar → Prop)
    (hD : ∀ z w, z ≈ w → (D z ↔ D w)) (hfd : ∀ t, D (f t)) (hgd : ∀ t, D (g t)) (t : Point) :
    D (value f g c t) := by
  rcases parameter_order_total t midpoint with ht | ht
  · exact (hD _ _ (first_piece f g c hf hg hg0 t ht)).2 (hfd _)
  · exact (hD _ _ (second_piece f g c hf hg hf1 t ht)).2 (hgd _)

theorem reversed (f g : Point → Scalar) (c : Scalar)
    (hf : ∀ s t, s ≈ t → f s ≈ f t) (hg : ∀ s t, s ≈ t → g s ≈ g t) (t : Point) :
    value f g c (reverse t) ≈ value (fun s => g (reverse s)) (fun s => f (reverse s)) c t := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (value f g c (reverse t)).property)
    (hright := (value (fun s => g (reverse s)) (fun s => f (reverse s)) c t).property)
  have hF := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := (f (leftParameter (reverse t))).property)
    (hright := (f (reverse (rightParameter t))).property) (hf _ _ (leftParameter_reverse t))
  have hG := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := (g (rightParameter (reverse t))).property)
    (hright := (g (reverse (leftParameter t))).property) (hg _ _ (rightParameter_reverse t))
  let F := ComplexRawQuotient.ofRaw (f (leftParameter (reverse t))).val (f (leftParameter (reverse t))).property
  let G := ComplexRawQuotient.ofRaw (g (rightParameter (reverse t))).val (g (rightParameter (reverse t))).property
  let RF := ComplexRawQuotient.ofRaw (f (reverse (rightParameter t))).val (f (reverse (rightParameter t))).property
  let RG := ComplexRawQuotient.ofRaw (g (reverse (leftParameter t))).val (g (reverse (leftParameter t))).property
  let C := ComplexRawQuotient.ofRaw c.val c.property
  change F=RF at hF
  change G=RG at hG
  change (F+G)+ -C=(RG+RF)+ -C
  grind only

end ComputableAnalysis.RiemannHilbert.ScalarPathConcatenation
