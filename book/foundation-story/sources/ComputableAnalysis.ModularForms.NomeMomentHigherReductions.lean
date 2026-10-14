import ComputableAnalysis.ModularForms.NomeMomentCubicQuotient

/-! Actual quartic and quintic difference sums reduce to lower moments. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

theorem polynomialNomeMomentRatio_four (r : Rat) : polynomialNomeMomentRatio r 4=32*r := by
  simp only [polynomialNomeMomentRatio,Rat.pow_succ,Rat.pow_zero,Rat.one_mul]
  grind only

theorem polynomialNomeDifferenceSum_degree_four (z : Scalar) (r : Rat) (hr : 0≤r)
    (hlocal : 32*r≤(1:Rat)/2) (hz : Small z.val r) :
    (polynomialNomeDifferenceSum z r 4).Equiv (sub (add (sub (scaleRat 4 (polynomialNomeMomentSum z r 3)) (scaleRat 6 (polynomialNomeMomentSum z r 2))) (scaleRat 4 (polynomialNomeMomentSum z r 1))) (polynomialNomeMomentSum z r 0)) := by
  have hl0 : polynomialNomeMomentRatio r 0≤(1:Rat)/2 := by rw [polynomialNomeMomentRatio_zero]; grind only
  have hl1 : polynomialNomeMomentRatio r 1≤(1:Rat)/2 := by rw [polynomialNomeMomentRatio_one]; grind only
  have hl2 : polynomialNomeMomentRatio r 2≤(1:Rat)/2 := by rw [polynomialNomeMomentRatio_two]; grind only
  have hl3 : polynomialNomeMomentRatio r 3≤(1:Rat)/2 := by rw [polynomialNomeMomentRatio_three]; grind only
  have hl4 : polynomialNomeMomentRatio r 4≤(1:Rat)/2 := by rw [polynomialNomeMomentRatio_four]; grind only
  let s0 : Scalar := ⟨_,polynomialNomeMomentSum_valid z r 0 hr hl0 hz⟩
  let s1 : Scalar := ⟨_,polynomialNomeMomentSum_valid z r 1 hr hl1 hz⟩
  let s2 : Scalar := ⟨_,polynomialNomeMomentSum_valid z r 2 hr hl2 hz⟩
  let s3 : Scalar := ⟨_,polynomialNomeMomentSum_valid z r 3 hr hl3 hz⟩
  let p := fun k N => (⟨polynomialNomeMomentPrefix z k N,polynomialNomeMomentPrefix_valid z k N⟩ : Scalar)
  let e := fun (k N : Nat) => 4*r*(polynomialNomeMomentRatio r k)^N
  have he (k : Nat) (hk : polynomialNomeMomentRatio r k≤(1:Rat)/2) : ShrinksToZero (e k) :=
    LocalODE.tail_bound_shrinks r _ hr (polynomialNomeMomentRatio_nonneg r k hr) hk
  have hen k N : 0≤e k N := Rat.mul_nonneg (Rat.mul_nonneg (by decide) hr)
    (Rat.pow_nonneg (polynomialNomeMomentRatio_nonneg r k hr))
  let q := fun N => (sub (add (sub (scaleRat 4 (p 3 N).val) (scaleRat 6 (p 2 N).val)) (scaleRat 4 (p 1 N).val)) (p 0 N).val)
  have vq N : (q N).Valid := (sub_valid (add_valid (sub_valid (scaleRat_valid (p 3 N).property) (scaleRat_valid (p 2 N).property)) (scaleRat_valid (p 1 N).property)) (p 0 N).property)
  have hc N : Small (sub (sub (add (sub (scaleRat 4 s3.val) (scaleRat 6 s2.val)) (scaleRat 4 s1.val)) s0.val) (q N)) ((((4*(e 3 N))+(6*(e 2 N)))+(4*(e 1 N)))+(e 0 N)) :=
    (represented_prefix_sub_close ⟨(add (sub (scaleRat 4 s3.val) (scaleRat 6 s2.val)) (scaleRat 4 s1.val)),(add_valid (sub_valid (scaleRat_valid s3.property) (scaleRat_valid s2.property)) (scaleRat_valid s1.property))⟩ ⟨s0.val,s0.property⟩ ⟨(add (sub (scaleRat 4 (p 3 N).val) (scaleRat 6 (p 2 N).val)) (scaleRat 4 (p 1 N).val)),(add_valid (sub_valid (scaleRat_valid (p 3 N).property) (scaleRat_valid (p 2 N).property)) (scaleRat_valid (p 1 N).property))⟩ ⟨(p 0 N).val,(p 0 N).property⟩ _ _ (represented_prefix_add_close ⟨(sub (scaleRat 4 s3.val) (scaleRat 6 s2.val)),(sub_valid (scaleRat_valid s3.property) (scaleRat_valid s2.property))⟩ ⟨(scaleRat 4 s1.val),(scaleRat_valid s1.property)⟩ ⟨(sub (scaleRat 4 (p 3 N).val) (scaleRat 6 (p 2 N).val)),(sub_valid (scaleRat_valid (p 3 N).property) (scaleRat_valid (p 2 N).property))⟩ ⟨(scaleRat 4 (p 1 N).val),(scaleRat_valid (p 1 N).property)⟩ _ _ (represented_prefix_sub_close ⟨(scaleRat 4 s3.val),(scaleRat_valid s3.property)⟩ ⟨(scaleRat 6 s2.val),(scaleRat_valid s2.property)⟩ ⟨(scaleRat 4 (p 3 N).val),(scaleRat_valid (p 3 N).property)⟩ ⟨(scaleRat 6 (p 2 N).val),(scaleRat_valid (p 2 N).property)⟩ _ _ (represented_prefix_scale_close ⟨s3.val,s3.property⟩ ⟨(p 3 N).val,(p 3 N).property⟩ 4 _ (by decide) (polynomialNomeMomentSum_close z r 3 hr hl3 hz N)) (represented_prefix_scale_close ⟨s2.val,s2.property⟩ ⟨(p 2 N).val,(p 2 N).property⟩ 6 _ (by decide) (polynomialNomeMomentSum_close z r 2 hr hl2 hz N))) (represented_prefix_scale_close ⟨s1.val,s1.property⟩ ⟨(p 1 N).val,(p 1 N).property⟩ 4 _ (by decide) (polynomialNomeMomentSum_close z r 1 hr hl1 hz N))) (polynomialNomeMomentSum_close z r 0 hr hl0 hz N))
  have hcomb : ShrinksToZero (fun N => ((((4*(e 3 N))+(6*(e 2 N)))+(4*(e 1 N)))+(e 0 N))) := (RepresentedCauchySum.sum_shrinks _ _ (RepresentedCauchySum.sum_shrinks _ _ (RepresentedCauchySum.sum_shrinks _ _ (SeriesLimitLaws.shrinks_scale _ (he 3 hl3) 4 (by decide)) (SeriesLimitLaws.shrinks_scale _ (he 2 hl2) 6 (by decide))) (SeriesLimitLaws.shrinks_scale _ (he 1 hl1) 4 (by decide))) (he 0 hl0))
  have vd := polynomialNomeDifferenceSum_valid z r 4 hr hl4 hz
  apply RepresentedCauchySum.unique q vq
    (fun N => e 4 N+((((4*(e 3 N))+(6*(e 2 N)))+(4*(e 1 N)))+(e 0 N)))
    (RepresentedCauchySum.sum_shrinks _ _ (he 4 hl4) hcomb) _ _ vd (sub_valid (add_valid (sub_valid (scaleRat_valid s3.property) (scaleRat_valid s2.property)) (scaleRat_valid s1.property)) s0.property)
  · intro N
    have h := Small.congr
      (sub_valid vd (ScalarSeries.block_valid _ (polynomialNomeDifferenceTerm_valid z 4) 0 N))
      (sub_valid vd (vq N))
      (FunctionTheory.sub_congr (equiv_refl _ vd) (polynomialNomeDifferencePrefix_degree_4 z N))
      (polynomialNomeDifferenceSum_close z r 4 hr hl4 hz N)
    exact h.mono (by
      have h0 := hen 0 N
      have h1 := hen 1 N
      have h2 := hen 2 N
      have h3 := hen 3 N
      grind only)
  · intro N
    exact (hc N).mono (by have hk := hen 4 N; grind only)

theorem polynomialNomeMomentRatio_five (r : Rat) : polynomialNomeMomentRatio r 5=64*r := by
  simp only [polynomialNomeMomentRatio,Rat.pow_succ,Rat.pow_zero,Rat.one_mul]
  grind only

theorem polynomialNomeDifferenceSum_degree_five (z : Scalar) (r : Rat) (hr : 0≤r)
    (hlocal : 64*r≤(1:Rat)/2) (hz : Small z.val r) :
    (polynomialNomeDifferenceSum z r 5).Equiv (add (sub (add (sub (scaleRat 5 (polynomialNomeMomentSum z r 4)) (scaleRat 10 (polynomialNomeMomentSum z r 3))) (scaleRat 10 (polynomialNomeMomentSum z r 2))) (scaleRat 5 (polynomialNomeMomentSum z r 1))) (polynomialNomeMomentSum z r 0)) := by
  have hl0 : polynomialNomeMomentRatio r 0≤(1:Rat)/2 := by rw [polynomialNomeMomentRatio_zero]; grind only
  have hl1 : polynomialNomeMomentRatio r 1≤(1:Rat)/2 := by rw [polynomialNomeMomentRatio_one]; grind only
  have hl2 : polynomialNomeMomentRatio r 2≤(1:Rat)/2 := by rw [polynomialNomeMomentRatio_two]; grind only
  have hl3 : polynomialNomeMomentRatio r 3≤(1:Rat)/2 := by rw [polynomialNomeMomentRatio_three]; grind only
  have hl4 : polynomialNomeMomentRatio r 4≤(1:Rat)/2 := by rw [polynomialNomeMomentRatio_four]; grind only
  have hl5 : polynomialNomeMomentRatio r 5≤(1:Rat)/2 := by rw [polynomialNomeMomentRatio_five]; grind only
  let s0 : Scalar := ⟨_,polynomialNomeMomentSum_valid z r 0 hr hl0 hz⟩
  let s1 : Scalar := ⟨_,polynomialNomeMomentSum_valid z r 1 hr hl1 hz⟩
  let s2 : Scalar := ⟨_,polynomialNomeMomentSum_valid z r 2 hr hl2 hz⟩
  let s3 : Scalar := ⟨_,polynomialNomeMomentSum_valid z r 3 hr hl3 hz⟩
  let s4 : Scalar := ⟨_,polynomialNomeMomentSum_valid z r 4 hr hl4 hz⟩
  let p := fun k N => (⟨polynomialNomeMomentPrefix z k N,polynomialNomeMomentPrefix_valid z k N⟩ : Scalar)
  let e := fun (k N : Nat) => 4*r*(polynomialNomeMomentRatio r k)^N
  have he (k : Nat) (hk : polynomialNomeMomentRatio r k≤(1:Rat)/2) : ShrinksToZero (e k) :=
    LocalODE.tail_bound_shrinks r _ hr (polynomialNomeMomentRatio_nonneg r k hr) hk
  have hen k N : 0≤e k N := Rat.mul_nonneg (Rat.mul_nonneg (by decide) hr)
    (Rat.pow_nonneg (polynomialNomeMomentRatio_nonneg r k hr))
  let q := fun N => (add (sub (add (sub (scaleRat 5 (p 4 N).val) (scaleRat 10 (p 3 N).val)) (scaleRat 10 (p 2 N).val)) (scaleRat 5 (p 1 N).val)) (p 0 N).val)
  have vq N : (q N).Valid := (add_valid (sub_valid (add_valid (sub_valid (scaleRat_valid (p 4 N).property) (scaleRat_valid (p 3 N).property)) (scaleRat_valid (p 2 N).property)) (scaleRat_valid (p 1 N).property)) (p 0 N).property)
  have hc N : Small (sub (add (sub (add (sub (scaleRat 5 s4.val) (scaleRat 10 s3.val)) (scaleRat 10 s2.val)) (scaleRat 5 s1.val)) s0.val) (q N)) (((((5*(e 4 N))+(10*(e 3 N)))+(10*(e 2 N)))+(5*(e 1 N)))+(e 0 N)) :=
    (represented_prefix_add_close ⟨(sub (add (sub (scaleRat 5 s4.val) (scaleRat 10 s3.val)) (scaleRat 10 s2.val)) (scaleRat 5 s1.val)),(sub_valid (add_valid (sub_valid (scaleRat_valid s4.property) (scaleRat_valid s3.property)) (scaleRat_valid s2.property)) (scaleRat_valid s1.property))⟩ ⟨s0.val,s0.property⟩ ⟨(sub (add (sub (scaleRat 5 (p 4 N).val) (scaleRat 10 (p 3 N).val)) (scaleRat 10 (p 2 N).val)) (scaleRat 5 (p 1 N).val)),(sub_valid (add_valid (sub_valid (scaleRat_valid (p 4 N).property) (scaleRat_valid (p 3 N).property)) (scaleRat_valid (p 2 N).property)) (scaleRat_valid (p 1 N).property))⟩ ⟨(p 0 N).val,(p 0 N).property⟩ _ _ (represented_prefix_sub_close ⟨(add (sub (scaleRat 5 s4.val) (scaleRat 10 s3.val)) (scaleRat 10 s2.val)),(add_valid (sub_valid (scaleRat_valid s4.property) (scaleRat_valid s3.property)) (scaleRat_valid s2.property))⟩ ⟨(scaleRat 5 s1.val),(scaleRat_valid s1.property)⟩ ⟨(add (sub (scaleRat 5 (p 4 N).val) (scaleRat 10 (p 3 N).val)) (scaleRat 10 (p 2 N).val)),(add_valid (sub_valid (scaleRat_valid (p 4 N).property) (scaleRat_valid (p 3 N).property)) (scaleRat_valid (p 2 N).property))⟩ ⟨(scaleRat 5 (p 1 N).val),(scaleRat_valid (p 1 N).property)⟩ _ _ (represented_prefix_add_close ⟨(sub (scaleRat 5 s4.val) (scaleRat 10 s3.val)),(sub_valid (scaleRat_valid s4.property) (scaleRat_valid s3.property))⟩ ⟨(scaleRat 10 s2.val),(scaleRat_valid s2.property)⟩ ⟨(sub (scaleRat 5 (p 4 N).val) (scaleRat 10 (p 3 N).val)),(sub_valid (scaleRat_valid (p 4 N).property) (scaleRat_valid (p 3 N).property))⟩ ⟨(scaleRat 10 (p 2 N).val),(scaleRat_valid (p 2 N).property)⟩ _ _ (represented_prefix_sub_close ⟨(scaleRat 5 s4.val),(scaleRat_valid s4.property)⟩ ⟨(scaleRat 10 s3.val),(scaleRat_valid s3.property)⟩ ⟨(scaleRat 5 (p 4 N).val),(scaleRat_valid (p 4 N).property)⟩ ⟨(scaleRat 10 (p 3 N).val),(scaleRat_valid (p 3 N).property)⟩ _ _ (represented_prefix_scale_close ⟨s4.val,s4.property⟩ ⟨(p 4 N).val,(p 4 N).property⟩ 5 _ (by decide) (polynomialNomeMomentSum_close z r 4 hr hl4 hz N)) (represented_prefix_scale_close ⟨s3.val,s3.property⟩ ⟨(p 3 N).val,(p 3 N).property⟩ 10 _ (by decide) (polynomialNomeMomentSum_close z r 3 hr hl3 hz N))) (represented_prefix_scale_close ⟨s2.val,s2.property⟩ ⟨(p 2 N).val,(p 2 N).property⟩ 10 _ (by decide) (polynomialNomeMomentSum_close z r 2 hr hl2 hz N))) (represented_prefix_scale_close ⟨s1.val,s1.property⟩ ⟨(p 1 N).val,(p 1 N).property⟩ 5 _ (by decide) (polynomialNomeMomentSum_close z r 1 hr hl1 hz N))) (polynomialNomeMomentSum_close z r 0 hr hl0 hz N))
  have hcomb : ShrinksToZero (fun N => (((((5*(e 4 N))+(10*(e 3 N)))+(10*(e 2 N)))+(5*(e 1 N)))+(e 0 N))) := (RepresentedCauchySum.sum_shrinks _ _ (RepresentedCauchySum.sum_shrinks _ _ (RepresentedCauchySum.sum_shrinks _ _ (RepresentedCauchySum.sum_shrinks _ _ (SeriesLimitLaws.shrinks_scale _ (he 4 hl4) 5 (by decide)) (SeriesLimitLaws.shrinks_scale _ (he 3 hl3) 10 (by decide))) (SeriesLimitLaws.shrinks_scale _ (he 2 hl2) 10 (by decide))) (SeriesLimitLaws.shrinks_scale _ (he 1 hl1) 5 (by decide))) (he 0 hl0))
  have vd := polynomialNomeDifferenceSum_valid z r 5 hr hl5 hz
  apply RepresentedCauchySum.unique q vq
    (fun N => e 5 N+(((((5*(e 4 N))+(10*(e 3 N)))+(10*(e 2 N)))+(5*(e 1 N)))+(e 0 N)))
    (RepresentedCauchySum.sum_shrinks _ _ (he 5 hl5) hcomb) _ _ vd (add_valid (sub_valid (add_valid (sub_valid (scaleRat_valid s4.property) (scaleRat_valid s3.property)) (scaleRat_valid s2.property)) (scaleRat_valid s1.property)) s0.property)
  · intro N
    have h := Small.congr
      (sub_valid vd (ScalarSeries.block_valid _ (polynomialNomeDifferenceTerm_valid z 5) 0 N))
      (sub_valid vd (vq N))
      (FunctionTheory.sub_congr (equiv_refl _ vd) (polynomialNomeDifferencePrefix_degree_5 z N))
      (polynomialNomeDifferenceSum_close z r 5 hr hl5 hz N)
    exact h.mono (by
      have h0 := hen 0 N
      have h1 := hen 1 N
      have h2 := hen 2 N
      have h3 := hen 3 N
      have h4 := hen 4 N
      grind only)
  · intro N
    exact (hc N).mono (by have hk := hen 5 N; grind only)

end ComputableAnalysis.ModularForms
