import ComputableAnalysis.ModularForms.NomeMomentLimitLinearity
import ComputableAnalysis.ModularForms.NomeMomentQuadraticReduction

/-! Actual cubic backward-difference sum reduces to lower polynomial moments. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

theorem polynomialNomeMomentRatio_three (r : Rat) : polynomialNomeMomentRatio r 3=16*r := by
  simp only [polynomialNomeMomentRatio,Rat.pow_succ,Rat.pow_zero,Rat.one_mul]
  grind only

theorem polynomialNomeDifferenceSum_degree_three (z : Scalar) (r : Rat) (hr : 0≤r)
    (hlocal : 16*r≤(1:Rat)/2) (hz : Small z.val r) :
    (polynomialNomeDifferenceSum z r 3).Equiv
      (add (sub (scaleRat 3 (polynomialNomeMomentSum z r 2))
        (scaleRat 3 (polynomialNomeMomentSum z r 1))) (polynomialNomeMomentSum z r 0)) := by
  have hl0 : polynomialNomeMomentRatio r 0≤(1:Rat)/2 := by rw [polynomialNomeMomentRatio_zero]; grind only
  have hl1 : polynomialNomeMomentRatio r 1≤(1:Rat)/2 := by rw [polynomialNomeMomentRatio_one]; grind only
  have hl2 : polynomialNomeMomentRatio r 2≤(1:Rat)/2 := by rw [polynomialNomeMomentRatio_two]; grind only
  have hl3 : polynomialNomeMomentRatio r 3≤(1:Rat)/2 := by rw [polynomialNomeMomentRatio_three]; exact hlocal
  let s0 : Scalar := ⟨_,polynomialNomeMomentSum_valid z r 0 hr hl0 hz⟩
  let s1 : Scalar := ⟨_,polynomialNomeMomentSum_valid z r 1 hr hl1 hz⟩
  let s2 : Scalar := ⟨_,polynomialNomeMomentSum_valid z r 2 hr hl2 hz⟩
  let p := fun k N => (⟨polynomialNomeMomentPrefix z k N,polynomialNomeMomentPrefix_valid z k N⟩ : Scalar)
  let e := fun (k N : Nat) => 4*r*(polynomialNomeMomentRatio r k)^N
  have he (k : Nat) (hk : polynomialNomeMomentRatio r k≤(1:Rat)/2) : ShrinksToZero (e k) :=
    LocalODE.tail_bound_shrinks r _ hr (polynomialNomeMomentRatio_nonneg r k hr) hk
  have hen k N : 0≤e k N := Rat.mul_nonneg (Rat.mul_nonneg (by decide) hr)
    (Rat.pow_nonneg (polynomialNomeMomentRatio_nonneg r k hr))
  let a : Scalar := ⟨sub (scaleRat 3 s2.val) (scaleRat 3 s1.val),sub_valid (scaleRat_valid s2.property) (scaleRat_valid s1.property)⟩
  let b := fun N => (⟨sub (scaleRat 3 (p 2 N).val) (scaleRat 3 (p 1 N).val),
    sub_valid (scaleRat_valid (p 2 N).property) (scaleRat_valid (p 1 N).property)⟩ : Scalar)
  let q := fun N => add (b N).val (p 0 N).val
  have vq N : (q N).Valid := add_valid (b N).property (p 0 N).property
  have hc N : Small (sub (add a.val s0.val) (q N)) ((3*e 2 N+3*e 1 N)+e 0 N) :=
    represented_prefix_add_close a s0 (b N) (p 0 N) _ _
      (represented_prefix_sub_close
        ⟨scaleRat 3 s2.val,scaleRat_valid s2.property⟩ ⟨scaleRat 3 s1.val,scaleRat_valid s1.property⟩
        ⟨scaleRat 3 (p 2 N).val,scaleRat_valid (p 2 N).property⟩ ⟨scaleRat 3 (p 1 N).val,scaleRat_valid (p 1 N).property⟩ _ _
        (represented_prefix_scale_close s2 (p 2 N) 3 _ (by decide) (polynomialNomeMomentSum_close z r 2 hr hl2 hz N))
        (represented_prefix_scale_close s1 (p 1 N) 3 _ (by decide) (polynomialNomeMomentSum_close z r 1 hr hl1 hz N)))
      (polynomialNomeMomentSum_close z r 0 hr hl0 hz N)
  have hcomb := RepresentedCauchySum.sum_shrinks _ _
    (RepresentedCauchySum.sum_shrinks _ _ (SeriesLimitLaws.shrinks_scale _ (he 2 hl2) 3 (by decide))
      (SeriesLimitLaws.shrinks_scale _ (he 1 hl1) 3 (by decide))) (he 0 hl0)
  have vd := polynomialNomeDifferenceSum_valid z r 3 hr hl3 hz
  apply RepresentedCauchySum.unique q vq
    (fun N => e 3 N+((3*e 2 N+3*e 1 N)+e 0 N))
    (RepresentedCauchySum.sum_shrinks _ _ (he 3 hl3) hcomb) _ _ vd (add_valid a.property s0.property)
  · intro N
    have h := Small.congr
      (sub_valid vd (ScalarSeries.block_valid _ (polynomialNomeDifferenceTerm_valid z 3) 0 N))
      (sub_valid vd (vq N))
      (FunctionTheory.sub_congr (equiv_refl _ vd) (polynomialNomeDifferencePrefix_degree_3 z N))
      (polynomialNomeDifferenceSum_close z r 3 hr hl3 hz N)
    exact h.mono (by have h2 := hen 2 N; have h1 := hen 1 N; have h0 := hen 0 N; grind only)
  · intro N
    exact (hc N).mono (by have h3 := hen 3 N; grind only)

end ComputableAnalysis.ModularForms
