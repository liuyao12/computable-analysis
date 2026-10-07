import ComputableAnalysis.ModularForms.UpperHorizontalRowSums
import ComputableAnalysis.ModularForms.UpperPositiveRowsSumPrefixes

/-! Removing horizontal truncation in the actual finite-row lattice approximations. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

private theorem sub_reverse (p q : ComplexRaw) (hp : p.Valid) (hq : q.Valid) :
    (neg (sub p q)).Equiv (sub q p) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := neg_valid (sub_valid hp hq)) (hright := sub_valid hq hp)
  change -(ComplexRawQuotient.ofRaw p hp-ComplexRawQuotient.ofRaw q hq)=
    ComplexRawQuotient.ofRaw q hq-ComplexRawQuotient.ofRaw p hp
  grind only

private theorem small_triangle (F p q : ComplexRaw) (hF : F.Valid) (hp : p.Valid) (hq : q.Valid)
    (a b : Rat) (h1 : Small (sub F p) a) (h2 : Small (sub p q) b) :
    Small (sub F q) (a+b) := by
  have he : (add (sub F p) (sub p q)).Equiv (sub F q) := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := add_valid (sub_valid hF hp) (sub_valid hp hq)) (hright := sub_valid hF hq)
    change (ComplexRawQuotient.ofRaw F hF-ComplexRawQuotient.ofRaw p hp)+
      (ComplexRawQuotient.ofRaw p hp-ComplexRawQuotient.ofRaw q hq)=
      ComplexRawQuotient.ofRaw F hF-ComplexRawQuotient.ofRaw q hq
    grind only
  exact Small.congr (add_valid (sub_valid hF hp) (sub_valid hp hq))
    (sub_valid hF hq) he (LocalODE.small_add h1 h2)

private theorem remove_truncation (F Q : ComplexRaw) (hF : F.Valid) (hQ : Q.Valid)
    (p : Nat → ComplexRaw) (hp : ∀ P, (p P).Valid) (B : Rat) (e : Nat → Rat)
    (he : ShrinksToZero e) (hFp : ∀ P, Small (sub F (p P)) B)
    (hQp : ∀ P, Small (sub Q (p P)) (e P)) : Small (sub F Q) B := by
  apply SeriesLimitLaws.small_closed _ B e he
  intro P
  exact small_triangle F (p P) Q hF (hp P) hQ B (e P) (hFp P)
    (Small.congr (neg_valid (sub_valid hQ (hp P))) (sub_valid (hp P) hQ)
      (sub_reverse Q (p P) hQ (hp P)) (SeriesLimitLaws.small_neg (hQp P)))

private theorem pair_close (H h S s : ComplexRaw)
    (hH : H.Valid) (hh : h.Valid) (hS : S.Valid) (hs : s.Valid) (a b : Rat)
    (h1 : Small (sub H h) a) (h2 : Small (sub S s) b) :
    Small (sub (add H (scaleRat 2 S)) (add h (scaleRat 2 s))) (a+2*b) := by
  have hscale := represented_prefix_scale_close ⟨S,hS⟩ ⟨s,hs⟩ 2 b (by decide +kernel) h2
  exact Small.congr
    (add_valid (sub_valid hH hh) (sub_valid (scaleRat_valid hS) (scaleRat_valid hs)))
    (sub_valid (add_valid hH (scaleRat_valid hS)) (add_valid hh (scaleRat_valid hs)))
    (equiv_symm (SeriesLimitLaws.addition_difference _ _ _ _ hH hh
      (scaleRat_valid hS) (scaleRat_valid hs))) (LocalODE.small_add h1 hscale)

private def rowWidthIndex (z : Scalar) (N P : Nat) : Nat :=
  4*upperPositiveRowsCutoff z N+P+N

private theorem rowWidthIndex_spec (z : Scalar) (N P : Nat) :
    rowWidthIndex z N P+1=4*upperPositiveRowsCutoff z N+(P+N+1) ∧ N≤rowWidthIndex z N P+1 := by
  unfold rowWidthIndex
  omega

private theorem rowError_shrinks (z : Scalar) (rate : Nat → Rat) (hrate : ShrinksToZero rate)
    (k N : Nat) :
    ShrinksToZero (fun P => rate (rowWidthIndex z N P)+
      2*((N:Rat)*(((2*32^k:Nat):Rat)*(((P+N+1:Nat):Rat))⁻¹))) := by
  have h1 : ShrinksToZero (fun P => rate (rowWidthIndex z N P)) := by
    have he : (fun P => rate (rowWidthIndex z N P))=
        (fun P => rate (P+(4*upperPositiveRowsCutoff z N+N))) := by
      funext P
      congr 1
      unfold rowWidthIndex
      omega
    rw [he]
    exact SeriesLimitLaws.shrinks_shift rate hrate _
  have h2 := SeriesLimitLaws.shrinks_shift _
    (upperPositiveLatticeRowsLimitPrefix_error_shrinks k N) N
  exact RepresentedCauchySum.sum_shrinks _ _ h1
    (SeriesLimitLaws.shrinks_scale _ h2 2 (by decide +kernel))

/-- The full lattice sum is uniformly close to the horizontal sum plus finitely many infinite rows. -/
theorem upperWeightFourLatticeSum_close_infiniteRowsPrefix (z : Scalar)
    (hz : InUpperHalfPlane z.val) (N : Nat) (hN : 0<N) :
    Small (sub (upperWeightFourLatticeSum z hz)
      (add (upperHorizontalWeightFourSum z hz)
        (scaleRat 2 (upperPositiveLatticeRowsLimitPrefix z hz 4 (by omega) N))))
      (2*upperWeightFourTailConstant z hz*reciprocalSquare N) := by
  let Q := add (upperHorizontalWeightFourSum z hz)
    (scaleRat 2 (upperPositiveLatticeRowsLimitPrefix z hz 4 (by omega) N))
  have hQ : Q.Valid := add_valid (upperHorizontalWeightFourSum_valid z hz)
    (scaleRat_valid (upperPositiveLatticeRowsLimitPrefix_valid z hz 4 (by omega) N))
  let p := fun P => upperWideRectangleSum z hz 4 (rowWidthIndex z N P+1) N
  have hp P : (p P).Valid := upperWideRectangleSum_valid z hz 4 _ N
  apply remove_truncation _ Q (upperWeightFourLatticeSum_valid z hz) hQ p hp _
    (fun P => upperWeightFourTailRate z hz (rowWidthIndex z N P)+
      2*((N:Rat)*(((2*32^4:Nat):Rat)*(((P+N+1:Nat):Rat))⁻¹)))
    (rowError_shrinks z _ (upperWeightFourTailRate_shrinks z hz) 4 N)
  · intro P
    exact upperWeightFourLatticeSum_close_wideRectangle z hz _ N hN (rowWidthIndex_spec z N P).2
  · intro P
    have hc := upperPositiveLatticeRowsLimitPrefix_canonical_close z hz 4 (by omega) N (P+N)
    have hw := rowWidthIndex_spec z N P
    have hh := upperHorizontalWeightFourSum_close_prefix z hz (rowWidthIndex z N P)
    have hpair := pair_close _ _ _ _ (upperHorizontalWeightFourSum_valid z hz)
      (upperLatticeFiniteRow z hz 4 (rowWidthIndex z N P+1) 0).property
      (upperPositiveLatticeRowsLimitPrefix_valid z hz 4 (by omega) N)
      (upperLatticePositiveRowsPrefix_valid z hz 4 (rowWidthIndex z N P+1) N) _ _ hh (by
        rw [hw.1]
        exact hc)
    have he := equiv_trans (upperWideRectangleSum_valid z hz 4 (rowWidthIndex z N P+1) N)
      (upperLatticeFiniteRowsSum_valid z hz 4 (rowWidthIndex z N P+1) N)
      (add_valid (upperLatticeFiniteRow z hz 4 (rowWidthIndex z N P+1) 0).property
        (scaleRat_valid (upperLatticePositiveRowsPrefix_valid z hz 4 (rowWidthIndex z N P+1) N)))
      (upperWideRectangleSum_rows z hz 4 _ N hw.2)
      (upperLatticeFiniteRowsSum_even_positiveRows z hz 2 _ N)
    exact Small.congr
      (sub_valid hQ (add_valid (upperLatticeFiniteRow z hz 4 (rowWidthIndex z N P+1) 0).property
        (scaleRat_valid (upperLatticePositiveRowsPrefix_valid z hz 4 (rowWidthIndex z N P+1) N))))
      (sub_valid hQ (hp P))
      (FunctionTheory.sub_congr (equiv_refl _ hQ) (equiv_symm he)) hpair

theorem upperWeightSixLatticeSum_close_infiniteRowsPrefix (z : Scalar)
    (hz : InUpperHalfPlane z.val) (N : Nat) (hN : 0<N) :
    Small (sub (upperWeightSixLatticeSum z hz)
      (add (upperHorizontalWeightSixSum z hz)
        (scaleRat 2 (upperPositiveLatticeRowsLimitPrefix z hz 6 (by omega) N))))
      (2*upperWeightSixTailConstant z hz*reciprocalSquare N) := by
  let Q := add (upperHorizontalWeightSixSum z hz)
    (scaleRat 2 (upperPositiveLatticeRowsLimitPrefix z hz 6 (by omega) N))
  have hQ : Q.Valid := add_valid (upperHorizontalWeightSixSum_valid z hz)
    (scaleRat_valid (upperPositiveLatticeRowsLimitPrefix_valid z hz 6 (by omega) N))
  let p := fun P => upperWideRectangleSum z hz 6 (rowWidthIndex z N P+1) N
  have hp P : (p P).Valid := upperWideRectangleSum_valid z hz 6 _ N
  apply remove_truncation _ Q (upperWeightSixLatticeSum_valid z hz) hQ p hp _
    (fun P => upperWeightSixTailRate z hz (rowWidthIndex z N P)+
      2*((N:Rat)*(((2*32^6:Nat):Rat)*(((P+N+1:Nat):Rat))⁻¹)))
    (rowError_shrinks z _ (upperWeightSixTailRate_shrinks z hz) 6 N)
  · intro P
    exact upperWeightSixLatticeSum_close_wideRectangle z hz _ N hN (rowWidthIndex_spec z N P).2
  · intro P
    have hc := upperPositiveLatticeRowsLimitPrefix_canonical_close z hz 6 (by omega) N (P+N)
    have hw := rowWidthIndex_spec z N P
    have hh := upperHorizontalWeightSixSum_close_prefix z hz (rowWidthIndex z N P)
    have hpair := pair_close _ _ _ _ (upperHorizontalWeightSixSum_valid z hz)
      (upperLatticeFiniteRow z hz 6 (rowWidthIndex z N P+1) 0).property
      (upperPositiveLatticeRowsLimitPrefix_valid z hz 6 (by omega) N)
      (upperLatticePositiveRowsPrefix_valid z hz 6 (rowWidthIndex z N P+1) N) _ _ hh (by
        rw [hw.1]
        exact hc)
    have he := equiv_trans (upperWideRectangleSum_valid z hz 6 (rowWidthIndex z N P+1) N)
      (upperLatticeFiniteRowsSum_valid z hz 6 (rowWidthIndex z N P+1) N)
      (add_valid (upperLatticeFiniteRow z hz 6 (rowWidthIndex z N P+1) 0).property
        (scaleRat_valid (upperLatticePositiveRowsPrefix_valid z hz 6 (rowWidthIndex z N P+1) N)))
      (upperWideRectangleSum_rows z hz 6 _ N hw.2)
      (upperLatticeFiniteRowsSum_even_positiveRows z hz 3 _ N)
    exact Small.congr
      (sub_valid hQ (add_valid (upperLatticeFiniteRow z hz 6 (rowWidthIndex z N P+1) 0).property
        (scaleRat_valid (upperLatticePositiveRowsPrefix_valid z hz 6 (rowWidthIndex z N P+1) N))))
      (sub_valid hQ (hp P))
      (FunctionTheory.sub_congr (equiv_refl _ hQ) (equiv_symm he)) hpair

end ComputableAnalysis.ModularForms
