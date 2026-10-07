import ComputableAnalysis.ModularForms.UpperRowLimitComparison

/-! Exact comparison of the constructed lattice sums with their actual iterated row sums. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

private theorem fixed_add_scale_close (a x y : ComplexRaw)
    (ha : a.Valid) (hx : x.Valid) (hy : y.Valid) (c E : Rat) (hc : 0≤c)
    (he : Small (sub x y) E) :
    Small (sub (add a (scaleRat c x)) (add a (scaleRat c y))) (c*E) := by
  have hscale := represented_prefix_scale_close ⟨x,hx⟩ ⟨y,hy⟩ c E hc he
  have heq : (sub (scaleRat c x) (scaleRat c y)).Equiv
      (sub (add a (scaleRat c x)) (add a (scaleRat c y))) := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := sub_valid (scaleRat_valid hx) (scaleRat_valid hy))
      (hright := sub_valid (add_valid ha (scaleRat_valid hx)) (add_valid ha (scaleRat_valid hy)))
    let A := ComplexRawQuotient.ofRaw a ha
    let X := ComplexRawQuotient.ofRaw (scaleRat c x) (scaleRat_valid hx)
    let Y := ComplexRawQuotient.ofRaw (scaleRat c y) (scaleRat_valid hy)
    change X-Y=(A+X)-(A+Y)
    generalize A=a,X=x,Y=y
    grind only
  exact Small.congr (sub_valid (scaleRat_valid hx) (scaleRat_valid hy))
    (sub_valid (add_valid ha (scaleRat_valid hx)) (add_valid ha (scaleRat_valid hy))) heq hscale

private theorem squaredRate_shrinks (C : Rat) (hC : 0≤C) :
    ShrinksToZero (fun N => 2*C*reciprocalSquare (N+2)) := by
  have hbase : ShrinksToZero (fun N => reciprocalSquare (N+1)) := by
    apply shrinksToZero_of_natOverSuccBound (C := 1)
    intro N
    change reciprocalSquare (N+1)≤1/((N+1:Nat):Rat)
    exact reciprocalSquare_le_reciprocal (N+1) (by omega)
  have hs := SeriesLimitLaws.shrinks_shift _ hbase 1
  have hshift : ShrinksToZero (fun N => reciprocalSquare (N+2)) := by
    simpa only [Nat.add_assoc] using hs
  exact SeriesLimitLaws.shrinks_scale _ hshift (2*C)
    (Rat.mul_nonneg (by decide +kernel) hC)

private theorem prefix_unique_two_errors (F G : ComplexRaw) (hF : F.Valid) (hG : G.Valid)
    (p : Nat → ComplexRaw) (hp : ∀ N, (p N).Valid) (C : Rat) (hC : 0≤C)
    (hFp : ∀ N, Small (sub F (p N)) (2*C*reciprocalSquare (N+2)))
    (hGp : ∀ N, Small (sub G (p N)) (2*(C*(((N+1:Nat):Rat))⁻¹))) : F.Equiv G := by
  let e := fun N => 2*C*reciprocalSquare (N+2)
  let s := fun N => 2*(C*(((N+1:Nat):Rat))⁻¹)
  have he : ShrinksToZero e := squaredRate_shrinks C hC
  have hs : ShrinksToZero s := SeriesLimitLaws.shrinks_scale _
    (rationalInverseSquareRate_shrinks C hC) 2 (by decide +kernel)
  have he0 (N : Nat) : 0≤e N := by
    have hn : (0:Rat)<((N+2:Nat):Rat) := by exact_mod_cast (show 0<N+2 by omega)
    exact Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) hC)
      (Rat.le_of_lt (Rat.inv_pos.mpr (Rat.mul_pos hn hn)))
  have hs0 (N : Nat) : 0≤s N := by
    have hn : (0:Rat)<((N+1:Nat):Rat) := by exact_mod_cast (show 0<N+1 by omega)
    exact Rat.mul_nonneg (by decide +kernel)
      (Rat.mul_nonneg hC (Rat.le_of_lt (Rat.inv_pos.mpr hn)))
  apply RepresentedCauchySum.unique p hp (fun N => e N+s N)
    (RepresentedCauchySum.sum_shrinks e s he hs) F G hF hG
  · intro N
    exact (hFp N).mono (by have := hs0 N; dsimp [e,s]; grind only)
  · intro N
    exact (hGp N).mono (by have := he0 N; dsimp [e,s]; grind only)

/-- The actual weight-four lattice sum equals the horizontal row plus twice all positive rows. -/
theorem upperWeightFourLatticeSum_iteratedRows (z : Scalar)
    (hz : InUpperHalfPlane z.val) :
    (upperWeightFourLatticeSum z hz).Equiv
      (add (upperHorizontalWeightFourSum z hz) (scaleRat 2 (upperPositiveWeightFourRowsSum z hz))) := by
  let G := add (upperHorizontalWeightFourSum z hz) (scaleRat 2 (upperPositiveWeightFourRowsSum z hz))
  have hG : G.Valid := add_valid (upperHorizontalWeightFourSum_valid z hz)
    (scaleRat_valid (upperPositiveWeightFourRowsSum_valid z hz))
  let p := fun N => add (upperHorizontalWeightFourSum z hz)
    (scaleRat 2 (upperPositiveLatticeRowsLimitPrefix z hz 4 (by omega) (N+2)))
  have hp N : (p N).Valid := add_valid (upperHorizontalWeightFourSum_valid z hz)
    (scaleRat_valid (upperPositiveLatticeRowsLimitPrefix_valid z hz 4 (by omega) (N+2)))
  have hC : 0≤upperWeightFourTailConstant z hz := by
    unfold upperWeightFourTailConstant
    exact Rat.mul_nonneg (by decide +kernel)
      (Rat.pow_nonneg (Rat.mul_nonneg (by decide +kernel) (latticeReciprocalConstant_nonnegative z hz)))
  apply prefix_unique_two_errors _ G (upperWeightFourLatticeSum_valid z hz) hG p hp _ hC
  · intro N
    exact upperWeightFourLatticeSum_close_infiniteRowsPrefix z hz (N+2) (by omega)
  · intro N
    exact fixed_add_scale_close _ _ _ (upperHorizontalWeightFourSum_valid z hz)
      (upperPositiveWeightFourRowsSum_valid z hz)
      (upperPositiveLatticeRowsLimitPrefix_valid z hz 4 (by omega) (N+2)) 2 _ (by decide +kernel)
      (upperPositiveWeightFourRowsSum_close_prefix z hz N)

/-- The actual weight-six lattice sum has the same justified iterated-row decomposition. -/
theorem upperWeightSixLatticeSum_iteratedRows (z : Scalar)
    (hz : InUpperHalfPlane z.val) :
    (upperWeightSixLatticeSum z hz).Equiv
      (add (upperHorizontalWeightSixSum z hz) (scaleRat 2 (upperPositiveWeightSixRowsSum z hz))) := by
  let G := add (upperHorizontalWeightSixSum z hz) (scaleRat 2 (upperPositiveWeightSixRowsSum z hz))
  have hG : G.Valid := add_valid (upperHorizontalWeightSixSum_valid z hz)
    (scaleRat_valid (upperPositiveWeightSixRowsSum_valid z hz))
  let p := fun N => add (upperHorizontalWeightSixSum z hz)
    (scaleRat 2 (upperPositiveLatticeRowsLimitPrefix z hz 6 (by omega) (N+2)))
  have hp N : (p N).Valid := add_valid (upperHorizontalWeightSixSum_valid z hz)
    (scaleRat_valid (upperPositiveLatticeRowsLimitPrefix_valid z hz 6 (by omega) (N+2)))
  have hC : 0≤upperWeightSixTailConstant z hz := by
    unfold upperWeightSixTailConstant
    exact Rat.mul_nonneg (by decide +kernel)
      (Rat.pow_nonneg (Rat.mul_nonneg (by decide +kernel) (latticeReciprocalConstant_nonnegative z hz)))
  apply prefix_unique_two_errors _ G (upperWeightSixLatticeSum_valid z hz) hG p hp _ hC
  · intro N
    exact upperWeightSixLatticeSum_close_infiniteRowsPrefix z hz (N+2) (by omega)
  · intro N
    exact fixed_add_scale_close _ _ _ (upperHorizontalWeightSixSum_valid z hz)
      (upperPositiveWeightSixRowsSum_valid z hz)
      (upperPositiveLatticeRowsLimitPrefix_valid z hz 6 (by omega) (N+2)) 2 _ (by decide +kernel)
      (upperPositiveWeightSixRowsSum_close_prefix z hz N)

end ComputableAnalysis.ModularForms
