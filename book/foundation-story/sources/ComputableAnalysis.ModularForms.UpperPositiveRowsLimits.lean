import ComputableAnalysis.ModularForms.UpperPositiveSquareAssembly

/-! Actual positive-row limits and quantitative comparison with finite horizontal cutoffs. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

/-- The independently constructed infinite positive-height lattice row. -/
def upperPositiveLatticeRowSum (z : Scalar) (hz : InUpperHalfPlane z.val)
    (k : Nat) (hk : 2≤k) (n : Nat) : Scalar :=
  integerReciprocalPowerRowSum (integerScaleScalar z ((n+1:Nat):Int))
    (integerScaleScalar_upper z hz _ (by omega)) k hk

/-- A finite sum of actual infinite rows; no change of infinite summation order is assumed. -/
def upperPositiveLatticeRowsLimitPrefix (z : Scalar) (hz : InUpperHalfPlane z.val)
    (k : Nat) (hk : 2≤k) (N : Nat) : ComplexRaw :=
  ScalarSeries.block (fun n => (upperPositiveLatticeRowSum z hz k hk n).val) 0 N

theorem upperPositiveLatticeRowsLimitPrefix_valid (z : Scalar)
    (hz : InUpperHalfPlane z.val) (k : Nat) (hk : 2≤k) (N : Nat) :
    (upperPositiveLatticeRowsLimitPrefix z hz k hk N).Valid :=
  ScalarSeries.block_valid _ (fun n => (upperPositiveLatticeRowSum z hz k hk n).property) 0 N

theorem upperLatticeFiniteRow_positive_canonical_close (z : Scalar)
    (hz : InUpperHalfPlane z.val) (k B : Nat) (hk : 2≤k) (n : Nat)
    (hB : Small (integerScaleScalar z ((n+1:Nat):Int)).val (B:Rat)) (P : Nat) :
    Small (sub (upperPositiveLatticeRowSum z hz k hk n).val
      (upperLatticeFiniteRow z hz k (4*B+(P+1)) ((n+1:Nat):Int)).val)
      (((2*32^k:Nat):Rat)*(((P+1:Nat):Rat))⁻¹) := by
  let w := integerScaleScalar z ((n+1:Nat):Int)
  have hw := integerScaleScalar_upper z hz ((n+1:Nat):Int) (by omega)
  have he := integerPowerRowAssembly_cutoff_agreement w hw k (pairedDerivativeCutoff w) B hk
    (pairedDerivativeCutoff_small w) hB
  exact Small.congr
    (sub_valid (integerPowerRowAssembly_valid w hw k B hk hB)
      (upperLatticeFiniteRow z hz k _ ((n+1:Nat):Int)).property)
    (sub_valid (upperPositiveLatticeRowSum z hz k hk n).property
      (upperLatticeFiniteRow z hz k _ ((n+1:Nat):Int)).property)
    (FunctionTheory.sub_congr (equiv_symm he)
      (equiv_refl _ (upperLatticeFiniteRow z hz k _ ((n+1:Nat):Int)).property))
    (upperLatticeFiniteRow_positive_close z hz k B hk _ (by omega) hB P)

private theorem block_error (f g : Nat → ComplexRaw)
    (hf : ∀ n, (f n).Valid) (hg : ∀ n, (g n).Valid) (E : Rat) (N : Nat)
    (he : ∀ n, n<N → Small (sub (f n) (g n)) E) :
    Small (sub (ScalarSeries.block f 0 N) (ScalarSeries.block g 0 N)) ((N:Rat)*E) := by
  induction N with
  | zero =>
    have hz : (sub ComplexRaw.zero ComplexRaw.zero).Equiv ComplexRaw.zero := by
      apply ComplexRawQuotient.equiv_of_ofRaw_eq
        (hleft := sub_valid (ofQComplex_valid _) (ofQComplex_valid _))
        (hright := ofQComplex_valid _)
      change (0:ScalarAlgebra.Value)-0=0
      grind only
    change Small (sub ComplexRaw.zero ComplexRaw.zero) ((0:Rat)*E)
    rw [Rat.zero_mul]
    exact Small.congr (ofQComplex_valid _) (sub_valid (ofQComplex_valid _) (ofQComplex_valid _))
      (equiv_symm hz) (Small.zero (by decide +kernel))
  | succ N ih =>
    have hb := LocalODE.small_add (ih (fun n hn => he n (by omega))) (he N (by omega))
    have hr : (N:Rat)*E+E=((N+1:Nat):Rat)*E := by
      rw [Rat.natCast_add]
      grind only
    rw [hr] at hb
    exact Small.congr
      (add_valid (sub_valid (ScalarSeries.block_valid f hf 0 N) (ScalarSeries.block_valid g hg 0 N))
        (sub_valid (hf N) (hg N)))
      (sub_valid (ScalarSeries.block_valid f hf 0 (N+1)) (ScalarSeries.block_valid g hg 0 (N+1)))
      (equiv_symm (by
        simp only [ScalarSeries.block.eq_2,Nat.zero_add]
        exact SeriesLimitLaws.addition_difference _ _ _ _
          (ScalarSeries.block_valid f hf 0 N) (ScalarSeries.block_valid g hg 0 N) (hf N) (hg N))) hb

/-- Horizontal truncation may be removed for any finite set of actual positive rows. -/
theorem upperPositiveLatticeRowsLimitPrefix_close (z : Scalar)
    (hz : InUpperHalfPlane z.val) (k B N : Nat) (hk : 2≤k)
    (hB : ∀ n, n<N → Small (integerScaleScalar z ((n+1:Nat):Int)).val (B:Rat)) (P : Nat) :
    Small (sub (upperPositiveLatticeRowsLimitPrefix z hz k hk N)
      (upperLatticePositiveRowsPrefix z hz k (4*B+(P+1)) N))
      ((N:Rat)*(((2*32^k:Nat):Rat)*(((P+1:Nat):Rat))⁻¹)) :=
  block_error (fun n => (upperPositiveLatticeRowSum z hz k hk n).val)
    (fun n => (upperLatticeFiniteRow z hz k (4*B+(P+1)) ((n+1:Nat):Int)).val)
    (fun n => (upperPositiveLatticeRowSum z hz k hk n).property)
    (fun n => (upperLatticeFiniteRow z hz k _ ((n+1:Nat):Int)).property) _ N
    (fun n hn => upperLatticeFiniteRow_positive_canonical_close z hz k B hk n (hB n hn) P)

theorem upperPositiveLatticeRowsLimitPrefix_error_shrinks (k N : Nat) :
    ShrinksToZero (fun P => (N:Rat)*(((2*32^k:Nat):Rat)*(((P+1:Nat):Rat))⁻¹)) := by
  have h : ShrinksToZero (fun P => (((2*32^k:Nat):Rat)*(((P+1:Nat):Rat))⁻¹)) := by
    apply shrinksToZero_of_natOverSuccBound (C := 2*32^k)
    intro P
    rw [Rat.div_def]
    exact Rat.le_refl
  exact SeriesLimitLaws.shrinks_scale _ h (N:Rat) (by exact_mod_cast (show 0≤N by omega))

/-- A constructed common cutoff for the first finitely many scaled row inputs. -/
def upperPositiveRowsCutoff (z : Scalar) : Nat → Nat
  | 0 => 0
  | N+1 => upperPositiveRowsCutoff z N+
      pairedDerivativeCutoff (integerScaleScalar z ((N+1:Nat):Int))

private theorem upperPositiveRowsCutoff_dominates (z : Scalar) (N n : Nat) (hn : n<N) :
    pairedDerivativeCutoff (integerScaleScalar z ((n+1:Nat):Int))≤upperPositiveRowsCutoff z N := by
  induction N with
  | zero => omega
  | succ N ih =>
    simp only [upperPositiveRowsCutoff]
    by_cases hlt : n<N
    · have hb := ih hlt
      omega
    · have he : n=N := by omega
      subst n
      omega

theorem upperPositiveRowsCutoff_small (z : Scalar) (N n : Nat) (hn : n<N) :
    Small (integerScaleScalar z ((n+1:Nat):Int)).val ((upperPositiveRowsCutoff z N):Rat) :=
  (pairedDerivativeCutoff_small (integerScaleScalar z ((n+1:Nat):Int))).mono
    (by exact_mod_cast upperPositiveRowsCutoff_dominates z N n hn)

/-- No cutoff evidence is required to approximate a finite prefix of actual infinite rows. -/
theorem upperPositiveLatticeRowsLimitPrefix_canonical_close (z : Scalar)
    (hz : InUpperHalfPlane z.val) (k : Nat) (hk : 2≤k) (N P : Nat) :
    Small (sub (upperPositiveLatticeRowsLimitPrefix z hz k hk N)
      (upperLatticePositiveRowsPrefix z hz k (4*upperPositiveRowsCutoff z N+(P+1)) N))
      ((N:Rat)*(((2*32^k:Nat):Rat)*(((P+1:Nat):Rat))⁻¹)) :=
  upperPositiveLatticeRowsLimitPrefix_close z hz k (upperPositiveRowsCutoff z N) N hk
    (upperPositiveRowsCutoff_small z N) P

theorem upperPositiveLatticeRowSum_congr (z w : Scalar)
    (hz : InUpperHalfPlane z.val) (hw : InUpperHalfPlane w.val) (he : z.val.Equiv w.val)
    (k : Nat) (hk : 2≤k) (n : Nat) :
    (upperPositiveLatticeRowSum z hz k hk n).val.Equiv
      (upperPositiveLatticeRowSum w hw k hk n).val :=
  integerReciprocalPowerRowSum_congr (integerScaleScalar z ((n+1:Nat):Int))
    (integerScaleScalar w ((n+1:Nat):Int))
    (integerScaleScalar_upper z hz _ (by omega))
    (integerScaleScalar_upper w hw _ (by omega))
    (integerAffine_equiv _ _ he) k hk

theorem upperPositiveLatticeRowsLimitPrefix_congr (z w : Scalar)
    (hz : InUpperHalfPlane z.val) (hw : InUpperHalfPlane w.val) (he : z.val.Equiv w.val)
    (k : Nat) (hk : 2≤k) (N : Nat) :
    (upperPositiveLatticeRowsLimitPrefix z hz k hk N).Equiv
      (upperPositiveLatticeRowsLimitPrefix w hw k hk N) :=
  ScalarSeries.block_congr _ _ (upperPositiveLatticeRowSum_congr z w hz hw he k hk) 0 N

end ComputableAnalysis.ModularForms
