import ComputableAnalysis.ModularForms.LatticeBasisCauchy163

/-! Constructed reindexed CM lattice sums and exact basis independence. -/
namespace ComputableAnalysis.ModularForms
open RiemannHilbert FunctionTheory QuadraticOrder163

private theorem weightFourTailRate_nonnegative (n : Nat) : 0≤weightFourTailRate n := by
  have hp : (0:Rat)<((n+1:Nat):Rat) := by exact_mod_cast (show 0<n+1 by omega)
  exact Rat.mul_nonneg (by unfold weightFourTailConstant; decide +kernel)
    (Rat.le_of_lt (Rat.inv_pos.mpr (Rat.mul_pos hp hp)))

private theorem basisWeightFourCauchyRate_shrinks :
    ShrinksToZero (fun n => 6*weightFourTailRate n) :=
  SeriesLimitLaws.shrinks_scale _ weightFourTailRate_shrinks 6 (by decide +kernel)

def basisWeightFourLatticeSum163 (g : SL2Z) : ComplexRaw :=
  RepresentedCauchySum.value (basisReindexedPrefix g 4) (basisReindexedPrefix_valid g 4)
    (fun n => 6*weightFourTailRate n)

theorem basisWeightFourLatticeSum163_valid (g : SL2Z) : (basisWeightFourLatticeSum163 g).Valid :=
  RepresentedCauchySum.value_valid _ _ _ basisWeightFourCauchyRate_shrinks
    (basisWeightFourPrefix_cauchy g)

theorem basisWeightFourLatticeSum163_close_prefix (g : SL2Z) (n : Nat) :
    Small (ComplexRaw.sub (basisWeightFourLatticeSum163 g) (basisReindexedPrefix g 4 n))
      (6*weightFourTailRate n) :=
  RepresentedCauchySum.value_close_prefix _ _ _ (basisWeightFourPrefix_cauchy g) n

/-- The actual reindexed limit agrees exactly with the original CM lattice sum. -/
theorem basisWeightFourLatticeSum163_equiv (g : SL2Z) :
    (basisWeightFourLatticeSum163 g).Equiv weightFourLatticeSum163 := by
  apply RepresentedCauchySum.unique (basisReindexedPrefix g 4) (basisReindexedPrefix_valid g 4)
    (fun n => 6*weightFourTailRate n) basisWeightFourCauchyRate_shrinks
    _ _ (basisWeightFourLatticeSum163_valid g) weightFourLatticeSum163_valid
    (basisWeightFourLatticeSum163_close_prefix g)
  intro n
  apply (weightFourLatticeSum163_close_reindexed g n).mono
  have he := basisWeightFourError_le g n
  have hn := weightFourTailRate_nonnegative n
  grind

private theorem weightSixTailRate_nonnegative (n : Nat) : 0≤weightSixTailRate n := by
  have hp : (0:Rat)<((n+1:Nat):Rat) := by exact_mod_cast (show 0<n+1 by omega)
  exact Rat.mul_nonneg (by unfold weightSixTailConstant; decide +kernel)
    (Rat.le_of_lt (Rat.inv_pos.mpr (Rat.mul_pos hp hp)))

private theorem basisWeightSixCauchyRate_shrinks :
    ShrinksToZero (fun n => 6*weightSixTailRate n) :=
  SeriesLimitLaws.shrinks_scale _ weightSixTailRate_shrinks 6 (by decide +kernel)

def basisWeightSixLatticeSum163 (g : SL2Z) : ComplexRaw :=
  RepresentedCauchySum.value (basisReindexedPrefix g 6) (basisReindexedPrefix_valid g 6)
    (fun n => 6*weightSixTailRate n)

theorem basisWeightSixLatticeSum163_valid (g : SL2Z) : (basisWeightSixLatticeSum163 g).Valid :=
  RepresentedCauchySum.value_valid _ _ _ basisWeightSixCauchyRate_shrinks
    (basisWeightSixPrefix_cauchy g)

theorem basisWeightSixLatticeSum163_close_prefix (g : SL2Z) (n : Nat) :
    Small (ComplexRaw.sub (basisWeightSixLatticeSum163 g) (basisReindexedPrefix g 6 n))
      (6*weightSixTailRate n) :=
  RepresentedCauchySum.value_close_prefix _ _ _ (basisWeightSixPrefix_cauchy g) n

/-- The actual reindexed limit agrees exactly with the original CM lattice sum. -/
theorem basisWeightSixLatticeSum163_equiv (g : SL2Z) :
    (basisWeightSixLatticeSum163 g).Equiv weightSixLatticeSum163 := by
  apply RepresentedCauchySum.unique (basisReindexedPrefix g 6) (basisReindexedPrefix_valid g 6)
    (fun n => 6*weightSixTailRate n) basisWeightSixCauchyRate_shrinks
    _ _ (basisWeightSixLatticeSum163_valid g) weightSixLatticeSum163_valid
    (basisWeightSixLatticeSum163_close_prefix g)
  intro n
  apply (weightSixLatticeSum163_close_reindexed g n).mono
  have he := basisWeightSixError_le g n
  have hn := weightSixTailRate_nonnegative n
  grind

end ComputableAnalysis.ModularForms
