import ComputableAnalysis.SinPiIntegral

namespace ComputableAnalysis

namespace SinPiIntegral

/-! The first finite transport checkpoint for the nested-radical sine route.
At stage zero the public left sum has one degenerate cell at the left endpoint;
the chart interval still contains the same rational anchor `0`. -/

theorem dyadicNestedRadicalStieltjes_base_witness :
    QInterval.Overlaps
      (dyadicNestedRadicalLeftSum 0)
      (sinPiStieltjesIntegral.compute 0) := by
  unfold QInterval.Overlaps
  constructor
  · rw [dyadicNestedRadicalLeftSum_zero]
    change 0 <= (sinPiStieltjesIntegral.compute 0).hi
    native_decide
  · rw [dyadicNestedRadicalLeftSum_zero]
    change (sinPiStieltjesIntegral.compute 0).lo <= 0
    native_decide

theorem dyadicNestedRadicalStieltjes_stage_one_overlap :
    QInterval.Overlaps
      (dyadicNestedRadicalLeftSum 1)
      (sinPiStieltjesIntegral.compute 1) := by
  unfold QInterval.Overlaps
  native_decide

theorem dyadicNestedRadicalStieltjes_stage_two_overlap :
    QInterval.Overlaps
      (dyadicNestedRadicalLeftSum 2)
      (sinPiStieltjesIntegral.compute 2) := by
  unfold QInterval.Overlaps
  native_decide

theorem dyadicNestedRadicalStieltjes_stage_three_overlap :
    QInterval.Overlaps
      (dyadicNestedRadicalLeftSum 3)
      (sinPiStieltjesIntegral.compute 3) := by
  unfold QInterval.Overlaps
  native_decide

/-! Packaging lemma for the final search-family assembly.  The search itself
is executable; this proof-level constructor only packages the already-proved
existence of a successful finite search at every requested precision. -/

noncomputable def DyadicTangentWitnessFamily.of_search_family
    (B : IntegralIdentities.ArctanInverseBisection)
    (hsearch : forall (depth k : Nat)
      (hk : k < 2 ^ depth),
      forall precision, ∃ m u, rationalTangentWitnessBoxSearch
        (dyadicTangentBoxAt B precision depth k hk)
        (dyadicNestedRadicalTableAt precision depth k).1 m = some u) :
    DyadicTangentWitnessFamily B := by
  classical
  refine { schedule := ?_ }
  intro depth k hk
  refine {
    witness := fun precision =>
      Classical.choose (Classical.choose_spec (hsearch depth k hk precision))
    searchPrecision := fun precision =>
      Classical.choose (hsearch depth k hk precision)
    search := fun precision =>
      Classical.choose_spec (Classical.choose_spec
        (hsearch depth k hk precision)) }

end SinPiIntegral

end ComputableAnalysis
