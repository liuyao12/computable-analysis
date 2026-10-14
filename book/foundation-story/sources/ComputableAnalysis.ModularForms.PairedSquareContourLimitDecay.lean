import ComputableAnalysis.ModularForms.PairedSquareContourLimit

/-! Sample bounds and large-radius decay pass to the represented candidate. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert

theorem pairedSquareContourLimit_bound (a : Scalar) (R : Rat) (hR : 0<R) :
    Small (pairedSquareContourLimit a R hR) (343669760*(1/R)) :=
  SeriesLimitLaws.small_of_prefix_bound _ (pairedSquareContourLimit_valid a R hR)
    (contourScheduledSample a R hR) (contourScheduledSample_valid a R hR) _
    (fun k => (RepresentedCauchySum.error k).val) RepresentedCauchySum.error_shrinks
    (pairedSquareContourLimit_sample_error a R hR)
    (fun k => pairedSquareDyadicContour_bound a R hR (contourDepth a R hR k))

theorem pairedSquareContourLimit_large_radius_small (a : Scalar) (eps : QPos) :
    ∃ K, ∀ n, K≤n →
      Small (pairedSquareContourLimit a ((n+1:Nat):Rat)
        (Rat.natCast_pos.mpr (Nat.succ_pos n))) eps.val := by
  obtain ⟨K,hK⟩ := pairedReciprocalTail_shrinks 343669760 eps
  refine ⟨K, ?_⟩
  intro n hn
  apply (pairedSquareContourLimit_bound a ((n+1:Nat):Rat)
    (Rat.natCast_pos.mpr (Nat.succ_pos n))).mono
  have hk := hK n hn
  have hc : ((343669760:Nat):Rat)=343669760 := by decide +kernel
  rw [hc] at hk
  simpa only [Rat.div_def,Rat.one_mul] using hk

end ComputableAnalysis.ModularForms
