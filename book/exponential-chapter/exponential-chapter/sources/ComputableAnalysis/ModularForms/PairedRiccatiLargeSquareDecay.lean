import ComputableAnalysis.ModularForms.PairedRiccatiSquareSumInvariance

/-! Actual finite contour sums vanish uniformly as square radii grow. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

theorem pairedSquareContourSum_successor_radius_bound (a : Scalar) (n N : Nat) (hN : 0<N) :
    Small (pairedSquareContourSum a ((n+1:Nat):Rat) N)
      (343669760*(((n+1:Nat):Rat))⁻¹) := by
  have hs := pairedSquareContourSum_bound a ((n+1:Nat):Rat)
    (Rat.natCast_pos.mpr (by omega)) N hN
  simpa only [Rat.div_def,Rat.one_mul] using hs

theorem pairedSquareContourSum_large_radius_small (a : Scalar) (eps : QPos) :
    ∃ K : Nat, ∀ n : Nat, K≤n → ∀ N : Nat, 0<N →
      Small (pairedSquareContourSum a ((n+1:Nat):Rat) N) eps.val := by
  obtain ⟨K,hK⟩ := pairedReciprocalTail_shrinks 343669760 eps
  exact ⟨K,fun n hn N hN =>
    (pairedSquareContourSum_successor_radius_bound a n N hN).mono (hK n hn)⟩

end ComputableAnalysis.ModularForms
