import ComputableAnalysis.ModularForms.RepresentedSequenceLimitUniqueness

/-! Representation invariance of the actual dyadic contour candidate. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert PDE.CauchyContour

theorem dyadicSampleAverage_congr (f g : Rat → Scalar)
    (he : ∀ u, (f u).val.Equiv (g u).val) (I : QInterval) (n : Nat) :
    (dyadicSampleAverage f I n).val.Equiv (dyadicSampleAverage g I n).val := by
  induction n generalizing I with
  | zero => exact he I.midpoint
  | succ n ih =>
    exact ComplexRaw.scaleRat_equiv_of_nonneg
      (by decide +kernel : (0:Rat)≤1/2)
      (add_equiv (ih (bisectInterval I false)) (ih (bisectInterval I true)))

theorem pairedSquareDyadicEdgeList_congr (a b : Scalar) (he : a.val.Equiv b.val)
    (R : Rat) (n : Nat) (edges : List HalfEdge) :
    (pairedSquareDyadicEdgeList a R n edges).val.Equiv
      (pairedSquareDyadicEdgeList b R n edges).val := by
  induction edges with
  | nil => exact equiv_refl _ (ofQComplex_valid _)
  | cons edge edges ih =>
    exact add_equiv (dyadicSampleAverage_congr
      (pairedSquareDensitySample a edge R) (pairedSquareDensitySample b edge R)
      (fun u => pairedSquareDensity_congr a b he edge u R) ⟨0,1⟩ n) ih

theorem pairedSquareContourLimit_congr (a b : Scalar) (he : a.val.Equiv b.val)
    (R : Rat) (hR : 0<R) :
    (pairedSquareContourLimit a R hR).Equiv (pairedSquareContourLimit b R hR) := by
  apply pairedSquareContourLimit_unique b R hR
    ⟨pairedSquareContourLimit a R hR,pairedSquareContourLimit_valid a R hR⟩
  intro eps
  obtain ⟨N,hN⟩ := pairedSquareContourLimit_convergence a R hR eps
  refine ⟨N, ?_⟩
  intro n hn
  have hd := pairedSquareDyadicEdgeList_congr a b he R n square
  exact Small.congr
    (sub_valid (pairedSquareContourLimit_valid a R hR) (pairedSquareDyadicContour a R n).property)
    (sub_valid (pairedSquareContourLimit_valid a R hR) (pairedSquareDyadicContour b R n).property)
    (FunctionTheory.sub_congr (equiv_refl _ (pairedSquareContourLimit_valid a R hR)) hd)
    (hN n hn)

end ComputableAnalysis.ModularForms
