import ComputableAnalysis.ModularForms.DyadicSampleBlockAgreement

/-! The original flat sums agree with the Cauchy dyadic contour averages. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert PDE.CauchyContour

theorem pairedSquareHalfEdgeSum_dyadic_agreement (a : Scalar) (edge : HalfEdge)
    (R : Rat) (n : Nat) :
    (pairedSquareDyadicAverage a edge R n).val.Equiv
      (pairedSquareHalfEdgeSum a edge R (2^n)) := by
  cases he : edge.upper
  · let f := pairedSquareDensitySample a edge R
    have hr := dyadicSampleAverage_reversal f (⟨0,1⟩ : QInterval) n
    have hi : reverseInterval (⟨0,1⟩ : QInterval)=⟨0,1⟩ := by decide +kernel
    rw [hi] at hr
    have hb := dyadicSampleAverage_block (fun u => f (1-u)) n
    have ht := equiv_trans (pairedSquareDyadicAverage a edge R n).property
      (dyadicSampleAverage (fun u => f (1-u)) ⟨0,1⟩ n).property
      (scaleRat_valid (ScalarSeries.block_valid _ (fun j => (f _).property) 0 (2^n)))
      (equiv_symm hr) hb
    simpa only [pairedSquareHalfEdgeSum,he,Bool.false_eq_true,if_false,
      f,pairedSquareDensitySample] using ht
  · have hb := dyadicSampleAverage_block (pairedSquareDensitySample a edge R) n
    simpa only [pairedSquareHalfEdgeSum,he,if_true,pairedSquareDyadicAverage,
      pairedSquareDensitySample] using hb

theorem pairedSquareEdgeListSum_dyadic_agreement (a : Scalar) (R : Rat)
    (n : Nat) (edges : List HalfEdge) :
    (pairedSquareDyadicEdgeList a R n edges).val.Equiv
      (pairedSquareEdgeListSum a R (2^n) edges) := by
  induction edges with
  | nil => exact equiv_refl _ (ofQComplex_valid _)
  | cons edge edges ih =>
    exact add_equiv
      (pairedSquareHalfEdgeSum_dyadic_agreement a edge R n) ih

theorem pairedSquareContourSum_dyadic_agreement (a : Scalar) (R : Rat) (n : Nat) :
    (pairedSquareDyadicContour a R n).val.Equiv (pairedSquareContourSum a R (2^n)) :=
  pairedSquareEdgeListSum_dyadic_agreement a R n square

theorem pairedSquareContourLimit_flat_dyadic_convergence (a : Scalar) (R : Rat)
    (hR : 0<R) (eps : QPos) :
    ∃ N, ∀ n, N≤n →
      Small (sub (pairedSquareContourLimit a R hR) (pairedSquareContourSum a R (2^n))) eps.val := by
  obtain ⟨N,hN⟩ := pairedSquareContourLimit_convergence a R hR eps
  refine ⟨N, ?_⟩
  intro n hn
  exact Small.congr
    (sub_valid (pairedSquareContourLimit_valid a R hR) (pairedSquareDyadicContour a R n).property)
    (sub_valid (pairedSquareContourLimit_valid a R hR) (pairedSquareContourSum_valid a R (2^n)))
    (FunctionTheory.sub_congr (equiv_refl _ (pairedSquareContourLimit_valid a R hR))
      (pairedSquareContourSum_dyadic_agreement a R n)) (hN n hn)

end ComputableAnalysis.ModularForms
