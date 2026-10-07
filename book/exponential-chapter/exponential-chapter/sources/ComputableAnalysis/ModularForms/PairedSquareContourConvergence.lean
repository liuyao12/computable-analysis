import ComputableAnalysis.ModularForms.PairedSquareContourLimitDecay
import ComputableAnalysis.ModularForms.PairedRiccatiFiniteChainVariation

/-! All late actual dyadic contour averages converge to the constructed
interval-name candidate, beyond the classically chosen subsequence. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert

theorem pairedSquareContourLimit_all_sample_error (a : Scalar) (R : Rat)
    (hR : 0<R) (k n : Nat) (hn : contourChosenDepth a R hR k≤n) :
    Small (sub (pairedSquareContourLimit a R hR)
      (pairedSquareDyadicContour a R n).val) (2*(RepresentedCauchySum.error k).val) := by
  have hc := Classical.choose_spec
    (pairedSquareDyadicContour_cauchy a R hR (RepresentedCauchySum.error k))
  have hk := monotoneDepth_ge (contourChosenDepth a R hR) k
  have hb := LocalODE.small_add (pairedSquareContourLimit_sample_error a R hR k)
    (hc (contourDepth a R hR k) n hk hn)
  let L : Scalar := ⟨pairedSquareContourLimit a R hR,pairedSquareContourLimit_valid a R hR⟩
  let S : Scalar := ⟨contourScheduledSample a R hR k,contourScheduledSample_valid a R hR k⟩
  let M := pairedSquareDyadicContour a R n
  have hd := Small.congr
    (add_valid (sub_valid L.property S.property) (sub_valid S.property M.property))
    (sub_valid L.property M.property) (representedDifference_split L S M) hb
  have he : (RepresentedCauchySum.error k).val+(RepresentedCauchySum.error k).val=
      2*(RepresentedCauchySum.error k).val := by grind only
  rw [he] at hd
  exact hd

theorem pairedSquareContourLimit_convergence (a : Scalar) (R : Rat)
    (hR : 0<R) (eps : QPos) :
    ∃ N, ∀ n, N≤n → Small (sub (pairedSquareContourLimit a R hR)
      (pairedSquareDyadicContour a R n).val) eps.val := by
  let half : QPos := ⟨eps.val/2, by
    rw [Rat.div_def]
    exact Rat.mul_pos eps.property (by decide +kernel)⟩
  obtain ⟨K,hK⟩ := RepresentedCauchySum.error_shrinks half
  refine ⟨contourChosenDepth a R hR K, ?_⟩
  intro n hn
  apply (pairedSquareContourLimit_all_sample_error a R hR K n hn).mono
  have hb := hK K (Nat.le_refl K)
  change (RepresentedCauchySum.error K).val≤eps.val/2 at hb
  grind only

end ComputableAnalysis.ModularForms
