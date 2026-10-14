import ComputableAnalysis.RiemannHilbert.ContourFrameSampler
import ComputableAnalysis.RiemannHilbert.ContourBoundaryAgreement
import ComputableAnalysis.RiemannHilbert.ContourLimits

/-! Actual holomorphic functions on a twelve-tile frame have equal outer
and inner boundary limits. Neither contour equality nor a Cauchy formula
is assumed in the holomorphic witness. -/
namespace ComputableAnalysis.RiemannHilbert.RectangularContour
open ComplexRaw FunctionTheory DomainFunctions
set_option autoImplicit false

def frameTile_domain (f : DomainFunctions.Map) (R : QPos)
    (hdom : ∀ z, frameDomain R z → f.domain z) (j k : Nat) (hi : squareFrameTileIndex j k) :
    ∀ z, representedRectangleContains (squareFrameTile R j k) z → f.domain z :=
  fun z hz => hdom z ⟨j,k,hi,hz⟩

theorem frameSample_tile_boundary_agreement (f : DomainFunctions.Map) (hf : Holomorphic f)
    (R : QPos) (hdom : ∀ z, frameDomain R z → f.domain z) (j k : Nat)
    (hi : squareFrameTileIndex j k) (n : Nat) :
    (rectangleGridBoundary (frameSample f R hdom) (squareFrameTile R j k) (2^n)).val.Equiv
      (holomorphicRectangleGridBoundary f hf (squareFrameTile R j k)
        (frameTile_domain f R hdom j k hi) n).val := by
  have ho := squareFrameTile_ordered R j k
  apply rectangleGridBoundary_congr _ _ _ _ ho.1 ho.2
  intro q hq
  have hd : f.domain (rationalRectangleScalar q) :=
    frameTile_domain f R hdom j k hi _ (rationalRectangle_represented_mem _ q hq)
  exact equiv_trans (frameSample f R hdom q).property
    (f.eval (rationalRectangleScalar q) hd).property
    (holomorphicRectangleSample f hf _ (frameTile_domain f R hdom j k hi) q).property
    (frameSample_agreement f R hdom j k hi q hq hd)
    (holomorphicRectangleSample_agreement f hf _ (frameTile_domain f R hdom j k hi) q hq hd)

theorem frameSample_tile_boundary_zero (f : DomainFunctions.Map) (hf : Holomorphic f)
    (R : QPos) (hdom : ∀ z, frameDomain R z → f.domain z) (j k : Nat)
    (hi : squareFrameTileIndex j k) (eps : QPos) :
    ∃ N, ∀ n, N≤n →
      Small (rectangleGridBoundary (frameSample f R hdom) (squareFrameTile R j k) (2^n)).val eps.val := by
  have ho := squareFrameTile_ordered R j k
  obtain ⟨N,hN⟩ := holomorphicRectangleGridBoundary_converges_zero f hf _
    (frameTile_domain f R hdom j k hi) ho.1 ho.2 eps
  exact ⟨N,fun n hn => Small.congr
    (holomorphicRectangleGridBoundary f hf _ (frameTile_domain f R hdom j k hi) n).property
    (rectangleGridBoundary (frameSample f R hdom) (squareFrameTile R j k) (2^n)).property
    (equiv_symm (frameSample_tile_boundary_agreement f hf R hdom j k hi n)) (hN n hn)⟩

theorem frameSample_uniform_boundary_depth (f : DomainFunctions.Map) (hf : Holomorphic f)
    (R : QPos) (hdom : ∀ z, frameDomain R z → f.domain z) (eps : QPos) :
    ∃ N, ∀ n, N≤n → ∀ j k, squareFrameTileIndex j k →
      Small (rectangleGridBoundary (frameSample f R hdom) (squareFrameTile R j k) (2^n)).val eps.val := by
  have h : ∀ j, j<4 → ∃ N, ∀ n, N≤n → ∀ k, k<4 → squareFrameTileIndex j k →
      Small (rectangleGridBoundary (frameSample f R hdom) (squareFrameTile R j k) (2^n)).val eps.val := by
    intro j hj
    apply finite_eventual_depth
    intro k hk
    by_cases hi : squareFrameTileIndex j k
    · obtain ⟨N,hN⟩ := frameSample_tile_boundary_zero f hf R hdom j k hi eps
      exact ⟨N,fun n hn _ => hN n hn⟩
    · exact ⟨0,by intro n hn hh; exact False.elim (hi hh)⟩
  obtain ⟨N,hN⟩ := finite_eventual_depth _ 4 h
  exact ⟨N,fun n hn j k hi => hN n hn j hi.1 k hi.2.1 hi⟩

def frameOuterBoundary (f : DomainFunctions.Map) (R : QPos)
    (hdom : ∀ z, frameDomain R z → f.domain z) (n : Nat) : Scalar :=
  frameScalarRectBoundary (squareFrameHorizontalEdge (frameSample f R hdom) R (2^n))
    (squareFrameVerticalEdge (frameSample f R hdom) R (2^n)) 0 0 4 4

def frameInnerBoundary (f : DomainFunctions.Map) (R : QPos)
    (hdom : ∀ z, frameDomain R z → f.domain z) (n : Nat) : Scalar :=
  frameScalarRectBoundary (squareFrameHorizontalEdge (frameSample f R hdom) R (2^n))
    (squareFrameVerticalEdge (frameSample f R hdom) R (2^n)) 1 1 2 2

def frameContourDifference (f : DomainFunctions.Map) (R : QPos)
    (hdom : ∀ z, frameDomain R z → f.domain z) (n : Nat) : Scalar :=
  gridScalarSub (frameOuterBoundary f R hdom n) (frameInnerBoundary f R hdom n)

theorem frameContourDifference_zero (f : DomainFunctions.Map) (hf : Holomorphic f)
    (R : QPos) (hdom : ∀ z, frameDomain R z → f.domain z) (eps : QPos) :
    ∃ N, ∀ n, N≤n → Small (frameContourDifference f R hdom n).val eps.val := by
  let eta : QPos := ⟨eps.val/12,by
    rw [Rat.div_def]; exact Rat.mul_pos eps.property (by decide +kernel)⟩
  obtain ⟨N,hN⟩ := frameSample_uniform_boundary_depth f hf R hdom eta
  refine ⟨N, ?_⟩
  intro n hn
  let tile := fun j k => rectangleGridBoundary (frameSample f R hdom) (squareFrameTile R j k) (2^n)
  have hb := frameScalarSum_bound tile 1 2 1 1 2 1 eta.val (Rat.le_of_lt eta.property) (by
    intro j k ht
    have hi : squareFrameTileIndex j k := by
      unfold representedFrameCell at ht
      unfold squareFrameTileIndex
      omega
    exact hN n hn j k hi)
  have he : ((representedFrameCellCount 1 2 1 1 2 1:Nat):Rat)*eta.val=eps.val := by
    change 12*(eps.val/12)=eps.val
    grind only
  rw [he] at hb
  exact Small.congr (frameScalarSum tile 1 2 1 1 2 1).property
    (frameContourDifference f R hdom n).property
    (squareFrame_tiled_boundary_agreement (frameSample f R hdom) R (2^n)
      (Nat.pow_pos (by omega))) hb

theorem frameContourDifference_converges_zero (f : DomainFunctions.Map) (hf : Holomorphic f)
    (R : QPos) (hdom : ∀ z, frameDomain R z → f.domain z) :
    Converges (frameContourDifference f R hdom) ⟨zero,ofQComplex_valid _⟩ :=
  converge_zero _ (frameContourDifference_zero f hf R hdom)

theorem frame_boundary_limits_agree (f : DomainFunctions.Map) (hf : Holomorphic f)
    (R : QPos) (hdom : ∀ z, frameDomain R z → f.domain z) (a b : Scalar)
    (ha : Converges (frameOuterBoundary f R hdom) a)
    (hb : Converges (frameInnerBoundary f R hdom) b) : a ≈ b := by
  apply SeriesLimitLaws.equiv_of_small_sub_zero
  apply small_zero_of_all_errors
  intro eps
  let eta : QPos := ⟨eps.val/3,by
    rw [Rat.div_def]; exact Rat.mul_pos eps.property (by decide +kernel)⟩
  obtain ⟨A,hA⟩ := ha eta
  obtain ⟨B,hB⟩ := hb eta
  obtain ⟨C,hC⟩ := frameContourDifference_zero f hf R hdom eta
  let n := max (max A B) C
  let p := frameOuterBoundary f R hdom n
  let q := frameInnerBoundary f R hdom n
  have hs := LocalODE.small_add
    (LocalODE.small_add
      (RepresentedCauchySum.small_sub_symm _ _ _ (hA n (by dsimp [n]; omega)))
      (hC n (by dsimp [n]; omega))) (hB n (by dsimp [n]; omega))
  have he : (eta.val+eta.val)+eta.val=eps.val := by dsimp [eta]; grind only
  rw [he] at hs
  exact Small.congr
    (add_valid (add_valid (sub_valid a.property p.property) (sub_valid p.property q.property))
      (sub_valid q.property b.property)) (sub_valid a.property b.property)
    (equiv_symm (SeriesLimitLaws.difference_via a.val b.val p.val q.val
      a.property b.property p.property q.property)) hs

end ComputableAnalysis.RiemannHilbert.RectangularContour
