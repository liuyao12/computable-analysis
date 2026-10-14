import ComputableAnalysis.RiemannHilbert.ContourHolomorphicSamples
import ComputableAnalysis.RiemannHilbert.ContourDyadicCells

/-! Uniform cell estimates without an assumed uniform mesh or Cauchy formula. Adapted from the corresponding finite rectangle proofs in
`ComputableAnalysis.ModularForms`, with only the generic dependencies retained. -/
namespace ComputableAnalysis.RiemannHilbert.RectangularContour
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions
set_option autoImplicit false

theorem holomorphicRectangle_uniform_midpoint_cycle_bound (f : DomainFunctions.Map) (hf : Holomorphic f) (J : QInterval × QInterval)
    (hdom : ∀ z : Scalar, representedRectangleContains J z → f.domain z)
    (eps : QPos) (hX : J.1.lo≤J.1.hi) (hY : J.2.lo≤J.2.hi) :
    ∃ N, ∀ choice : Nat → Bool × Bool, ∀ n, N≤n → ∀ H : QPos,
      (rectangleBisection J choice n).1.width≤2*H.val →
      (rectangleBisection J choice n).2.width≤2*H.val →
      Small (fullRectangleMidpointCycle (holomorphicRectangleSample f hf J hdom)
        (rectangleBisection J choice n)).val (64*eps.val*H.val*H.val) := by
  obtain ⟨N,hN⟩ := domainRectangleNeighborhood_uniform_depth
    (f) (hf)
    eps J hX hY (domain_rectangle_neighborhood_cover f hf eps J hX hY hdom)
  refine ⟨N, ?_⟩
  intro choice n hn H hx hy
  obtain ⟨c,hc,hnear⟩ := hN choice n hn
  let K := rectangleBisection J choice n
  have hKX : K.1.lo≤K.1.hi := by
    dsimp [K]
    rw [rectangleBisection_coordinates]
    exact bisectionInterval_ordered J.1 hX (fun k => (choice k).1) n
  have hKY : K.2.lo≤K.2.hi := by
    dsimp [K]
    rw [rectangleBisection_coordinates]
    exact bisectionInterval_ordered J.2 hY (fun k => (choice k).2) n
  have hm := (rectangleMidpoints_mem K hKX hKY).1
  have near (q : QComplex) (hq : rationalRectangleContains K q) :
      Small (Centered.offset c (rationalRectangleScalar q)).val
        ((hf).continuousDerivative.delta c hc eps).val :=
    (hnear q hq).mono (minRadius_right _ _)
  have mem (q : QComplex) (hq : rationalRectangleContains K q) : rationalRectangleContains J q :=
    rectangleBisection_contains_initial J hX hY choice n q hq
  have hb := rectangleSampleModel_full_cycle_bound (holomorphicRectangleSample f hf J hdom) K
    ((hf).derivative c hc) (4*eps.val*H.val) H
    (Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) (Rat.le_of_lt eps.property))
      (Rat.le_of_lt H.property)) hKX hKY hx hy
    (fun q hq hd => holomorphicRectangleSample_model_error f hf J hdom c hc
      (rectangleCenter K) q (mem _ hm) (mem _ hq) H eps hd (near _ hm) (near _ hq))
  have he : 16*(4*eps.val*H.val)*H.val=64*eps.val*H.val*H.val := by grind only
  rw [he] at hb
  exact hb

theorem holomorphicRectangle_uniform_dyadic_midpoint_error (f : DomainFunctions.Map) (hf : Holomorphic f) (J : QInterval × QInterval)
    (hdom : ∀ z : Scalar, representedRectangleContains J z → f.domain z)
    (eps W : QPos) (hX : J.1.lo≤J.1.hi) (hY : J.2.lo≤J.2.hi)
    (hx : J.1.width≤2*W.val) (hy : J.2.width≤2*W.val) :
    ∃ N, ∀ choice : Nat → Bool × Bool, ∀ n, N≤n →
      Small (fullRectangleMidpointCycle (holomorphicRectangleSample f hf J hdom) (rectangleBisection J choice n)).val
        (64*eps.val*(W.val*((1:Rat)/2)^n)*(W.val*((1:Rat)/2)^n)) := by
  obtain ⟨N,hN⟩ := holomorphicRectangle_uniform_midpoint_cycle_bound f hf J hdom eps hX hY
  refine ⟨N, ?_⟩
  intro choice n hn
  let H : QPos := ⟨W.val*((1:Rat)/2)^n,
    Rat.mul_pos W.property (Rat.pow_pos (by decide +kernel))⟩
  have hp : 0≤((1:Rat)/2)^n := Rat.pow_nonneg (by decide +kernel)
  have bounds : (rectangleBisection J choice n).1.width≤2*H.val ∧
      (rectangleBisection J choice n).2.width≤2*H.val := by
    rw [rectangleBisection_coordinates]
    change (bisectionInterval J.1 (fun k => (choice k).1) n).width≤2*H.val ∧
      (bisectionInterval J.2 (fun k => (choice k).2) n).width≤2*H.val
    rw [bisectionInterval_width,bisectionInterval_width]
    have hxx := Rat.mul_le_mul_of_nonneg_right hx hp
    have hyy := Rat.mul_le_mul_of_nonneg_right hy hp
    change J.1.width*((1:Rat)/2)^n≤2*(W.val*((1:Rat)/2)^n) ∧
      J.2.width*((1:Rat)/2)^n≤2*(W.val*((1:Rat)/2)^n)
    constructor <;> grind only
  exact hN choice n hn H bounds.1 bounds.2

theorem holomorphicRectangle_indexed_dyadic_cell_bound (f : DomainFunctions.Map) (hf : Holomorphic f) (J : QInterval × QInterval)
    (hdom : ∀ z : Scalar, representedRectangleContains J z → f.domain z)
    (eps W : QPos) (hX : J.1.lo≤J.1.hi) (hY : J.2.lo≤J.2.hi)
    (hx : J.1.width≤2*W.val) (hy : J.2.width≤2*W.val) :
    ∃ N, ∀ n, N≤n → ∀ j l : Nat, j<2^n → l<2^n →
      Small (fullRectangleMidpointCycle (holomorphicRectangleSample f hf J hdom) (rectangleGridCell J (2^n) j l)).val
        (64*eps.val*(W.val*((1:Rat)/2)^n)*(W.val*((1:Rat)/2)^n)) := by
  obtain ⟨N,hN⟩ := holomorphicRectangle_uniform_dyadic_midpoint_error f hf J hdom eps W hX hY hx hy
  refine ⟨N, ?_⟩
  intro n hn j l hj hk
  obtain ⟨choice,hc⟩ := rectangleGridCell_bisection J n j l hj hk
  have hb := hN choice n hn
  rw [hc] at hb
  exact hb

end ComputableAnalysis.RiemannHilbert.RectangularContour
