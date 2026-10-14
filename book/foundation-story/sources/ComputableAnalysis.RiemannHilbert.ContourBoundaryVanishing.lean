import ComputableAnalysis.RiemannHilbert.ContourUniformCells

/-! Literal holomorphic rectangle boundary sums converge to the executable zero name. Adapted from the corresponding finite rectangle proofs in
`ComputableAnalysis.ModularForms`, with only the generic dependencies retained. -/
namespace ComputableAnalysis.RiemannHilbert.RectangularContour
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions
set_option autoImplicit false

def holomorphicRectangleGridBoundary (f : DomainFunctions.Map) (hf : Holomorphic f) (J : QInterval × QInterval)
    (hdom : ∀ z : Scalar, representedRectangleContains J z → f.domain z) (n : Nat) : Scalar :=
  rectangleGridBoundary (holomorphicRectangleSample f hf J hdom) J (2^n)

theorem holomorphicRectangleGridBoundary_eventual_bound (f : DomainFunctions.Map) (hf : Holomorphic f) (J : QInterval × QInterval)
    (hdom : ∀ z : Scalar, representedRectangleContains J z → f.domain z) (eps W : QPos) (hX : J.1.lo≤J.1.hi) (hY : J.2.lo≤J.2.hi)
    (hx : J.1.width≤2*W.val) (hy : J.2.width≤2*W.val) :
    ∃ N, ∀ n, N≤n → Small (holomorphicRectangleGridBoundary f hf J hdom n).val (64*eps.val*W.val*W.val) := by
  obtain ⟨N,hN⟩ := holomorphicRectangle_indexed_dyadic_cell_bound f hf J hdom eps W hX hY hx hy
  refine ⟨N, ?_⟩
  intro n hn
  let E := 64*eps.val*(W.val*((1:Rat)/2)^n)*(W.val*((1:Rat)/2)^n)
  have hw : 0≤W.val*((1:Rat)/2)^n :=
    Rat.mul_nonneg (Rat.le_of_lt W.property) (Rat.pow_nonneg (by decide +kernel))
  have hE : 0≤E := Rat.mul_nonneg
    (Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) (Rat.le_of_lt eps.property)) hw) hw
  have hb := gridScalarDoubleSum_bound (2^n) (2^n)
    (fun j k => fullRectangleMidpointCycle (holomorphicRectangleSample f hf J hdom) (rectangleGridCell J (2^n) j k)) E hE
    (fun j k hj hk => hN n hn j k hj hk)
  have hp := two_pow_half_pow n
  have he : ((2^n:Nat):Rat)*(((2^n:Nat):Rat)*E)=64*eps.val*W.val*W.val := by
    dsimp [E]
    grind only
  rw [he] at hb
  exact Small.congr (rectangleGridCycleSum (holomorphicRectangleSample f hf J hdom) J (2^n)).property (holomorphicRectangleGridBoundary f hf J hdom n).property
    (rectangleGridCycleSum_boundary_agreement
      (holomorphicRectangleSample f hf J hdom) J (2^n)) hb

theorem holomorphicRectangleGridBoundary_converges_zero (f : DomainFunctions.Map) (hf : Holomorphic f) (J : QInterval × QInterval)
    (hdom : ∀ z : Scalar, representedRectangleContains J z → f.domain z)
    (hX : J.1.lo≤J.1.hi) (hY : J.2.lo≤J.2.hi) (eps : QPos) :
    ∃ N, ∀ n, N≤n → Small (holomorphicRectangleGridBoundary f hf J hdom n).val eps.val := by
  let W : QPos := ⟨1+qabs J.1.width+qabs J.2.width,by
    have hx := qabs_nonneg J.1.width
    have hy := qabs_nonneg J.2.width
    grind only⟩
  have hx : J.1.width≤2*W.val := by
    have ha := self_le_qabs J.1.width
    have hb := qabs_nonneg J.1.width
    have hc := qabs_nonneg J.2.width
    change J.1.width≤2*(1+qabs J.1.width+qabs J.2.width)
    grind only
  have hy : J.2.width≤2*W.val := by
    have ha := self_le_qabs J.2.width
    have hb := qabs_nonneg J.1.width
    have hc := qabs_nonneg J.2.width
    change J.2.width≤2*(1+qabs J.1.width+qabs J.2.width)
    grind only
  have hD : 0<64*W.val*W.val :=
    Rat.mul_pos (Rat.mul_pos (by decide +kernel) W.property) W.property
  let eta : QPos := ⟨eps.val/(64*W.val*W.val),by
    rw [Rat.div_def]
    exact Rat.mul_pos eps.property (Rat.inv_pos.mpr hD)⟩
  obtain ⟨N,hN⟩ := holomorphicRectangleGridBoundary_eventual_bound f hf J hdom eta W hX hY hx hy
  refine ⟨N, ?_⟩
  intro n hn
  have hb := hN n hn
  have he : eta.val*(64*W.val*W.val)=eps.val := Rat.div_mul_cancel (Rat.ne_of_gt hD)
  have he' : 64*eta.val*W.val*W.val=eps.val := by grind only
  rw [he'] at hb
  exact hb

end ComputableAnalysis.RiemannHilbert.RectangularContour
