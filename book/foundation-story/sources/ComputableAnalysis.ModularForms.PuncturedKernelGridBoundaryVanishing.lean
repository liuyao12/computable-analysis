import ComputableAnalysis.ModularForms.PuncturedKernelMidpointCycle
import ComputableAnalysis.ModularForms.PairedRiccatiGridBoundaryVanishing

/-! Literal weighted boundary sums for the actual kernel vanish on separated rectangles. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

def puncturedKernelGridBoundary (c : Scalar) (J : QInterval × QInterval) (n : Nat) : Scalar :=
  rectangleGridBoundary (rationalRiccatiKernelSample c) J (2^n)

theorem puncturedKernelGridBoundary_eventual_bound (c : Scalar) (R : QPos) (eps W : QPos)
    (J : QInterval × QInterval) (hs : rectangleSeparated J R) (hX : J.1.lo≤J.1.hi) (hY : J.2.lo≤J.2.hi)
    (hx : J.1.width≤2*W.val) (hy : J.2.width≤2*W.val) :
    ∃ N, ∀ n, N≤n → Small (puncturedKernelGridBoundary c J n).val (64*eps.val*W.val*W.val) := by
  obtain ⟨N,hN⟩ := puncturedKernel_indexed_dyadic_cell_bound c R eps W J hs hX hY hx hy
  refine ⟨N, ?_⟩
  intro n hn
  let E := 64*eps.val*(W.val*((1:Rat)/2)^n)*(W.val*((1:Rat)/2)^n)
  have hw : 0≤W.val*((1:Rat)/2)^n :=
    Rat.mul_nonneg (Rat.le_of_lt W.property) (Rat.pow_nonneg (by decide +kernel))
  have hE : 0≤E := Rat.mul_nonneg
    (Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) (Rat.le_of_lt eps.property)) hw) hw
  have hb := gridScalarDoubleSum_bound (2^n) (2^n)
    (fun j k => fullRectangleMidpointCycle (rationalRiccatiKernelSample c) (rectangleGridCell J (2^n) j k)) E hE
    (fun j k hj hk => hN n hn j k hj hk)
  have hp := two_pow_half_pow n
  have he : ((2^n:Nat):Rat)*(((2^n:Nat):Rat)*E)=64*eps.val*W.val*W.val := by
    dsimp [E]
    grind only
  rw [he] at hb
  exact Small.congr (rectangleGridCycleSum (rationalRiccatiKernelSample c) J (2^n)).property (puncturedKernelGridBoundary c J n).property
    (rectangleGridCycleSum_boundary_agreement
      (rationalRiccatiKernelSample c) J (2^n)) hb

theorem puncturedKernelGridBoundary_converges_zero (c : Scalar) (R : QPos) (J : QInterval × QInterval)
    (hs : rectangleSeparated J R)
    (hX : J.1.lo≤J.1.hi) (hY : J.2.lo≤J.2.hi) (eps : QPos) :
    ∃ N, ∀ n, N≤n → Small (puncturedKernelGridBoundary c J n).val eps.val := by
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
  obtain ⟨N,hN⟩ := puncturedKernelGridBoundary_eventual_bound c R eta W J hs hX hY hx hy
  refine ⟨N, ?_⟩
  intro n hn
  have hb := hN n hn
  have he : eta.val*(64*W.val*W.val)=eps.val := Rat.div_mul_cancel (Rat.ne_of_gt hD)
  have he' : 64*eta.val*W.val*W.val=eps.val := by grind only
  rw [he'] at hb
  exact hb

end ComputableAnalysis.ModularForms
