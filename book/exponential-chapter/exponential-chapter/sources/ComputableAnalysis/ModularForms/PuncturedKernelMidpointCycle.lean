import ComputableAnalysis.ModularForms.PuncturedKernelSampleLinearization
import ComputableAnalysis.ModularForms.MidpointAffineErrorBound
import ComputableAnalysis.ModularForms.DyadicCellIndexing

/-! Actual punctured-kernel midpoint cycles from proved sample linearization. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

theorem rectangleSampleModel_full_cycle_bound (f : QComplex → Scalar)
    (J : QInterval × QInterval) (d : Scalar) (E : Rat) (H : QPos) (hE : 0≤E)
    (hX : J.1.lo≤J.1.hi) (hY : J.2.lo≤J.2.hi)
    (hx : J.1.width≤2*H.val) (hy : J.2.width≤2*H.val)
    (hlocal : ∀ q : QComplex, rationalRectangleContains J q →
      Small (Centered.offset (rationalRectangleScalar (rectangleCenter J)) (rationalRectangleScalar q)).val H.val →
      Small (sub (f q).val (affineMidpointModel (f (rectangleCenter J)) d
        (Centered.offset (rationalRectangleScalar (rectangleCenter J)) (rationalRectangleScalar q))).val) E) :
    Small (fullRectangleMidpointCycle f J).val (16*E*H.val) := by
  have hm := rectangleMidpoints_mem J hX hY
  have he := rectangleMidpoints_translations J
  have hv := rectangleHalfVectors_small J H hX hY hx hy
  let C := rationalRectangleScalar (rectangleCenter J)
  have model (q : QComplex) (w : Scalar) (hq : rationalRectangleContains J q)
      (htrans : Centered.translate C w=rationalRectangleScalar q) (hw : Small w.val H.val) :
      Small (sub (f q).val (affineMidpointModel (f (rectangleCenter J)) d w).val) E := by
    have hoff : (Centered.offset C (rationalRectangleScalar q)).val.Equiv w.val := by
      rw [←htrans]
      exact Centered.offset_translate C w
    have hnear := Small.congr w.property (Centered.offset C (rationalRectangleScalar q)).property (equiv_symm hoff) hw
    have hb := hlocal q hq hnear
    have hmodel := add_equiv (equiv_refl _ (f (rectangleCenter J)).property)
      (mul_equiv d.property d.property (Centered.offset C (rationalRectangleScalar q)).property w.property
        (equiv_refl _ d.property) hoff)
    exact Small.congr
      (sub_valid (f q).property (affineMidpointModel (f (rectangleCenter J)) d (Centered.offset C (rationalRectangleScalar q))).property)
      (sub_valid (f q).property (affineMidpointModel (f (rectangleCenter J)) d w).property)
      (FunctionTheory.sub_congr (equiv_refl _ (f q).property) hmodel) hb
  have hb := midpointAffineError_cycle_bound
    (f (rectangleRight J)) (f (rectangleLeft J)) (f (rectangleTop J)) (f (rectangleBottom J))
    (f (rectangleCenter J)) d (rationalRectangleScalar (rectangleHalfX J))
    (rationalRectangleScalar (rectangleHalfY J)) E H.val hE (Rat.le_of_lt H.property)
    (model _ _ hm.2.1 he.1 hv.1)
    (model _ _ hm.2.2.1 he.2.1 (SeriesLimitLaws.small_neg hv.1))
    (model _ _ hm.2.2.2.1 he.2.2.1 hv.2)
    (model _ _ hm.2.2.2.2 he.2.2.2 (SeriesLimitLaws.small_neg hv.2)) hv.1 hv.2
  have hs := LocalODE.small_scale (by decide +kernel : (0:Rat)≤2) hb
  have hc : 2*(8*E*H.val)=16*E*H.val := by grind only
  rw [hc] at hs
  exact hs

theorem puncturedKernel_uniform_midpoint_cycle_bound (c : Scalar)
    (J : QInterval × QInterval) (R eps : QPos) (hs : rectangleSeparated J R)
    (hX : J.1.lo≤J.1.hi) (hY : J.2.lo≤J.2.hi) :
    ∃ N, ∀ choice : Nat → Bool × Bool, ∀ n, N≤n → ∀ H : QPos,
      (rectangleBisection J choice n).1.width≤2*H.val →
      (rectangleBisection J choice n).2.width≤2*H.val →
      Small (fullRectangleMidpointCycle (rationalRiccatiKernelSample c)
        (rectangleBisection J choice n)).val (64*eps.val*H.val*H.val) := by
  obtain ⟨N,hN⟩ := puncturedKernel_uniform_sample_linearization c J R eps hs hX hY
  refine ⟨N, ?_⟩
  intro choice n hn H hx hy
  obtain ⟨a,ha,hmodel⟩ := hN choice n hn
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
  have hb := rectangleSampleModel_full_cycle_bound (rationalRiccatiKernelSample c) K
    ((pairedRiccatiCauchyIntegrandMap_holomorphic c).derivative a ha) (4*eps.val*H.val) H
    (Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) (Rat.le_of_lt eps.property)) (Rat.le_of_lt H.property))
    hKX hKY hx hy (fun q hq hd => hmodel (rectangleCenter K) q H hm hq hd)
  have he : 16*(4*eps.val*H.val)*H.val=64*eps.val*H.val*H.val := by grind only
  rw [he] at hb
  exact hb

theorem puncturedKernel_uniform_dyadic_midpoint_error (c : Scalar) (R : QPos) (eps W : QPos)
    (J : QInterval × QInterval) (hs : rectangleSeparated J R) (hX : J.1.lo≤J.1.hi) (hY : J.2.lo≤J.2.hi)
    (hx : J.1.width≤2*W.val) (hy : J.2.width≤2*W.val) :
    ∃ N, ∀ choice : Nat → Bool × Bool, ∀ n, N≤n →
      Small (fullRectangleMidpointCycle (rationalRiccatiKernelSample c) (rectangleBisection J choice n)).val
        (64*eps.val*(W.val*((1:Rat)/2)^n)*(W.val*((1:Rat)/2)^n)) := by
  obtain ⟨N,hN⟩ := puncturedKernel_uniform_midpoint_cycle_bound c J R eps hs hX hY
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

theorem puncturedKernel_indexed_dyadic_cell_bound (c : Scalar) (R : QPos) (eps W : QPos)
    (J : QInterval × QInterval) (hs : rectangleSeparated J R) (hX : J.1.lo≤J.1.hi) (hY : J.2.lo≤J.2.hi)
    (hx : J.1.width≤2*W.val) (hy : J.2.width≤2*W.val) :
    ∃ N, ∀ n, N≤n → ∀ j k : Nat, j<2^n → k<2^n →
      Small (fullRectangleMidpointCycle (rationalRiccatiKernelSample c) (rectangleGridCell J (2^n) j k)).val
        (64*eps.val*(W.val*((1:Rat)/2)^n)*(W.val*((1:Rat)/2)^n)) := by
  obtain ⟨N,hN⟩ := puncturedKernel_uniform_dyadic_midpoint_error c R eps W J hs hX hY hx hy
  refine ⟨N, ?_⟩
  intro n hn j k hj hk
  obtain ⟨choice,hc⟩ := rectangleGridCell_bisection J n j k hj hk
  have hb := hN choice n hn
  rw [hc] at hb
  exact hb

end ComputableAnalysis.ModularForms
