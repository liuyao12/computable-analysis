import ComputableAnalysis.ModularForms.RationalRectangleMidpoints

/-! Actual rational rectangle midpoint cycles obey uniform quadratic errors. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

def pairedRiccatiRectangleCycle (J : QInterval × QInterval) : Scalar :=
  midpointWeightedCycle
    (pairedEntireRiccatiMap.eval (rationalRectangleScalar (rectangleRight J)) trivial)
    (pairedEntireRiccatiMap.eval (rationalRectangleScalar (rectangleLeft J)) trivial)
    (pairedEntireRiccatiMap.eval (rationalRectangleScalar (rectangleTop J)) trivial)
    (pairedEntireRiccatiMap.eval (rationalRectangleScalar (rectangleBottom J)) trivial)
    (rationalRectangleScalar (rectangleHalfX J)) (rationalRectangleScalar (rectangleHalfY J))

theorem pairedRiccatiRectangleCycle_neighborhood_bound (J : QInterval × QInterval)
    (a : Scalar) (eps H : QPos) (hX : J.1.lo≤J.1.hi) (hY : J.2.lo≤J.2.hi)
    (hx : J.1.width≤2*H.val) (hy : J.2.width≤2*H.val)
    (hnear : ∀ q : QComplex, rationalRectangleContains J q →
      Small (sub (ofQComplex q) a.val)
        (pairedEntireRiccatiMap_holomorphic.continuousDerivative.delta a trivial eps).val) :
    Small (pairedRiccatiRectangleCycle J).val (32*eps.val*H.val*H.val) := by
  have hm := rectangleMidpoints_mem J hX hY
  have he := rectangleMidpoints_translations J
  have hs := rectangleHalfVectors_small J H hX hY hx hy
  have hb := pairedRiccati_rectangle_neighborhood_bound a
    (rationalRectangleScalar (rectangleCenter J))
    (rationalRectangleScalar (rectangleHalfX J))
    (rationalRectangleScalar (rectangleHalfY J)) eps H
    (hnear _ hm.1)
    (by rw [he.1]; exact hnear _ hm.2.1)
    (by rw [he.2.1]; exact hnear _ hm.2.2.1)
    (by rw [he.2.2.1]; exact hnear _ hm.2.2.2.1)
    (by rw [he.2.2.2]; exact hnear _ hm.2.2.2.2) hs.1 hs.2
  rw [he.1,he.2.1,he.2.2.1,he.2.2.2] at hb
  have hc : 8*(4*eps.val*H.val)*H.val=32*eps.val*H.val*H.val := by grind only
  rw [hc] at hb
  exact hb

theorem pairedRiccati_uniform_midpoint_cycle_bound (eps : QPos)
    (J : QInterval × QInterval) (hX : J.1.lo≤J.1.hi) (hY : J.2.lo≤J.2.hi) :
    ∃ N, ∀ choice : Nat → Bool × Bool, ∀ n, N≤n → ∀ H : QPos,
      (rectangleBisection J choice n).1.width≤2*H.val →
      (rectangleBisection J choice n).2.width≤2*H.val →
      Small (pairedRiccatiRectangleCycle (rectangleBisection J choice n)).val
        (32*eps.val*H.val*H.val) := by
  obtain ⟨N,hN⟩ := pairedRiccati_uniform_derivative_neighborhoods eps J hX hY
  refine ⟨N, ?_⟩
  intro choice n hn H hx hy
  obtain ⟨a,ha⟩ := hN choice n hn
  have hoX : (rectangleBisection J choice n).1.lo≤(rectangleBisection J choice n).1.hi := by
    rw [rectangleBisection_coordinates]
    exact bisectionInterval_ordered J.1 hX (fun k => (choice k).1) n
  have hoY : (rectangleBisection J choice n).2.lo≤(rectangleBisection J choice n).2.hi := by
    rw [rectangleBisection_coordinates]
    exact bisectionInterval_ordered J.2 hY (fun k => (choice k).2) n
  exact pairedRiccatiRectangleCycle_neighborhood_bound _ a eps H hoX hoY hx hy ha

theorem pairedRiccati_uniform_dyadic_midpoint_error (eps W : QPos)
    (J : QInterval × QInterval) (hX : J.1.lo≤J.1.hi) (hY : J.2.lo≤J.2.hi)
    (hx : J.1.width≤2*W.val) (hy : J.2.width≤2*W.val) :
    ∃ N, ∀ choice : Nat → Bool × Bool, ∀ n, N≤n →
      Small (pairedRiccatiRectangleCycle (rectangleBisection J choice n)).val
        (32*eps.val*(W.val*((1:Rat)/2)^n)*(W.val*((1:Rat)/2)^n)) := by
  obtain ⟨N,hN⟩ := pairedRiccati_uniform_midpoint_cycle_bound eps J hX hY
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

end ComputableAnalysis.ModularForms
