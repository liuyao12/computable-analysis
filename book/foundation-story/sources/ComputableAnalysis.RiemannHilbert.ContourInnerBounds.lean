import ComputableAnalysis.RiemannHilbert.ContourInnerLinearity

/-! Finite inner-boundary errors, with the edge length and number of
samples explicitly cancelled. No mesh convergence is assumed. -/
namespace ComputableAnalysis.RiemannHilbert.RectangularContour
open ComplexRaw FunctionTheory DomainFunctions
set_option autoImplicit false

theorem innerHorizontalEdge_bound (f : QComplex → Scalar) (R : QPos) (M j k : Nat)
    (hM : 0<M) (hj : j=1 ∨ j=2) (hk : k=1 ∨ k=3) (E : Rat) (hE : 0≤E)
    (hf : ∀ q, frameDomain R (rationalRectangleScalar q) → Small (f q).val E) :
    Small (squareFrameHorizontalEdge f R M j k).val ((M:Rat)*(2*E*(R.val/(M:Rat)))) := by
  have hv : 0≤R.val/(M:Rat) := by
    rw [Rat.div_def]
    exact Rat.mul_nonneg (Rat.le_of_lt R.property)
      (Rat.le_of_lt (Rat.inv_pos.mpr (Rat.natCast_pos.mpr hM)))
  apply gridScalarSum_bound M _ _ (Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) hE) hv)
  intro u hu
  exact Small.mul (f _).property (rationalRectangleScalar _).property hE hv
    (hf _ (innerHorizontalPoint_mem R M j k u hM hj hk hu))
    (frameHorizontal_velocity_bound R M j k hM)

theorem innerVerticalEdge_bound (f : QComplex → Scalar) (R : QPos) (M j k : Nat)
    (hM : 0<M) (hj : j=1 ∨ j=3) (hk : k=1 ∨ k=2) (E : Rat) (hE : 0≤E)
    (hf : ∀ q, frameDomain R (rationalRectangleScalar q) → Small (f q).val E) :
    Small (squareFrameVerticalEdge f R M j k).val ((M:Rat)*(2*E*(R.val/(M:Rat)))) := by
  have hv : 0≤R.val/(M:Rat) := by
    rw [Rat.div_def]
    exact Rat.mul_nonneg (Rat.le_of_lt R.property)
      (Rat.le_of_lt (Rat.inv_pos.mpr (Rat.natCast_pos.mpr hM)))
  apply gridScalarSum_bound M _ _ (Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) hE) hv)
  intro u hu
  exact Small.mul (f _).property (rationalRectangleScalar _).property hE hv
    (hf _ (innerVerticalPoint_mem R M j k u hM hj hk hu))
    (frameVertical_velocity_bound R M j k hM)

theorem innerBoundary_bound (f : QComplex → Scalar) (R : QPos) (M : Nat) (hM : 0<M)
    (E : Rat) (hE : 0≤E)
    (hf : ∀ q, frameDomain R (rationalRectangleScalar q) → Small (f q).val E) :
    Small (innerBoundary f R M).val (16*(M:Rat)*E*(R.val/(M:Rat))) := by
  let D := (M:Rat)*(2*E*(R.val/(M:Rat)))
  have hv : 0≤R.val/(M:Rat) := by
    rw [Rat.div_def]
    exact Rat.mul_nonneg (Rat.le_of_lt R.property)
      (Rat.le_of_lt (Rat.inv_pos.mpr (Rat.natCast_pos.mpr hM)))
  have hD : 0≤D := Rat.mul_nonneg Rat.natCast_nonneg
    (Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) hE) hv)
  have hh := gridScalarSum_bound 2
    (fun j => gridScalarSub (squareFrameHorizontalEdge f R M (1+j) 1)
      (squareFrameHorizontalEdge f R M (1+j) (1+2))) (D+D) (Rat.add_nonneg hD hD) (by
        intro j hj
        exact SeriesLimitLaws.small_sub
          (innerHorizontalEdge_bound f R M (1+j) 1 hM (by omega) (Or.inl rfl) E hE hf)
          (innerHorizontalEdge_bound f R M (1+j) 3 hM (by omega) (Or.inr rfl) E hE hf))
  have hh' := gridScalarSum_bound 2
    (fun k => gridScalarSub (squareFrameVerticalEdge f R M (1+2) (1+k))
      (squareFrameVerticalEdge f R M 1 (1+k))) (D+D) (Rat.add_nonneg hD hD) (by
        intro k hk
        exact SeriesLimitLaws.small_sub
          (innerVerticalEdge_bound f R M 3 (1+k) hM (Or.inr rfl) (by omega) E hE hf)
          (innerVerticalEdge_bound f R M 1 (1+k) hM (Or.inl rfl) (by omega) E hE hf))
  have hb := LocalODE.small_add hh hh'
  have he : (2:Rat)*(D+D)+2*(D+D)=16*(M:Rat)*E*(R.val/(M:Rat)) := by
    dsimp [D]
    grind only
  rw [show ((2:Nat):Rat)=2 by decide +kernel,he] at hb
  exact hb

theorem innerBoundary_inverse_error_bound (f : QComplex → Scalar) (R : QPos)
    (M : Nat) (hM : 0<M) (eps : QPos)
    (hf : ∀ q, frameDomain R (rationalRectangleScalar q) → Small (f q).val (4*eps.val/R.val)) :
    Small (innerBoundary f R M).val (64*eps.val) := by
  have hE : 0≤4*eps.val/R.val := by
    rw [Rat.div_def]
    exact Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) (Rat.le_of_lt eps.property))
      (Rat.le_of_lt (Rat.inv_pos.mpr R.property))
  have hb := innerBoundary_bound f R M hM _ hE hf
  have hr := Rat.mul_inv_cancel R.val (Rat.ne_of_gt R.property)
  have hm := Rat.mul_inv_cancel (M:Rat) (Rat.ne_of_gt (Rat.natCast_pos.mpr hM))
  have he : 16*(M:Rat)*(4*eps.val/R.val)*(R.val/(M:Rat))=64*eps.val := by
    simp only [Rat.div_def]
    grind only
  rw [he] at hb
  exact hb

end ComputableAnalysis.RiemannHilbert.RectangularContour
