import ComputableAnalysis.RiemannHilbert.ContourRationalCenteredGeometry

/-! Actual Cauchy kernel evaluations on a fixed rational square agree with
the displaced inner-frame quadrature. Domain evidence is constructed locally. -/
namespace ComputableAnalysis.RiemannHilbert.RectangularContour
open ComplexRaw FunctionTheory DomainFunctions
set_option autoImplicit false

theorem innerBoundary_congr_at_samples (s t : QComplex → Scalar) (R : QPos) (M : Nat)
    (hH : ∀ j k v, (j=1 ∨ j=2) → (k=1 ∨ k=3) → v<M →
      s (innerHorizontalPoint R M j k v)≈t (innerHorizontalPoint R M j k v))
    (hV : ∀ j k v, (j=1 ∨ j=3) → (k=1 ∨ k=2) → v<M →
      s (innerVerticalPoint R M j k v)≈t (innerVerticalPoint R M j k v)) :
    innerBoundary s R M≈innerBoundary t R M := by
  have hh (j k : Nat) (hj : j=1 ∨ j=2) (hk : k=1 ∨ k=3) :
      squareFrameHorizontalEdge s R M j k≈squareFrameHorizontalEdge t R M j k := by
    apply gridScalarSum_congr_bounded M
    intro v hv
    exact mul_equiv (s _).property (t _).property (ofQComplex_valid _) (ofQComplex_valid _)
      (hH j k v hj hk hv) (equiv_refl _ (ofQComplex_valid _))
  have hv (j k : Nat) (hj : j=1 ∨ j=3) (hk : k=1 ∨ k=2) :
      squareFrameVerticalEdge s R M j k≈squareFrameVerticalEdge t R M j k := by
    apply gridScalarSum_congr_bounded M
    intro v hv
    exact mul_equiv (s _).property (t _).property (ofQComplex_valid _) (ofQComplex_valid _)
      (hV j k v hj hk hv) (equiv_refl _ (ofQComplex_valid _))
  refine Setoid.trans (innerBoundary_paired_edges s R M)
    (Setoid.trans ?_ (Setoid.symm (innerBoundary_paired_edges t R M)))
  exact add_equiv
    (FunctionTheory.sub_congr (add_equiv (hh 1 1 (Or.inl rfl) (Or.inl rfl)) (hh 2 1 (Or.inr rfl) (Or.inl rfl)))
      (add_equiv (hh 1 3 (Or.inl rfl) (Or.inr rfl)) (hh 2 3 (Or.inr rfl) (Or.inr rfl))))
    (FunctionTheory.sub_congr (add_equiv (hv 3 1 (Or.inr rfl) (Or.inl rfl)) (hv 3 2 (Or.inr rfl) (Or.inr rfl)))
      (add_equiv (hv 1 1 (Or.inl rfl) (Or.inl rfl)) (hv 1 2 (Or.inl rfl) (Or.inr rfl))))

theorem rationalCenteredRectangle_inner_horizontal_mem (c : QComplex) (R : QPos) (M j k v : Nat)
    (hM : 0<M) (hj : j=1 ∨ j=2) (hk : k=1 ∨ k=3) (hv : v<M) :
    rationalRectangleBoundaryContains (rationalCenteredRectangle c R.val)
      (QComplex.add c (innerHorizontalPoint R M j k v)) := by
  let J := rationalCenteredRectangle c R.val
  have ho := rationalCenteredRectangle_ordered c R
  have hn : 0<2*M := by omega
  unfold innerHorizontalPoint
  rcases hj with hj|hj <;> subst j <;> rcases hk with hk|hk <;> subst k
  · rw [←rationalCenteredRectangle_horizontal_point c R M 0 0 v hM]
    simp only [Nat.zero_mul,Nat.zero_add,Nat.mul_zero]
    rw [rectangleGridHorizontalPoint_bottom]
    exact Or.inl ⟨(intervalGridTag_mem_interval J.1 (2*M) v ho.1 hn (by omega)).1,
      (intervalGridTag_mem_interval J.1 (2*M) v ho.1 hn (by omega)).2,Rat.le_refl,Rat.le_refl⟩
  · rw [←rationalCenteredRectangle_horizontal_point c R M 0 1 v hM]
    simp only [Nat.zero_mul,Nat.zero_add,Nat.mul_one]
    rw [rectangleGridHorizontalPoint_top _ _ _ hn]
    exact Or.inr (Or.inl ⟨(intervalGridTag_mem_interval J.1 (2*M) v ho.1 hn (by omega)).1,
      (intervalGridTag_mem_interval J.1 (2*M) v ho.1 hn (by omega)).2,Rat.le_refl,Rat.le_refl⟩)
  · rw [←rationalCenteredRectangle_horizontal_point c R M 1 0 v hM]
    simp only [Nat.one_mul,Nat.mul_zero]
    rw [rectangleGridHorizontalPoint_bottom]
    exact Or.inl ⟨(intervalGridTag_mem_interval J.1 (2*M) (M+v) ho.1 hn (by omega)).1,
      (intervalGridTag_mem_interval J.1 (2*M) (M+v) ho.1 hn (by omega)).2,Rat.le_refl,Rat.le_refl⟩
  · rw [←rationalCenteredRectangle_horizontal_point c R M 1 1 v hM]
    simp only [Nat.one_mul,Nat.mul_one]
    rw [rectangleGridHorizontalPoint_top _ _ _ hn]
    exact Or.inr (Or.inl ⟨(intervalGridTag_mem_interval J.1 (2*M) (M+v) ho.1 hn (by omega)).1,
      (intervalGridTag_mem_interval J.1 (2*M) (M+v) ho.1 hn (by omega)).2,Rat.le_refl,Rat.le_refl⟩)

theorem rationalCenteredRectangle_inner_vertical_mem (c : QComplex) (R : QPos) (M j k v : Nat)
    (hM : 0<M) (hj : j=1 ∨ j=3) (hk : k=1 ∨ k=2) (hv : v<M) :
    rationalRectangleBoundaryContains (rationalCenteredRectangle c R.val)
      (QComplex.add c (innerVerticalPoint R M j k v)) := by
  let J := rationalCenteredRectangle c R.val
  have ho := rationalCenteredRectangle_ordered c R
  have hn : 0<2*M := by omega
  unfold innerVerticalPoint
  rcases hj with hj|hj <;> subst j <;> rcases hk with hk|hk <;> subst k
  · rw [←rationalCenteredRectangle_vertical_point c R M 0 0 v hM]
    simp only [Nat.zero_mul,Nat.zero_add,Nat.mul_zero]
    rw [rectangleGridVerticalPoint_left]
    exact Or.inr (Or.inr (Or.inl ⟨Rat.le_refl,Rat.le_refl,
      (intervalGridTag_mem_interval J.2 (2*M) v ho.2 hn (by omega)).1,
      (intervalGridTag_mem_interval J.2 (2*M) v ho.2 hn (by omega)).2⟩))
  · rw [←rationalCenteredRectangle_vertical_point c R M 1 0 v hM]
    simp only [Nat.one_mul,Nat.mul_zero]
    rw [rectangleGridVerticalPoint_left]
    exact Or.inr (Or.inr (Or.inl ⟨Rat.le_refl,Rat.le_refl,
      (intervalGridTag_mem_interval J.2 (2*M) (M+v) ho.2 hn (by omega)).1,
      (intervalGridTag_mem_interval J.2 (2*M) (M+v) ho.2 hn (by omega)).2⟩))
  · rw [←rationalCenteredRectangle_vertical_point c R M 0 1 v hM]
    simp only [Nat.zero_mul,Nat.zero_add,Nat.mul_one]
    rw [rectangleGridVerticalPoint_right _ _ _ hn]
    exact Or.inr (Or.inr (Or.inr ⟨Rat.le_refl,Rat.le_refl,
      (intervalGridTag_mem_interval J.2 (2*M) v ho.2 hn (by omega)).1,
      (intervalGridTag_mem_interval J.2 (2*M) v ho.2 hn (by omega)).2⟩))
  · rw [←rationalCenteredRectangle_vertical_point c R M 1 1 v hM]
    simp only [Nat.one_mul,Nat.mul_one]
    rw [rectangleGridVerticalPoint_right _ _ _ hn]
    exact Or.inr (Or.inr (Or.inr ⟨Rat.le_refl,Rat.le_refl,
      (intervalGridTag_mem_interval J.2 (2*M) (M+v) ho.2 hn (by omega)).1,
      (intervalGridTag_mem_interval J.2 (2*M) (M+v) ho.2 hn (by omega)).2⟩))

theorem rationalCenteredRectangle_kernel_sample (f : DomainFunctions.Map) (b : Scalar) (c : QComplex)
    (R : QPos) (hd : RectangleBoundaryDomains (ribbonCauchyKernel f b) (rationalCenteredRectangle c R.val))
    (hdom : ∀ z, frameDomain R z → f.domain (Centered.translate (rationalRectangleScalar c) z))
    (hc : Small (Centered.offset (rationalRectangleScalar c) b).val (R.val/64)) (q : QComplex)
    (hq : frameDomain R (rationalRectangleScalar q))
    (hboundary : rationalRectangleBoundaryContains (rationalCenteredRectangle c R.val) (QComplex.add c q)) :
    rectangleBoundarySample (ribbonCauchyKernel f b) (rationalCenteredRectangle c R.val) hd (QComplex.add c q)≈
      displacedFrameSample f b (rationalRectangleScalar c) R hdom hc q := by
  let K := ribbonCauchyKernel f b
  let z := rationalRectangleScalar q
  let v := (kernelTranslation (rationalRectangleScalar c)).eval z trivial
  have hv := displacedFrame_domain f b (rationalRectangleScalar c) R hdom hc z hq
  have he : v≈rationalRectangleScalar (QComplex.add c q) :=
    Setoid.trans (kernelTranslation_agreement _ z) (rationalRectangleScalar_translate c q)
  have ha : K.domain (rationalRectangleScalar (QComplex.add c q)) :=
    (K.domain_congr v _ he).mp (compose_outer_mem hv)
  refine Setoid.trans (rectangleBoundarySample_value K _ hd _ hboundary ha) ?_
  refine Setoid.trans (K.eval_congr _ _ _ (compose_outer_mem hv) (Setoid.symm he)) ?_
  exact Setoid.symm (frameSample_on_frame (displacedFrameFunction f b (rationalRectangleScalar c)) R
    (displacedFrame_domain f b (rationalRectangleScalar c) R hdom hc) q hq)

theorem rationalCenteredRectangle_cauchy_boundary (f : DomainFunctions.Map) (b : Scalar) (c : QComplex)
    (R : QPos) (hd : RectangleBoundaryDomains (ribbonCauchyKernel f b) (rationalCenteredRectangle c R.val))
    (hdom : ∀ z, frameDomain R z → f.domain (Centered.translate (rationalRectangleScalar c) z))
    (hc : Small (Centered.offset (rationalRectangleScalar c) b).val (R.val/64)) (n : Nat) :
    continuousRectangleBoundary (ribbonCauchyKernel f b) (rationalCenteredRectangle c R.val) hd (n+1)≈
      displacedInnerPrefix f b (rationalRectangleScalar c) R hdom hc (2^n) := by
  let s := rectangleBoundarySample (ribbonCauchyKernel f b) (rationalCenteredRectangle c R.val) hd
  have ho := rationalCenteredRectangle_ordered c R
  have he := rectangleBoundarySample_edges (ribbonCauchyKernel f b) _ ho.1 ho.2 hd (n+1)
  have hp : 2^(n+1)=2*(2^n) := by rw [Nat.pow_succ]; omega
  rw [hp] at he
  refine Setoid.trans (Setoid.symm he) ?_
  refine Setoid.trans (rationalCenteredRectangle_boundary s c R (2^n) (Nat.two_pow_pos n)) ?_
  apply innerBoundary_congr_at_samples
  · intro j k v hj hk hv
    exact rationalCenteredRectangle_kernel_sample f b c R hd hdom hc _
      (innerHorizontalPoint_mem R (2^n) j k v (Nat.two_pow_pos n) hj hk hv)
      (rationalCenteredRectangle_inner_horizontal_mem c R (2^n) j k v (Nat.two_pow_pos n) hj hk hv)
  · intro j k v hj hk hv
    exact rationalCenteredRectangle_kernel_sample f b c R hd hdom hc _
      (innerVerticalPoint_mem R (2^n) j k v (Nat.two_pow_pos n) hj hk hv)
      (rationalCenteredRectangle_inner_vertical_mem c R (2^n) j k v (Nat.two_pow_pos n) hj hk hv)

end ComputableAnalysis.RiemannHilbert.RectangularContour
