import ComputableAnalysis.ModularForms.DomainRectangleNeighborhoodCover
import ComputableAnalysis.ModularForms.PairedRiccatiKernelProductContinuity

/-! Analytic endpoint errors transferred to the literal rational kernel samples. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

def rationalRiccatiKernelSample (c : Scalar) (q : QComplex) : Scalar :=
  scalarProduct (pairedEntireRiccatiMap.eval (Centered.translate c (rationalRectangleScalar q)) trivial)
    (rationalSquaredKernel q)

theorem puncturedKernel_eval_sample_agreement (c : Scalar) (q : QComplex)
    (hz : (pairedRiccatiCauchyIntegrandMap c).domain (rationalRectangleScalar q)) :
    ((pairedRiccatiCauchyIntegrandMap c).eval (rationalRectangleScalar q) hz).val.Equiv
      (rationalRiccatiKernelSample c q).val := by
  have hq : QComplex.normSq q≠0 := by
    intro he
    have heq := QComplex.normSq_eq_zero_iff.mp he
    apply hz
    rw [heq]
    exact equiv_refl zero (ofQComplex_valid _)
  exact pairedRiccatiCauchyIntegrandMap_rational_agreement c q hq hz

theorem puncturedKernel_sample_model_error (c a : Scalar) (ha : NonzeroBoxSearch.Nonzero a)
    (J : QInterval × QInterval) (R : QPos) (hs : rectangleSeparated J R)
    (p q : QComplex) (hp : rationalRectangleContains J p) (hq : rationalRectangleContains J q)
    (W eps : QPos) (hd : Small (sub (ofQComplex q) (ofQComplex p)) W.val)
    (hpa : Small (Centered.offset a (rationalRectangleScalar p)).val
      ((pairedRiccatiCauchyIntegrandMap_holomorphic c).continuousDerivative.delta a ha eps).val)
    (hqa : Small (Centered.offset a (rationalRectangleScalar q)).val
      ((pairedRiccatiCauchyIntegrandMap_holomorphic c).continuousDerivative.delta a ha eps).val) :
    Small (sub (rationalRiccatiKernelSample c q).val
      (affineMidpointModel (rationalRiccatiKernelSample c p)
        ((pairedRiccatiCauchyIntegrandMap_holomorphic c).derivative a ha)
        (Centered.offset (rationalRectangleScalar p) (rationalRectangleScalar q))).val)
      (4*eps.val*W.val) := by
  let f := pairedRiccatiCauchyIntegrandMap c
  let d := (pairedRiccatiCauchyIntegrandMap_holomorphic c).derivative a ha
  let P := rationalRectangleScalar p
  let Q := rationalRectangleScalar q
  have hP : f.domain P := punctureSafeRectangle_kernel_domain c J R hs P (rationalRectangle_represented_mem J p hp)
  have hQ : f.domain Q := punctureSafeRectangle_kernel_domain c J R hs Q (rationalRectangle_represented_mem J q hq)
  have hr := puncturedRiccati_rectangle_segment_linearization c a ha J R hs p q hp hq W eps hd hpa hqa
  have hb := Small.congr (remainder_valid f P hP d Q hQ)
    (sub_valid (f.eval Q hQ).property (affineMidpointModel (f.eval P hP) d (Centered.offset P Q)).property)
    (equiv_symm (localAffineModel_error_equiv f P d Q hP hQ)) hr
  have hmodel := add_equiv (puncturedKernel_eval_sample_agreement c p hP)
    (equiv_refl _ (scalarProduct d (Centered.offset P Q)).property)
  exact Small.congr
    (sub_valid (f.eval Q hQ).property (affineMidpointModel (f.eval P hP) d (Centered.offset P Q)).property)
    (sub_valid (rationalRiccatiKernelSample c q).property
      (affineMidpointModel (rationalRiccatiKernelSample c p) d (Centered.offset P Q)).property)
    (FunctionTheory.sub_congr (puncturedKernel_eval_sample_agreement c q hQ) hmodel) hb

theorem puncturedKernel_uniform_sample_linearization (c : Scalar)
    (J : QInterval × QInterval) (R eps : QPos) (hs : rectangleSeparated J R)
    (hX : J.1.lo≤J.1.hi) (hY : J.2.lo≤J.2.hi) :
    ∃ N, ∀ choice : Nat → Bool × Bool, ∀ n, N≤n →
      ∃ a : Scalar, ∃ ha : NonzeroBoxSearch.Nonzero a,
        ∀ p q : QComplex, ∀ W : QPos,
          rationalRectangleContains (rectangleBisection J choice n) p →
          rationalRectangleContains (rectangleBisection J choice n) q →
          Small (sub (ofQComplex q) (ofQComplex p)) W.val →
          Small (sub (rationalRiccatiKernelSample c q).val
            (affineMidpointModel (rationalRiccatiKernelSample c p)
              ((pairedRiccatiCauchyIntegrandMap_holomorphic c).derivative a ha)
              (Centered.offset (rationalRectangleScalar p) (rationalRectangleScalar q))).val)
            (4*eps.val*W.val) := by
  obtain ⟨N,hN⟩ := puncturedRiccati_uniform_derivative_neighborhoods c J R eps hs hX hY
  refine ⟨N, ?_⟩
  intro choice n hn
  obtain ⟨a,ha,hnear⟩ := hN choice n hn
  refine ⟨a,ha, ?_⟩
  intro p q W hp hq hd
  exact puncturedKernel_sample_model_error c a ha J R hs p q
    (rectangleBisection_contains_initial J hX hY choice n p hp)
    (rectangleBisection_contains_initial J hX hY choice n q hq) W eps hd
    (hnear p hp).2 (hnear q hq).2

end ComputableAnalysis.ModularForms
