import ComputableAnalysis.RiemannHilbert.ContourOuterAgreement
import ComputableAnalysis.RiemannHilbert.ContourNormalizedCauchy

/-! One executable sampler for the actual Cauchy kernel on every nested
frame. Only rational coordinate bounds and pole tests select evaluations. -/
namespace ComputableAnalysis.RiemannHilbert.RectangularContour
open ComplexRaw FunctionTheory DomainFunctions BoxApproximation
set_option autoImplicit false

def fixedSquareSampleGood (f : DomainFunctions.Map) (hf : Holomorphic f)
    (a : Scalar) (ha : f.domain a) (q : QComplex) : Prop :=
  coordinateBound q≤2*(contourBaseRadius f hf a ha).val ∧ QComplex.normSq q≠0

instance fixedSquareSampleGood_decidable (f : DomainFunctions.Map) (hf : Holomorphic f)
    (a : Scalar) (ha : f.domain a) (q : QComplex) : Decidable (fixedSquareSampleGood f hf a ha q) :=
  inferInstanceAs (Decidable (coordinateBound q≤2*(contourBaseRadius f hf a ha).val ∧ QComplex.normSq q≠0))

theorem fixedSquareSample_numerator_domain (f : DomainFunctions.Map) (hf : Holomorphic f)
    (a : Scalar) (ha : f.domain a) (q : QComplex) (hq : fixedSquareSampleGood f hf a ha q) :
    f.domain (Centered.translate a (rationalRectangleScalar q)) := by
  have hb := (rational_small q).mono hq.1
  have hs := Small.congr (ofQComplex_valid _)
    (Centered.offset a (Centered.translate a (rationalRectangleScalar q))).property
    (equiv_symm (Centered.offset_translate a (rationalRectangleScalar q))) hb
  have hr : 2*(contourBaseRadius f hf a ha).val≤(hf.openDomain.radius a ha).val := by
    simpa only [shrinkingContourRadius,Rat.pow_zero,Rat.mul_one] using shrinkingContourRadius_inside f hf a ha 0
  exact hf.openDomain.inside a ha _ (hs.mono hr)

theorem fixedSquareSample_kernel_domain (f : DomainFunctions.Map) (hf : Holomorphic f)
    (a : Scalar) (ha : f.domain a) (q : QComplex) (hq : fixedSquareSampleGood f hf a ha q) :
    (cauchyKernel f a).domain (rationalRectangleScalar q) := by
  have hp := RationalReciprocal.raw_mul_constants q (RationalReciprocal.inverse q)
  rw [RationalReciprocal.mul_inverse q hq.2] at hp
  have hz := RepresentedReciprocal.nonzero_of_inverse (rationalRectangleScalar q)
    (rationalRectangleScalar (RationalReciprocal.inverse q)) hp
  have hn := fixedSquareSample_numerator_domain f hf a ha q hq
  exact ⟨⟨trivial,(f.domain_congr _ _ (kernelTranslation_agreement a _)).mpr hn⟩,hz⟩

def fixedSquareSample (f : DomainFunctions.Map) (hf : Holomorphic f)
    (a : Scalar) (ha : f.domain a) (q : QComplex) : Scalar :=
  if hq : fixedSquareSampleGood f hf a ha q then
    (cauchyKernel f a).eval (rationalRectangleScalar q) (fixedSquareSample_kernel_domain f hf a ha q hq)
  else rationalRectangleScalar QComplex.zero

theorem fixedSquareSample_value (f : DomainFunctions.Map) (hf : Holomorphic f)
    (a : Scalar) (ha : f.domain a) (q : QComplex) (hq : fixedSquareSampleGood f hf a ha q)
    (hd : (cauchyKernel f a).domain (rationalRectangleScalar q)) :
    fixedSquareSample f hf a ha q ≈ (cauchyKernel f a).eval (rationalRectangleScalar q) hd := by
  rw [fixedSquareSample,dif_pos hq]
  exact equiv_refl _ ((cauchyKernel f a).eval _ hd).property

theorem shrinkingContourRadius_le_base (f : DomainFunctions.Map) (hf : Holomorphic f)
    (a : Scalar) (ha : f.domain a) (m : Nat) :
    (shrinkingContourRadius f hf a ha m).val≤(contourBaseRadius f hf a ha).val := by
  have hb := Rat.mul_le_mul_of_nonneg_left (half_power_le_one m)
    (Rat.le_of_lt (contourBaseRadius f hf a ha).property)
  simpa only [shrinkingContourRadius,Rat.mul_one] using hb

theorem fixedSquareSample_frame_good (f : DomainFunctions.Map) (hf : Holomorphic f)
    (a : Scalar) (ha : f.domain a) (m : Nat) (q : QComplex)
    (hq : frameDomain (shrinkingContourRadius f hf a ha m) (rationalRectangleScalar q)) :
    fixedSquareSampleGood f hf a ha q := by
  have hr := shrinkingContourRadius_le_base f hf a ha m
  have hc := rational_coordinate_bound q _ (frameDomain_bound _ _ hq)
  have hn := frame_rational_norm_lower _ q hq
  have hp := Rat.mul_pos (shrinkingContourRadius f hf a ha m).property
    (shrinkingContourRadius f hf a ha m).property
  constructor
  · have h := Rat.mul_le_mul_of_nonneg_left hr (show (0:Rat)≤2 by decide +kernel)
    exact Rat.le_trans hc h
  · exact Rat.ne_of_gt (by grind only)

theorem fixedSquareSample_frame_agreement (f : DomainFunctions.Map) (hf : Holomorphic f)
    (a : Scalar) (ha : f.domain a) (m : Nat) (q : QComplex)
    (hq : frameDomain (shrinkingContourRadius f hf a ha m) (rationalRectangleScalar q)) :
    fixedSquareSample f hf a ha q ≈
      cauchyFrameSample f a (shrinkingContourRadius f hf a ha m) (shrinkingFrame_domain f hf a ha m) q := by
  have hv := fixedSquareSample_value f hf a ha q (fixedSquareSample_frame_good f hf a ha m q hq)
    (cauchyKernel_frame_domain f a _ (shrinkingFrame_domain f hf a ha m) _ hq)
  exact Setoid.trans hv (Setoid.symm (frameSample_on_frame _ _
    (cauchyKernel_frame_domain f a _ (shrinkingFrame_domain f hf a ha m)) q hq))

def nestedSquareInner (f : DomainFunctions.Map) (hf : Holomorphic f)
    (a : Scalar) (ha : f.domain a) (m n : Nat) : Scalar :=
  innerBoundary (fixedSquareSample f hf a ha) (shrinkingContourRadius f hf a ha m) (2^n)

def nestedSquareOuter (f : DomainFunctions.Map) (hf : Holomorphic f)
    (a : Scalar) (ha : f.domain a) (m n : Nat) : Scalar :=
  outerBoundary (fixedSquareSample f hf a ha) (shrinkingContourRadius f hf a ha m) (2^n)

theorem nestedSquareInner_actual (f : DomainFunctions.Map) (hf : Holomorphic f)
    (a : Scalar) (ha : f.domain a) (m n : Nat) :
    nestedSquareInner f hf a ha m n ≈ shrinkingCauchyPrefix f hf a ha m (2^n) :=
  innerBoundary_congr_on_frame _ _ _ _ (Nat.two_pow_pos n) (fixedSquareSample_frame_agreement f hf a ha m)

theorem nestedSquareOuter_actual (f : DomainFunctions.Map) (hf : Holomorphic f)
    (a : Scalar) (ha : f.domain a) (m n : Nat) :
    nestedSquareOuter f hf a ha m n ≈
      frameOuterBoundary (cauchyKernel f a) (shrinkingContourRadius f hf a ha m)
        (cauchyKernel_frame_domain f a _ (shrinkingFrame_domain f hf a ha m)) n :=
  outerBoundary_congr_on_frame _ _ _ _ (Nat.two_pow_pos n) (fixedSquareSample_frame_agreement f hf a ha m)

end ComputableAnalysis.RiemannHilbert.RectangularContour
