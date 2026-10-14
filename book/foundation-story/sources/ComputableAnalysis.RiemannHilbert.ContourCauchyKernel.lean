import ComputableAnalysis.RiemannHilbert.ContourFrameDeformation
import ComputableAnalysis.RiemannHilbert.ReciprocalHolomorphic
import ComputableAnalysis.RiemannHilbert.DomainHolomorphicIntersectionSum
import ComputableAnalysis.RiemannHilbert.DomainAffineFunction

/-! The actual centered Cauchy integrand, at arbitrary represented centers.
The pole is excluded by whole-frame coordinate separation. -/
namespace ComputableAnalysis.RiemannHilbert.RectangularContour
open ComplexRaw FunctionTheory DomainFunctions
set_option autoImplicit false

def kernelTranslation (a : Scalar) : DomainFunctions.Map := DomainFunctions.affine a oneScalar

theorem kernelTranslation_agreement (a z : Scalar) :
    (kernelTranslation a).eval z trivial ≈ Centered.translate a z := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := ((kernelTranslation a).eval z trivial).property)
    (hright := (Centered.translate a z).property)
  let A := ComplexRawQuotient.ofRaw a.val a.property
  let Z := ComplexRawQuotient.ofRaw z.val z.property
  change A+1*Z=A+Z
  grind only

def kernelNumerator (f : DomainFunctions.Map) (a : Scalar) : DomainFunctions.Map :=
  compose f (kernelTranslation a)

def kernelRestrictedNumerator (f : DomainFunctions.Map) (a : Scalar) : DomainFunctions.Map :=
  onDomain (kernelNumerator f a)
    (intersectionSum (kernelNumerator f a) ReciprocalHolomorphic.function).domain_congr
    (fun _ hz => hz.1)

def cauchyKernel (f : DomainFunctions.Map) (a : Scalar) : DomainFunctions.Map :=
  productOn (kernelRestrictedNumerator f a) ReciprocalHolomorphic.function (fun _ hz => hz.2)

def cauchyKernel_holomorphic (f : DomainFunctions.Map) (hf : Holomorphic f) (a : Scalar) :
    Holomorphic (cauchyKernel f a) := by
  let hn := hf.compose (DomainFunctions.affine_holomorphic a oneScalar)
  let ho := intersectionOpenData hn ReciprocalHolomorphic.holomorphic
  let hr := hn.onDomain ho (fun _ hz => hz.1)
  exact hr.productOn ReciprocalHolomorphic.holomorphic (fun _ hz => hz.2)

theorem cauchyKernel_value (f : DomainFunctions.Map) (a z : Scalar)
    (hz : (cauchyKernel f a).domain z)
    (hd : f.domain (Centered.translate a z)) :
    (cauchyKernel f a).eval z hz ≈
      scalarProduct (f.eval (Centered.translate a z) hd) (RepresentedReciprocal.inverse z hz.2) :=
  mul_equiv (f.eval _ hz.1.2).property (f.eval _ hd).property
    (RepresentedReciprocal.inverse z hz.2).property (RepresentedReciprocal.inverse z hz.2).property
    (f.eval_congr _ _ hz.1.2 hd (kernelTranslation_agreement a z))
    (equiv_refl _ (RepresentedReciprocal.inverse z hz.2).property)

theorem cauchyKernel_center_congr (f : DomainFunctions.Map) (a b z : Scalar)
    (ha : (cauchyKernel f a).domain z) (hb : (cauchyKernel f b).domain z) (he : a ≈ b) :
    (cauchyKernel f a).eval z ha ≈ (cauchyKernel f b).eval z hb := by
  have ht : (kernelTranslation a).eval z trivial ≈ (kernelTranslation b).eval z trivial :=
    add_equiv he (equiv_refl _ (mul_valid oneScalar.property z.property))
  exact mul_equiv (f.eval _ ha.1.2).property (f.eval _ hb.1.2).property
    (RepresentedReciprocal.inverse z ha.2).property (RepresentedReciprocal.inverse z hb.2).property
    (f.eval_congr _ _ ha.1.2 hb.1.2 ht)
    (equiv_refl _ (RepresentedReciprocal.inverse z ha.2).property)

theorem frameDomain_nonzero (R : QPos) (z : Scalar) (hz : frameDomain R z) :
    NonzeroBoxSearch.Nonzero z := by
  obtain ⟨j,k,hi,hz⟩ := hz
  exact representedRectangle_nonzero _ R (squareFrameTile_separated R j k hi) z hz

theorem frameDomain_bound (R : QPos) (z : Scalar) (hz : frameDomain R z) :
    Small z.val (2*R.val) := by
  obtain ⟨j,k,hi,hz⟩ := hz
  have index_bounds (u : Nat) (hu : u<4) :
      -2*R.val≤(squareFrameInterval R u).lo ∧
        (squareFrameInterval R u).hi≤2*R.val := by
    have hu0 : 0≤(u:Rat) := Rat.natCast_nonneg
    have hu4 : (u:Rat)≤3 := by exact_mod_cast (show u≤3 by omega)
    have hl := Rat.mul_nonneg hu0 (Rat.le_of_lt R.property)
    have hh := Rat.mul_le_mul_of_nonneg_right hu4 (Rat.le_of_lt R.property)
    simp only [squareFrameInterval,Rat.natCast_add]
    change -2*R.val≤ -2*R.val+(u:Rat)*R.val ∧
      -2*R.val+((u:Rat)+1)*R.val≤2*R.val
    constructor <;> grind only
  have hx := index_bounds j hi.1
  have hy := index_bounds k hi.2.1
  have hxl : -(2*R.val)≤(squareFrameInterval R j).lo := by grind only
  have hyl : -(2*R.val)≤(squareFrameInterval R k).lo := by grind only
  refine ⟨?_,?_,?_,?_⟩ <;> intro n m
  · exact Rat.le_trans hxl (hz.1 0 m)
  · exact Rat.le_trans (hz.2.1 n 0) hx.2
  · exact Rat.le_trans hyl (hz.2.2.1 0 m)
  · exact Rat.le_trans (hz.2.2.2 n 0) hy.2

def cauchyKernel_frame_domain (f : DomainFunctions.Map) (a : Scalar) (R : QPos)
    (hdom : ∀ z, frameDomain R z → f.domain (Centered.translate a z)) :
    ∀ z, frameDomain R z → (cauchyKernel f a).domain z :=
  fun z hz => ⟨⟨trivial,(f.domain_congr _ _ (kernelTranslation_agreement a z)).mpr (hdom z hz)⟩,
    frameDomain_nonzero R z hz⟩

theorem cauchyKernel_frame_difference_zero (f : DomainFunctions.Map) (hf : Holomorphic f)
    (a : Scalar) (R : QPos) (hdom : ∀ z, frameDomain R z → f.domain (Centered.translate a z))
    (eps : QPos) : ∃ N, ∀ n, N≤n →
      Small (frameContourDifference (cauchyKernel f a) R (cauchyKernel_frame_domain f a R hdom) n).val eps.val :=
  frameContourDifference_zero _ (cauchyKernel_holomorphic f hf a) R (cauchyKernel_frame_domain f a R hdom) eps

theorem cauchyKernel_frame_limits_agree (f : DomainFunctions.Map) (hf : Holomorphic f)
    (a : Scalar) (R : QPos) (hdom : ∀ z, frameDomain R z → f.domain (Centered.translate a z))
    (u v : Scalar)
    (hu : Converges (frameOuterBoundary (cauchyKernel f a) R (cauchyKernel_frame_domain f a R hdom)) u)
    (hv : Converges (frameInnerBoundary (cauchyKernel f a) R (cauchyKernel_frame_domain f a R hdom)) v) :
    u ≈ v :=
  frame_boundary_limits_agree _ (cauchyKernel_holomorphic f hf a) R
    (cauchyKernel_frame_domain f a R hdom) u v hu hv

end ComputableAnalysis.RiemannHilbert.RectangularContour
