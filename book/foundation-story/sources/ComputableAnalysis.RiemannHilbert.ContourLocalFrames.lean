import ComputableAnalysis.RiemannHilbert.ContourInnerKernelError

/-! Actual local frames at arbitrary represented centers. Their rational
radii and the continuity-error stages are explicit computations. -/
namespace ComputableAnalysis.RiemannHilbert.RectangularContour
open ComplexRaw FunctionTheory DomainFunctions
set_option autoImplicit false

def contourBaseRadius (f : DomainFunctions.Map) (hf : Holomorphic f) (a : Scalar) (ha : f.domain a) : QPos :=
  divideRadius (hf.openDomain.radius a ha) ⟨4,by decide +kernel⟩

def shrinkingContourRadius (f : DomainFunctions.Map) (hf : Holomorphic f)
    (a : Scalar) (ha : f.domain a) (n : Nat) : QPos :=
  ⟨(contourBaseRadius f hf a ha).val*((1:Rat)/2)^n,
    Rat.mul_pos (contourBaseRadius f hf a ha).property (Rat.pow_pos (by decide +kernel))⟩

theorem half_power_le_one (n : Nat) : ((1:Rat)/2)^n≤1 := by
  induction n with
  | zero => decide +kernel
  | succ n ih =>
    rw [Rat.pow_succ]
    have h := Rat.mul_le_mul_of_nonneg_right ih (by decide +kernel : (0:Rat)≤1/2)
    grind only

theorem shrinkingContourRadius_inside (f : DomainFunctions.Map) (hf : Holomorphic f)
    (a : Scalar) (ha : f.domain a) (n : Nat) :
    2*(shrinkingContourRadius f hf a ha n).val≤(hf.openDomain.radius a ha).val := by
  have h := Rat.mul_le_mul_of_nonneg_left (half_power_le_one n)
    (Rat.le_of_lt (contourBaseRadius f hf a ha).property)
  have he := divideRadius_identity (hf.openDomain.radius a ha) (⟨4,by decide +kernel⟩ : QPos)
  change 4*(contourBaseRadius f hf a ha).val=(hf.openDomain.radius a ha).val at he
  have hp := (contourBaseRadius f hf a ha).property
  change 2*((contourBaseRadius f hf a ha).val*((1:Rat)/2)^n)≤_
  grind only

def contourErrorStage (f : DomainFunctions.Map) (hf : Holomorphic f)
    (a : Scalar) (ha : f.domain a) (delta : QPos) : Nat :=
  RationalMajorant.natRateStage (2*(contourBaseRadius f hf a ha).val) delta

theorem contourErrorStage_spec (f : DomainFunctions.Map) (hf : Holomorphic f)
    (a : Scalar) (ha : f.domain a) (delta : QPos) (n : Nat)
    (hn : contourErrorStage f hf a ha delta≤n) :
    2*(shrinkingContourRadius f hf a ha n).val≤delta.val := by
  have hC : 0≤2*(contourBaseRadius f hf a ha).val :=
    Rat.mul_nonneg (by decide +kernel) (Rat.le_of_lt (contourBaseRadius f hf a ha).property)
  have hp := Rat.mul_le_mul_of_nonneg_left (RationalMajorant.half_pow_le_one_div_succ n) hC
  have hr := RationalMajorant.natRateStage_spec_of_le hC delta hn
  have he : (2*(contourBaseRadius f hf a ha).val)*(1/((n+1:Nat):Rat))=
      (2*(contourBaseRadius f hf a ha).val)/((n+1:Nat):Rat) := by
    simp only [Rat.div_def,Rat.one_mul]
  rw [he] at hp
  change 2*((contourBaseRadius f hf a ha).val*((1:Rat)/2)^n)≤delta.val
  have hb := Rat.le_trans hp hr
  grind only

theorem shrinkingFrame_domain (f : DomainFunctions.Map) (hf : Holomorphic f)
    (a : Scalar) (ha : f.domain a) (n : Nat) :
    ∀ z, frameDomain (shrinkingContourRadius f hf a ha n) z → f.domain (Centered.translate a z) := by
  intro z hz
  have hs := Small.congr z.property (Centered.offset a (Centered.translate a z)).property
    (equiv_symm (Centered.offset_translate a z))
    (frameDomain_bound (shrinkingContourRadius f hf a ha n) z hz)
  exact hf.openDomain.inside a ha _ (hs.mono (shrinkingContourRadius_inside f hf a ha n))

theorem shrinkingFrame_numerator_close (f : DomainFunctions.Map) (hf : Holomorphic f)
    (a : Scalar) (ha : f.domain a) (eps : QPos) (n : Nat)
    (hn : contourErrorStage f hf a ha (hf.continuous.delta a ha eps)≤n) :
    ∀ z hz, Small (sub (f.eval (Centered.translate a z) (shrinkingFrame_domain f hf a ha n z hz)).val
      (f.eval a ha).val) eps.val := by
  intro z hz
  have hs := Small.congr z.property (Centered.offset a (Centered.translate a z)).property
    (equiv_symm (Centered.offset_translate a z))
    (frameDomain_bound (shrinkingContourRadius f hf a ha n) z hz)
  exact hf.continuous.estimate a ha eps _ _ (hs.mono (contourErrorStage_spec f hf a ha _ n hn))

def shrinkingCauchyPrefix (f : DomainFunctions.Map) (hf : Holomorphic f)
    (a : Scalar) (ha : f.domain a) (n M : Nat) : Scalar :=
  cauchyInnerPrefix f a (shrinkingContourRadius f hf a ha n) (shrinkingFrame_domain f hf a ha n) M

def shrinkingReciprocalPrefix (f : DomainFunctions.Map) (hf : Holomorphic f)
    (a : Scalar) (ha : f.domain a) (n M : Nat) : Scalar :=
  reciprocalInnerPrefix (shrinkingContourRadius f hf a ha n) M

theorem shrinkingPrefix_center_estimate (f : DomainFunctions.Map) (hf : Holomorphic f)
    (a : Scalar) (ha : f.domain a) (eps : QPos) (n M : Nat) (hM : 0<M)
    (hn : contourErrorStage f hf a ha (hf.continuous.delta a ha eps)≤n) :
    Small (sub (shrinkingCauchyPrefix f hf a ha n M).val
      (mul (f.eval a ha).val (shrinkingReciprocalPrefix f hf a ha n M).val)) (64*eps.val) :=
  inner_cauchy_center_estimate f a ha _ (shrinkingFrame_domain f hf a ha n) eps
    (shrinkingFrame_numerator_close f hf a ha eps n hn) M hM

end ComputableAnalysis.RiemannHilbert.RectangularContour
