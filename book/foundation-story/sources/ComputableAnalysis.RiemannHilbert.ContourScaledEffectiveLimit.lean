import ComputableAnalysis.RiemannHilbert.ContourEffectiveLimit

/-! Rational rescaling prevents the represented-limit algorithm from
unnecessarily resolving large intermediate quadratures to unit absolute error.
Prefix errors and equivalence with the original construction are proved. -/
namespace ComputableAnalysis.RiemannHilbert.RectangularContour
open ComplexRaw FunctionTheory DomainFunctions RadialLogarithmChains
set_option autoImplicit false

def effectiveBoundaryScale (J : QInterval × QInterval) (B : QPos) : QPos :=
  ⟨max 0 (effectiveBoundaryConstant J B)+1,by grind⟩

def scaledEffectivePrefix (f : DomainFunctions.Map) (J : QInterval × QInterval)
    (hd : RectangleBoundaryDomains f J) (B : QPos) (n : Nat) : Scalar :=
  scale (effectiveBoundaryScale J B).val⁻¹ (continuousRectangleBoundary f J hd n)

def scaledEffectiveTail (J : QInterval × QInterval) (B : QPos) (n : Nat) : Rat :=
  (effectiveBoundaryConstant J B*(effectiveBoundaryScale J B).val⁻¹)*((1:Rat)/2)^n

theorem scaledEffectiveTail_shrinks (J : QInterval × QInterval) (B : QPos)
    (hX : J.1.lo≤J.1.hi) (hY : J.2.lo≤J.2.hi) : ShrinksToZero (scaledEffectiveTail J B) := by
  have hC := Rat.mul_nonneg (effectiveBoundaryConstant_nonneg J B hX hY)
    (Rat.le_of_lt (Rat.inv_pos.mpr (effectiveBoundaryScale J B).property))
  intro eps
  exact ⟨RationalMajorant.natRateStage _ eps,fun n hn => contour_half_rate _ hC eps n hn⟩

theorem scaledEffectivePrefix_cauchy (f : DomainFunctions.Map) (hf : Holomorphic f)
    (J : QInterval × QInterval) (hX : J.1.lo≤J.1.hi) (hY : J.2.lo≤J.2.hi)
    (hd : RectangleBoundaryDomains f J) (B : QPos)
    (hder : RectangleBoundaryDerivativeBound f hf J hd B) (k n : Nat) (hkn : k≤n) :
    Small (sub (scaledEffectivePrefix f J hd B n).val (scaledEffectivePrefix f J hd B k).val) (scaledEffectiveTail J B k) := by
  have hs := RationalDilation.displacement_bound (effectiveBoundaryScale J B).val⁻¹
    (Rat.le_of_lt (Rat.inv_pos.mpr (effectiveBoundaryScale J B).property)) _ _ _
    (continuousRectangleBoundary_effective_cauchy f hf J hX hY hd B hder k n hkn)
  have he : (effectiveBoundaryScale J B).val⁻¹*effectiveBoundaryTail J B k=scaledEffectiveTail J B k := by
    dsimp [effectiveBoundaryTail,scaledEffectiveTail]; grind only
  rw [he] at hs
  exact hs

def scaledEffectiveBoundaryValue (f : DomainFunctions.Map) (hf : Holomorphic f)
    (J : QInterval × QInterval) (hX : J.1.lo≤J.1.hi) (hY : J.2.lo≤J.2.hi)
    (hd : RectangleBoundaryDomains f J) (B : QPos)
    (hder : RectangleBoundaryDerivativeBound f hf J hd B) : Scalar :=
  scale (effectiveBoundaryScale J B).val
    ⟨RepresentedCauchySum.value (fun n => (scaledEffectivePrefix f J hd B n).val)
      (fun n => (scaledEffectivePrefix f J hd B n).property) (scaledEffectiveTail J B),
      RepresentedCauchySum.value_valid _ _ _ (scaledEffectiveTail_shrinks J B hX hY)
        (scaledEffectivePrefix_cauchy f hf J hX hY hd B hder)⟩

theorem scaledEffectiveBoundaryValue_prefix_error (f : DomainFunctions.Map) (hf : Holomorphic f)
    (J : QInterval × QInterval) (hX : J.1.lo≤J.1.hi) (hY : J.2.lo≤J.2.hi)
    (hd : RectangleBoundaryDomains f J) (B : QPos)
    (hder : RectangleBoundaryDerivativeBound f hf J hd B) (n : Nat) :
    Small (sub (continuousRectangleBoundary f J hd n).val
      (scaledEffectiveBoundaryValue f hf J hX hY hd B hder).val) (effectiveBoundaryTail J B n) := by
  let w : Scalar := ⟨RepresentedCauchySum.value (fun n => (scaledEffectivePrefix f J hd B n).val)
    (fun n => (scaledEffectivePrefix f J hd B n).property) (scaledEffectiveTail J B),
    RepresentedCauchySum.value_valid _ _ _ (scaledEffectiveTail_shrinks J B hX hY)
      (scaledEffectivePrefix_cauchy f hf J hX hY hd B hder)⟩
  have h := RepresentedCauchySum.value_close_prefix (fun n => (scaledEffectivePrefix f J hd B n).val)
    (fun n => (scaledEffectivePrefix f J hd B n).property) _ (scaledEffectivePrefix_cauchy f hf J hX hY hd B hder) n
  have hs := RationalDilation.displacement_bound (effectiveBoundaryScale J B).val
    (Rat.le_of_lt (effectiveBoundaryScale J B).property) w (scaledEffectivePrefix f J hd B n) _ h
  have hi := Rat.mul_inv_cancel (effectiveBoundaryScale J B).val (Rat.ne_of_gt (effectiveBoundaryScale J B).property)
  have he : (effectiveBoundaryScale J B).val*scaledEffectiveTail J B n=effectiveBoundaryTail J B n := by
    dsimp [scaledEffectiveTail,effectiveBoundaryTail]; grind only
  rw [he] at hs
  have heq := FunctionTheory.sub_congr (equiv_refl _ (scale (effectiveBoundaryScale J B).val w).property)
    (RationalDilation.undo_right (effectiveBoundaryScale J B).val (effectiveBoundaryScale J B).property
      (continuousRectangleBoundary f J hd n))
  exact RepresentedCauchySum.small_sub_symm _ _ _ (Small.congr
    (sub_valid (scale (effectiveBoundaryScale J B).val w).property
      (scale (effectiveBoundaryScale J B).val (scaledEffectivePrefix f J hd B n)).property)
    (sub_valid (scaledEffectiveBoundaryValue f hf J hX hY hd B hder).property (continuousRectangleBoundary f J hd n).property)
    heq hs)

theorem scaledEffectiveBoundaryValue_converges (f : DomainFunctions.Map) (hf : Holomorphic f)
    (J : QInterval × QInterval) (hX : J.1.lo≤J.1.hi) (hY : J.2.lo≤J.2.hi)
    (hd : RectangleBoundaryDomains f J) (B : QPos)
    (hder : RectangleBoundaryDerivativeBound f hf J hd B) :
    Converges (continuousRectangleBoundary f J hd) (scaledEffectiveBoundaryValue f hf J hX hY hd B hder) := by
  intro eps
  exact ⟨RationalMajorant.natRateStage (effectiveBoundaryConstant J B) eps,fun n hn =>
    (scaledEffectiveBoundaryValue_prefix_error f hf J hX hY hd B hder n).mono
      (contour_half_rate _ (effectiveBoundaryConstant_nonneg J B hX hY) eps n hn)⟩

theorem scaledEffectiveBoundaryValue_agreement (f : DomainFunctions.Map) (hf : Holomorphic f)
    (J : QInterval × QInterval) (hX : J.1.lo≤J.1.hi) (hY : J.2.lo≤J.2.hi)
    (hd : RectangleBoundaryDomains f J) (B : QPos)
    (hder : RectangleBoundaryDerivativeBound f hf J hd B) :
    scaledEffectiveBoundaryValue f hf J hX hY hd B hder≈effectiveRectangleBoundaryValue f hf J hX hY hd B hder :=
  converge_unique _ _ _ (scaledEffectiveBoundaryValue_converges f hf J hX hY hd B hder)
    (effectiveRectangleBoundaryValue_converges f hf J hX hY hd B hder)

end ComputableAnalysis.RiemannHilbert.RectangularContour
