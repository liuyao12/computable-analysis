import ComputableAnalysis.RiemannHilbert.ContourEffectiveBoundary

/-! Constructed represented limits of the actual boundary quadratures.
The algorithm uses the supplied rational derivative bound. Prefix agreement,
convergence, and independence of that bound are proved afterwards. -/
namespace ComputableAnalysis.RiemannHilbert.RectangularContour
open ComplexRaw FunctionTheory DomainFunctions
set_option autoImplicit false

def effectiveRectangleBoundaryRaw (f : DomainFunctions.Map) (J : QInterval × QInterval)
    (hd : RectangleBoundaryDomains f J) (B : QPos) : ComplexRaw :=
  RepresentedCauchySum.value (fun n => (continuousRectangleBoundary f J hd n).val)
    (fun n => (continuousRectangleBoundary f J hd n).property) (effectiveBoundaryTail J B)

theorem effectiveRectangleBoundaryRaw_valid (f : DomainFunctions.Map) (hf : Holomorphic f)
    (J : QInterval × QInterval) (hX : J.1.lo≤J.1.hi) (hY : J.2.lo≤J.2.hi)
    (hd : RectangleBoundaryDomains f J) (B : QPos)
    (hder : RectangleBoundaryDerivativeBound f hf J hd B) : (effectiveRectangleBoundaryRaw f J hd B).Valid :=
  RepresentedCauchySum.value_valid _ _ _ (effectiveBoundaryTail_shrinks J B hX hY)
    (continuousRectangleBoundary_effective_cauchy f hf J hX hY hd B hder)

def effectiveRectangleBoundaryValue (f : DomainFunctions.Map) (hf : Holomorphic f)
    (J : QInterval × QInterval) (hX : J.1.lo≤J.1.hi) (hY : J.2.lo≤J.2.hi)
    (hd : RectangleBoundaryDomains f J) (B : QPos)
    (hder : RectangleBoundaryDerivativeBound f hf J hd B) : Scalar :=
  ⟨effectiveRectangleBoundaryRaw f J hd B,effectiveRectangleBoundaryRaw_valid f hf J hX hY hd B hder⟩

theorem effectiveRectangleBoundaryValue_prefix_error (f : DomainFunctions.Map) (hf : Holomorphic f)
    (J : QInterval × QInterval) (hX : J.1.lo≤J.1.hi) (hY : J.2.lo≤J.2.hi)
    (hd : RectangleBoundaryDomains f J) (B : QPos)
    (hder : RectangleBoundaryDerivativeBound f hf J hd B) (n : Nat) :
    Small (sub (continuousRectangleBoundary f J hd n).val
      (effectiveRectangleBoundaryValue f hf J hX hY hd B hder).val) (effectiveBoundaryTail J B n) :=
  RepresentedCauchySum.small_sub_symm _ _ _ (RepresentedCauchySum.value_close_prefix _ _ _
    (continuousRectangleBoundary_effective_cauchy f hf J hX hY hd B hder) n)

theorem effectiveRectangleBoundaryValue_converges (f : DomainFunctions.Map) (hf : Holomorphic f)
    (J : QInterval × QInterval) (hX : J.1.lo≤J.1.hi) (hY : J.2.lo≤J.2.hi)
    (hd : RectangleBoundaryDomains f J) (B : QPos)
    (hder : RectangleBoundaryDerivativeBound f hf J hd B) :
    Converges (continuousRectangleBoundary f J hd) (effectiveRectangleBoundaryValue f hf J hX hY hd B hder) := by
  intro eps
  refine ⟨RationalMajorant.natRateStage (effectiveBoundaryConstant J B) eps,fun n hn => ?_⟩
  exact (effectiveRectangleBoundaryValue_prefix_error f hf J hX hY hd B hder n).mono
    (contour_half_rate _ (effectiveBoundaryConstant_nonneg J B hX hY) eps n hn)

theorem effectiveRectangleBoundaryValue_limit_identity (f : DomainFunctions.Map) (hf : Holomorphic f)
    (J : QInterval × QInterval) (hX : J.1.lo≤J.1.hi) (hY : J.2.lo≤J.2.hi)
    (hd : RectangleBoundaryDomains f J) (B : QPos)
    (hder : RectangleBoundaryDerivativeBound f hf J hd B) (u : Scalar)
    (hu : Converges (continuousRectangleBoundary f J hd) u) :
    effectiveRectangleBoundaryValue f hf J hX hY hd B hder ≈ u :=
  converge_unique _ _ u (effectiveRectangleBoundaryValue_converges f hf J hX hY hd B hder) hu

theorem effectiveRectangleBoundaryValue_bound_independent (f : DomainFunctions.Map) (hf hg : Holomorphic f)
    (J : QInterval × QInterval) (hX : J.1.lo≤J.1.hi) (hY : J.2.lo≤J.2.hi)
    (hd : RectangleBoundaryDomains f J) (B C : QPos)
    (hB : RectangleBoundaryDerivativeBound f hf J hd B) (hC : RectangleBoundaryDerivativeBound f hg J hd C) :
    effectiveRectangleBoundaryValue f hf J hX hY hd B hB ≈ effectiveRectangleBoundaryValue f hg J hX hY hd C hC :=
  effectiveRectangleBoundaryValue_limit_identity f hf J hX hY hd B hB _
    (effectiveRectangleBoundaryValue_converges f hg J hX hY hd C hC)

theorem effectiveRectangleBoundaryValue_eval_congr (f g : DomainFunctions.Map) (hf : Holomorphic f) (hg : Holomorphic g)
    (J : QInterval × QInterval) (hX : J.1.lo≤J.1.hi) (hY : J.2.lo≤J.2.hi)
    (hd : RectangleBoundaryDomains f J) (he : RectangleBoundaryDomains g J) (B C : QPos)
    (hB : RectangleBoundaryDerivativeBound f hf J hd B) (hC : RectangleBoundaryDerivativeBound g hg J he C)
    (hfg : ∀ z (hfz : f.domain z) (hgz : g.domain z), f.eval z hfz ≈ g.eval z hgz) :
    effectiveRectangleBoundaryValue f hf J hX hY hd B hB ≈ effectiveRectangleBoundaryValue g hg J hX hY he C hC := by
  apply effectiveRectangleBoundaryValue_limit_identity f hf J hX hY hd B hB
  exact converge_congr _ _ _ (effectiveRectangleBoundaryValue_converges g hg J hX hY he C hC)
    (fun n => equiv_symm (continuousRectangleBoundary_eval_congr f g J hX hY hd he hfg n))

theorem effectiveRectangleBoundaryValue_zero (f : DomainFunctions.Map) (hf : Holomorphic f)
    (J : QInterval × QInterval) (hX : J.1.lo≤J.1.hi) (hY : J.2.lo≤J.2.hi)
    (hdom : ∀ z : Scalar, representedRectangleContains J z → f.domain z)
    (hd : RectangleBoundaryDomains f J) (B : QPos)
    (hder : RectangleBoundaryDerivativeBound f hf J hd B) :
    effectiveRectangleBoundaryValue f hf J hX hY hd B hder ≈ rationalRectangleScalar QComplex.zero :=
  effectiveRectangleBoundaryValue_limit_identity f hf J hX hY hd B hder _
    (converge_zero _ (continuousRectangleBoundary_eventual_zero f hf J hX hY hdom hd))

end ComputableAnalysis.RiemannHilbert.RectangularContour
