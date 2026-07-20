import ComputableAnalysis.ArctanGeometry
import ComputableAnalysis.ElementaryFunctions
import ComputableAnalysis.FTC
import ComputableAnalysis.RationalCircle

/-!
# Integral identities for elementary functions

This file records the comparison layer between geometric definitions and
definite-integral representations.  The geometric trigonometric algorithms are
not redefined here; instead, this file states the integral identities they
should satisfy once the derivative and Riemann-sum certificates are supplied.
-/

namespace ComputableAnalysis

namespace FunctionOnInterval

/-- Forget the interval-domain proof argument and expose an interval function
as a `RealFunRaw` with the interval as its domain.  Outside the interval the
compute field is a harmless dummy value; the domain field prevents it from
being used in theorem statements. -/
def toRealFunRaw (F : FunctionOnInterval) : RealFunRaw where
  domain := inDomainInterval F.lower F.upper
  compute := fun x n =>
    if hleft : F.lower <= x then
      if hright : x <= F.upper then
        F.compute x ⟨hleft, hright⟩ n
      else
        { lo := 0, hi := 0 }
    else
      { lo := 0, hi := 0 }

theorem toRealFunRaw_compute_of_mem
    (F : FunctionOnInterval) {x : Rat}
    (hx : inDomainInterval F.lower F.upper x) (n : Nat) :
    F.toRealFunRaw.compute x n = F.compute x hx n := by
  rcases hx with ⟨hleft, hright⟩
  simp [toRealFunRaw, hleft, hright]

theorem toRealFunRaw_valid (F : FunctionOnInterval) :
    F.toRealFunRaw.Valid := by
  intro x hx
  have hcompute :
      F.toRealFunRaw.compute x = F.raw.compute x (F.defined_on x hx) := by
    funext n
    rw [toRealFunRaw_compute_of_mem F hx n]
    rfl
  rw [RealFunRaw.applyCompute, hcompute]
  exact F.valid_on x (F.defined_on x hx)

/-- Domain-aware endpoint telescoping for an interval-certified primitive. -/
theorem endpointDifferenceRaw_adjacent_additive
    (F : FunctionOnInterval) {a b c : Rat}
    (ha : F.lower <= a) (hab : a <= b) (hbc : b <= c)
    (hc : c <= F.upper)
    (hab_valid :
      RealRaw.ValidCompute (endpointDifferenceCompute F.toRealFunRaw a b))
    (hbc_valid :
      RealRaw.ValidCompute (endpointDifferenceCompute F.toRealFunRaw b c))
    (hac_valid :
      RealRaw.ValidCompute (endpointDifferenceCompute F.toRealFunRaw a c)) :
    ((endpointDifferenceRaw F.toRealFunRaw a b hab_valid) +
      (endpointDifferenceRaw F.toRealFunRaw b c hbc_valid)).Equiv
        (endpointDifferenceRaw F.toRealFunRaw a c hac_valid) :=
  ComputableAnalysis.endpointDifferenceRaw_adjacent_additive
    F.toRealFunRaw_valid
    ⟨ha, Rat.le_trans hab (Rat.le_trans hbc hc)⟩
    ⟨Rat.le_trans ha hab, Rat.le_trans hbc hc⟩
    ⟨Rat.le_trans ha (Rat.le_trans hab hbc), hc⟩
    hab_valid hbc_valid hac_valid

end FunctionOnInterval

namespace Integral

/-- A definite-integral identity on raw total functions:
the integral of `integrand` over `[a,b]` equals the endpoint difference of the
primitive. -/
structure DefiniteIdentity
    (integrand primitive : RealFunRaw) (a b : Rat) where
  construction : Integral.Construction integrand a b
  endpoint_valid :
    RealRaw.ValidCompute (endpointDifferenceCompute primitive a b)
  equivalent :
    DefiniteIntegralEqualsEndpointDifference
      primitive integrand a b construction endpoint_valid

namespace DefiniteIdentity

theorem integral_valid
    {integrand primitive : RealFunRaw} {a b : Rat}
    (I : DefiniteIdentity integrand primitive a b) :
    (Integral.integral integrand a b I.construction).Valid :=
  FTC.integral_valid_of_construction I.construction

theorem endpoint_formula
    {integrand primitive : RealFunRaw} {a b : Rat}
    (I : DefiniteIdentity integrand primitive a b) :
    DefiniteIntegralEqualsEndpointDifference
      primitive integrand a b I.construction I.endpoint_valid :=
  I.equivalent

end DefiniteIdentity

/-- The same definite-integral identity, but with both functions already
certified on a finite rational interval. -/
structure DefiniteIdentityOnInterval
    (integrand primitive : FunctionOnInterval) where
  same_lower : primitive.lower = integrand.lower
  same_upper : primitive.upper = integrand.upper
  construction :
    Integral.Construction
      integrand.toRealFunRaw integrand.lower integrand.upper
  endpoint_valid :
    RealRaw.ValidCompute
      (endpointDifferenceCompute
        primitive.toRealFunRaw integrand.lower integrand.upper)
  equivalent :
    DefiniteIntegralEqualsEndpointDifference
      primitive.toRealFunRaw integrand.toRealFunRaw
      integrand.lower integrand.upper construction endpoint_valid

namespace DefiniteIdentityOnInterval

def toDefiniteIdentity
    {integrand primitive : FunctionOnInterval}
    (I : DefiniteIdentityOnInterval integrand primitive) :
    DefiniteIdentity
      integrand.toRealFunRaw primitive.toRealFunRaw
      integrand.lower integrand.upper where
  construction := I.construction
  endpoint_valid := I.endpoint_valid
  equivalent := I.equivalent

theorem integral_valid
    {integrand primitive : FunctionOnInterval}
    (I : DefiniteIdentityOnInterval integrand primitive) :
    (Integral.integral
      integrand.toRealFunRaw integrand.lower integrand.upper
      I.construction).Valid :=
  I.toDefiniteIdentity.integral_valid

theorem endpoint_formula
    {integrand primitive : FunctionOnInterval}
    (I : DefiniteIdentityOnInterval integrand primitive) :
    DefiniteIntegralEqualsEndpointDifference
      primitive.toRealFunRaw integrand.toRealFunRaw
      integrand.lower integrand.upper I.construction I.endpoint_valid :=
  I.equivalent

end DefiniteIdentityOnInterval

/-- A definite-integral identity for the domain-aware `ConstructionFor`
interface.  This is the version used by hand-built interval constructions,
where the raw computation is already a valid integral on the whole
`FunctionOnInterval` but is not necessarily presented as the generic
left-Riemann `Integral.Construction` plan. -/
structure DefiniteIdentityFor
    (integrand primitive : FunctionOnInterval) where
  same_lower : primitive.lower = integrand.lower
  same_upper : primitive.upper = integrand.upper
  construction : Integral.ConstructionFor integrand
  endpoint_valid :
    RealRaw.ValidCompute
      (endpointDifferenceCompute
        primitive.toRealFunRaw integrand.lower integrand.upper)
  equivalent :
    (Integral.integralFor integrand construction).Equiv
      (endpointDifferenceRaw
        primitive.toRealFunRaw integrand.lower integrand.upper
        endpoint_valid)

namespace DefiniteIdentityFor

theorem integral_valid
    {integrand primitive : FunctionOnInterval}
    (I : DefiniteIdentityFor integrand primitive) :
    (Integral.integralFor integrand I.construction).Valid :=
  Integral.integralFor_valid integrand I.construction

theorem endpoint_formula
    {integrand primitive : FunctionOnInterval}
    (I : DefiniteIdentityFor integrand primitive) :
    (Integral.integralFor integrand I.construction).Equiv
      (endpointDifferenceRaw
        primitive.toRealFunRaw integrand.lower integrand.upper
        I.endpoint_valid) :=
  I.equivalent

theorem endpoint_raw_valid
    {integrand primitive : FunctionOnInterval}
    (I : DefiniteIdentityFor integrand primitive) :
    (endpointDifferenceRaw
      primitive.toRealFunRaw integrand.lower integrand.upper
      I.endpoint_valid).Valid := by
  simpa [endpointDifferenceRaw, RealRaw.Valid] using I.endpoint_valid

/-- Replace the integral construction in a domain-aware definite-integral
identity by an equivalent construction. -/
def transportConstruction
    {integrand primitive : FunctionOnInterval}
    (I : DefiniteIdentityFor integrand primitive)
    (construction' : Integral.ConstructionFor integrand)
    (hconstruction :
      (Integral.integralFor integrand construction').Equiv
        (Integral.integralFor integrand I.construction)) :
    DefiniteIdentityFor integrand primitive where
  same_lower := I.same_lower
  same_upper := I.same_upper
  construction := construction'
  endpoint_valid := I.endpoint_valid
  equivalent := by
    exact RealRaw.equiv_trans
      (Integral.integralFor_valid integrand construction')
      I.integral_valid
      I.endpoint_raw_valid
      hconstruction
      I.equivalent

/-- Two domain-aware definite-integral identities for the same integrand and
primitive have equivalent integral raw reals. -/
theorem integral_equiv_integral
    {integrand primitive : FunctionOnInterval}
    (I J : DefiniteIdentityFor integrand primitive) :
    (Integral.integralFor integrand I.construction).Equiv
      (Integral.integralFor integrand J.construction) := by
  exact RealRaw.equiv_trans
    I.integral_valid
    I.endpoint_raw_valid
    J.integral_valid
    I.equivalent
    (RealRaw.equiv_symm J.equivalent)

/-- Additivity transfers from endpoint differences to integrals once each
piece has a definite-integral identity.

This is the FTC-facing algebra step: after proving
`∫_a^b f = F(b)-F(a)`, `∫_b^c f = F(c)-F(b)`, and
`∫_a^c f = F(c)-F(a)`, the remaining additivity proof is just endpoint
telescoping. -/
theorem integral_add_equiv_of_endpoint_additive
    {integrandAB primitiveAB integrandBC primitiveBC integrandAC primitiveAC :
      FunctionOnInterval}
    (Iab : DefiniteIdentityFor integrandAB primitiveAB)
    (Ibc : DefiniteIdentityFor integrandBC primitiveBC)
    (Iac : DefiniteIdentityFor integrandAC primitiveAC)
    (hendpoint :
      ((endpointDifferenceRaw primitiveAB.toRealFunRaw
          integrandAB.lower integrandAB.upper Iab.endpoint_valid) +
        (endpointDifferenceRaw primitiveBC.toRealFunRaw
          integrandBC.lower integrandBC.upper Ibc.endpoint_valid)).Equiv
          (endpointDifferenceRaw primitiveAC.toRealFunRaw
            integrandAC.lower integrandAC.upper Iac.endpoint_valid)) :
    ((Integral.integralFor integrandAB Iab.construction) +
      (Integral.integralFor integrandBC Ibc.construction)).Equiv
        (Integral.integralFor integrandAC Iac.construction) := by
  have hsum_integral_valid :
      ((Integral.integralFor integrandAB Iab.construction) +
        (Integral.integralFor integrandBC Ibc.construction)).Valid :=
    RealRaw.add_valid Iab.integral_valid Ibc.integral_valid
  have hsum_endpoint_valid :
      ((endpointDifferenceRaw primitiveAB.toRealFunRaw
          integrandAB.lower integrandAB.upper Iab.endpoint_valid) +
        (endpointDifferenceRaw primitiveBC.toRealFunRaw
          integrandBC.lower integrandBC.upper Ibc.endpoint_valid)).Valid :=
    RealRaw.add_valid Iab.endpoint_raw_valid Ibc.endpoint_raw_valid
  have hintegral_to_endpoint :
      ((Integral.integralFor integrandAB Iab.construction) +
        (Integral.integralFor integrandBC Ibc.construction)).Equiv
          ((endpointDifferenceRaw primitiveAB.toRealFunRaw
              integrandAB.lower integrandAB.upper Iab.endpoint_valid) +
            (endpointDifferenceRaw primitiveBC.toRealFunRaw
              integrandBC.lower integrandBC.upper Ibc.endpoint_valid)) :=
    RealRaw.add_equiv
      Iab.integral_valid Iab.endpoint_raw_valid
      Ibc.integral_valid Ibc.endpoint_raw_valid
      Iab.equivalent Ibc.equivalent
  have hintegral_to_ac_endpoint :
      ((Integral.integralFor integrandAB Iab.construction) +
        (Integral.integralFor integrandBC Ibc.construction)).Equiv
          (endpointDifferenceRaw primitiveAC.toRealFunRaw
            integrandAC.lower integrandAC.upper Iac.endpoint_valid) :=
    RealRaw.equiv_trans
      hsum_integral_valid hsum_endpoint_valid Iac.endpoint_raw_valid
      hintegral_to_endpoint hendpoint
  exact RealRaw.equiv_trans
    hsum_integral_valid Iac.endpoint_raw_valid Iac.integral_valid
    hintegral_to_ac_endpoint
    (RealRaw.equiv_symm Iac.equivalent)

/-- Linearity-facing orientation of
`integral_add_equiv_of_endpoint_additive`.

If the endpoint difference of `H` is the sum of the endpoint differences of
`F` and `G`, then the integral of `H` is the sum of the integrals of `F` and
`G`. -/
theorem integral_equiv_add_of_endpoint_add
    {integrandF primitiveF integrandG primitiveG integrandH primitiveH :
      FunctionOnInterval}
    (IF : DefiniteIdentityFor integrandF primitiveF)
    (IG : DefiniteIdentityFor integrandG primitiveG)
    (IH : DefiniteIdentityFor integrandH primitiveH)
    (hendpoint :
      (endpointDifferenceRaw primitiveH.toRealFunRaw
        integrandH.lower integrandH.upper IH.endpoint_valid).Equiv
          ((endpointDifferenceRaw primitiveF.toRealFunRaw
              integrandF.lower integrandF.upper IF.endpoint_valid) +
            (endpointDifferenceRaw primitiveG.toRealFunRaw
              integrandG.lower integrandG.upper IG.endpoint_valid))) :
    (Integral.integralFor integrandH IH.construction).Equiv
      ((Integral.integralFor integrandF IF.construction) +
        (Integral.integralFor integrandG IG.construction)) :=
  RealRaw.equiv_symm
    (integral_add_equiv_of_endpoint_additive
      IF IG IH (RealRaw.equiv_symm hendpoint))

/-- Rational scaling transfers from endpoint differences to
integrals once both sides have definite-integral identities.

This is the scalar analogue of
`integral_add_equiv_of_endpoint_additive`. -/
theorem integral_scaleRat_equiv_of_endpoint_scaleRat
    {integrand primitive scaledIntegrand scaledPrimitive : FunctionOnInterval}
    {r : Rat}
    (I : DefiniteIdentityFor integrand primitive)
    (J : DefiniteIdentityFor scaledIntegrand scaledPrimitive)
    (hendpoint :
      (endpointDifferenceRaw scaledPrimitive.toRealFunRaw
        scaledIntegrand.lower scaledIntegrand.upper J.endpoint_valid).Equiv
        (RealRaw.scaleRat r
          (endpointDifferenceRaw primitive.toRealFunRaw
            integrand.lower integrand.upper I.endpoint_valid))) :
    (Integral.integralFor scaledIntegrand J.construction).Equiv
      (RealRaw.scaleRat r
        (Integral.integralFor integrand I.construction)) := by
  have hscaled_endpoint_valid :
      (RealRaw.scaleRat r
        (endpointDifferenceRaw primitive.toRealFunRaw
          integrand.lower integrand.upper I.endpoint_valid)).Valid :=
    RealRaw.scaleRat_valid I.endpoint_raw_valid
  have hscaled_integral_valid :
      (RealRaw.scaleRat r
        (Integral.integralFor integrand I.construction)).Valid :=
    RealRaw.scaleRat_valid I.integral_valid
  have hintegral_to_scaled_endpoint :
      (Integral.integralFor scaledIntegrand J.construction).Equiv
        (RealRaw.scaleRat r
          (endpointDifferenceRaw primitive.toRealFunRaw
            integrand.lower integrand.upper I.endpoint_valid)) :=
    RealRaw.equiv_trans
      J.integral_valid J.endpoint_raw_valid hscaled_endpoint_valid
      J.equivalent hendpoint
  exact RealRaw.equiv_trans
    J.integral_valid hscaled_endpoint_valid hscaled_integral_valid
    hintegral_to_scaled_endpoint
    (RealRaw.equiv_symm
      (RealRaw.scaleRat_equiv I.equivalent))

/-- Order transfers from endpoint differences to integrals once both sides
have definite-integral identities.

This is the order analogue of the endpoint-additivity and endpoint-scaling
transfer theorems: after FTC has identified each integral with a primitive
endpoint difference, it remains only to prove the endpoint differences are
ordered. -/
theorem integral_le_of_endpoint_le
    {integrandF primitiveF integrandG primitiveG : FunctionOnInterval}
    (IF : DefiniteIdentityFor integrandF primitiveF)
    (IG : DefiniteIdentityFor integrandG primitiveG)
    (hendpoint :
      (endpointDifferenceRaw primitiveF.toRealFunRaw
        integrandF.lower integrandF.upper IF.endpoint_valid).Le
        (endpointDifferenceRaw primitiveG.toRealFunRaw
          integrandG.lower integrandG.upper IG.endpoint_valid)) :
    (Integral.integralFor integrandF IF.construction).Le
      (Integral.integralFor integrandG IG.construction) := by
  have hleft :
      (Integral.integralFor integrandF IF.construction).Le
        (endpointDifferenceRaw primitiveF.toRealFunRaw
          integrandF.lower integrandF.upper IF.endpoint_valid) :=
    RealRaw.le_of_equiv IF.integral_valid IF.endpoint_raw_valid IF.equivalent
  have hright :
      (endpointDifferenceRaw primitiveG.toRealFunRaw
        integrandG.lower integrandG.upper IG.endpoint_valid).Le
        (Integral.integralFor integrandG IG.construction) :=
    RealRaw.le_of_equiv IG.endpoint_raw_valid IG.integral_valid
      (RealRaw.equiv_symm IG.equivalent)
  exact RealRaw.le_trans IG.endpoint_raw_valid
    (RealRaw.le_trans IF.endpoint_raw_valid hleft hendpoint)
    hright

end DefiniteIdentityFor

/-- A definite-integral identity whose integral side is explicitly supplied by
a monotone-integral construction. -/
structure MonotoneDefiniteIdentityFor
    (integrand primitive : FunctionOnInterval) where
  same_lower : primitive.lower = integrand.lower
  same_upper : primitive.upper = integrand.upper
  construction : Integral.MonotoneConstructionFor integrand
  endpoint_valid :
    RealRaw.ValidCompute
      (endpointDifferenceCompute
        primitive.toRealFunRaw integrand.lower integrand.upper)
  equivalent :
    (Integral.monotoneIntegralFor integrand construction).Equiv
      (endpointDifferenceRaw
        primitive.toRealFunRaw integrand.lower integrand.upper
        endpoint_valid)

namespace MonotoneDefiniteIdentityFor

def toDefiniteIdentityFor
    {integrand primitive : FunctionOnInterval}
    (I : MonotoneDefiniteIdentityFor integrand primitive) :
    DefiniteIdentityFor integrand primitive where
  same_lower := I.same_lower
  same_upper := I.same_upper
  construction := I.construction.construction
  endpoint_valid := I.endpoint_valid
  equivalent := by
    simpa [Integral.monotoneIntegralFor] using I.equivalent

theorem integral_valid
    {integrand primitive : FunctionOnInterval}
    (I : MonotoneDefiniteIdentityFor integrand primitive) :
    (Integral.monotoneIntegralFor integrand I.construction).Valid :=
  Integral.monotoneIntegralFor_valid integrand I.construction

theorem endpoint_raw_valid
    {integrand primitive : FunctionOnInterval}
    (I : MonotoneDefiniteIdentityFor integrand primitive) :
    (endpointDifferenceRaw
      primitive.toRealFunRaw integrand.lower integrand.upper
      I.endpoint_valid).Valid := by
  simpa [endpointDifferenceRaw, RealRaw.Valid] using I.endpoint_valid

theorem endpoint_formula
    {integrand primitive : FunctionOnInterval}
    (I : MonotoneDefiniteIdentityFor integrand primitive) :
    (Integral.monotoneIntegralFor integrand I.construction).Equiv
      (endpointDifferenceRaw
        primitive.toRealFunRaw integrand.lower integrand.upper
        I.endpoint_valid) :=
  I.equivalent

/-- Monotone-facing version of
`DefiniteIdentityFor.integral_add_equiv_of_endpoint_additive`. -/
theorem integral_add_equiv_of_endpoint_additive
    {integrandAB primitiveAB integrandBC primitiveBC integrandAC primitiveAC :
      FunctionOnInterval}
    (Iab : MonotoneDefiniteIdentityFor integrandAB primitiveAB)
    (Ibc : MonotoneDefiniteIdentityFor integrandBC primitiveBC)
    (Iac : MonotoneDefiniteIdentityFor integrandAC primitiveAC)
    (hendpoint :
      ((endpointDifferenceRaw primitiveAB.toRealFunRaw
          integrandAB.lower integrandAB.upper Iab.endpoint_valid) +
        (endpointDifferenceRaw primitiveBC.toRealFunRaw
          integrandBC.lower integrandBC.upper Ibc.endpoint_valid)).Equiv
          (endpointDifferenceRaw primitiveAC.toRealFunRaw
            integrandAC.lower integrandAC.upper Iac.endpoint_valid)) :
    ((Integral.monotoneIntegralFor integrandAB Iab.construction) +
      (Integral.monotoneIntegralFor integrandBC Ibc.construction)).Equiv
        (Integral.monotoneIntegralFor integrandAC Iac.construction) := by
  simpa [MonotoneDefiniteIdentityFor.toDefiniteIdentityFor,
    Integral.monotoneIntegralFor] using
    DefiniteIdentityFor.integral_add_equiv_of_endpoint_additive
      Iab.toDefiniteIdentityFor Ibc.toDefiniteIdentityFor
      Iac.toDefiniteIdentityFor hendpoint

/-- Monotone-facing version of
`DefiniteIdentityFor.integral_equiv_add_of_endpoint_add`. -/
theorem integral_equiv_add_of_endpoint_add
    {integrandF primitiveF integrandG primitiveG integrandH primitiveH :
      FunctionOnInterval}
    (IF : MonotoneDefiniteIdentityFor integrandF primitiveF)
    (IG : MonotoneDefiniteIdentityFor integrandG primitiveG)
    (IH : MonotoneDefiniteIdentityFor integrandH primitiveH)
    (hendpoint :
      (endpointDifferenceRaw primitiveH.toRealFunRaw
        integrandH.lower integrandH.upper IH.endpoint_valid).Equiv
          ((endpointDifferenceRaw primitiveF.toRealFunRaw
              integrandF.lower integrandF.upper IF.endpoint_valid) +
            (endpointDifferenceRaw primitiveG.toRealFunRaw
              integrandG.lower integrandG.upper IG.endpoint_valid))) :
    (Integral.monotoneIntegralFor integrandH IH.construction).Equiv
      ((Integral.monotoneIntegralFor integrandF IF.construction) +
        (Integral.monotoneIntegralFor integrandG IG.construction)) := by
  simpa [MonotoneDefiniteIdentityFor.toDefiniteIdentityFor,
    Integral.monotoneIntegralFor] using
    DefiniteIdentityFor.integral_equiv_add_of_endpoint_add
      IF.toDefiniteIdentityFor IG.toDefiniteIdentityFor
      IH.toDefiniteIdentityFor hendpoint

/-- Monotone-facing version of
`DefiniteIdentityFor.integral_scaleRat_equiv_of_endpoint_scaleRat`. -/
theorem integral_scaleRat_equiv_of_endpoint_scaleRat
    {integrand primitive scaledIntegrand scaledPrimitive : FunctionOnInterval}
    {r : Rat}
    (I : MonotoneDefiniteIdentityFor integrand primitive)
    (J : MonotoneDefiniteIdentityFor scaledIntegrand scaledPrimitive)
    (hendpoint :
      (endpointDifferenceRaw scaledPrimitive.toRealFunRaw
        scaledIntegrand.lower scaledIntegrand.upper J.endpoint_valid).Equiv
        (RealRaw.scaleRat r
          (endpointDifferenceRaw primitive.toRealFunRaw
            integrand.lower integrand.upper I.endpoint_valid))) :
    (Integral.monotoneIntegralFor scaledIntegrand J.construction).Equiv
      (RealRaw.scaleRat r
        (Integral.monotoneIntegralFor integrand I.construction)) := by
  simpa [MonotoneDefiniteIdentityFor.toDefiniteIdentityFor,
    Integral.monotoneIntegralFor] using
    DefiniteIdentityFor.integral_scaleRat_equiv_of_endpoint_scaleRat
      I.toDefiniteIdentityFor J.toDefiniteIdentityFor hendpoint

/-- Monotone-facing version of
`DefiniteIdentityFor.integral_le_of_endpoint_le`. -/
theorem integral_le_of_endpoint_le
    {integrandF primitiveF integrandG primitiveG : FunctionOnInterval}
    (IF : MonotoneDefiniteIdentityFor integrandF primitiveF)
    (IG : MonotoneDefiniteIdentityFor integrandG primitiveG)
    (hendpoint :
      (endpointDifferenceRaw primitiveF.toRealFunRaw
        integrandF.lower integrandF.upper IF.endpoint_valid).Le
        (endpointDifferenceRaw primitiveG.toRealFunRaw
          integrandG.lower integrandG.upper IG.endpoint_valid)) :
    (Integral.monotoneIntegralFor integrandF IF.construction).Le
      (Integral.monotoneIntegralFor integrandG IG.construction) := by
  simpa [MonotoneDefiniteIdentityFor.toDefiniteIdentityFor,
    Integral.monotoneIntegralFor] using
    DefiniteIdentityFor.integral_le_of_endpoint_le
      IF.toDefiniteIdentityFor IG.toDefiniteIdentityFor hendpoint

end MonotoneDefiniteIdentityFor

/-- A definite-integral identity whose integral side is supplied by the public
general integral interface: a finite sum over monotone pieces. -/
structure GeneralDefiniteIdentityFor
    (integrand primitive : FunctionOnInterval) where
  same_lower : primitive.lower = integrand.lower
  same_upper : primitive.upper = integrand.upper
  construction : Integral.GeneralConstructionFor integrand
  endpoint_valid :
    RealRaw.ValidCompute
      (endpointDifferenceCompute
        primitive.toRealFunRaw integrand.lower integrand.upper)
  equivalent :
    (Integral.generalIntegralFor integrand construction).Equiv
      (endpointDifferenceRaw
        primitive.toRealFunRaw integrand.lower integrand.upper
        endpoint_valid)

namespace GeneralDefiniteIdentityFor

theorem integral_valid
    {integrand primitive : FunctionOnInterval}
    (I : GeneralDefiniteIdentityFor integrand primitive) :
    (Integral.generalIntegralFor integrand I.construction).Valid :=
  Integral.generalIntegralFor_valid integrand I.construction

theorem endpoint_raw_valid
    {integrand primitive : FunctionOnInterval}
    (I : GeneralDefiniteIdentityFor integrand primitive) :
    (endpointDifferenceRaw
      primitive.toRealFunRaw integrand.lower integrand.upper
      I.endpoint_valid).Valid := by
  simpa [endpointDifferenceRaw, RealRaw.Valid] using I.endpoint_valid

theorem endpoint_formula
    {integrand primitive : FunctionOnInterval}
    (I : GeneralDefiniteIdentityFor integrand primitive) :
    (Integral.generalIntegralFor integrand I.construction).Equiv
      (endpointDifferenceRaw
        primitive.toRealFunRaw integrand.lower integrand.upper
        I.endpoint_valid) :=
  I.equivalent

/-- Forget that the integral was built by the public general construction and
view it through the ordinary domain-aware definite-integral identity
interface. -/
def toDefiniteIdentityFor
    {integrand primitive : FunctionOnInterval}
    (I : GeneralDefiniteIdentityFor integrand primitive) :
    DefiniteIdentityFor integrand primitive where
  same_lower := I.same_lower
  same_upper := I.same_upper
  construction :=
    { compute := (Integral.generalIntegralFor integrand I.construction).compute
      certificate := by
        simpa [RealRaw.Valid] using I.integral_valid }
  endpoint_valid := I.endpoint_valid
  equivalent := by
    change (Integral.generalIntegralFor integrand I.construction).Equiv
      (endpointDifferenceRaw
        primitive.toRealFunRaw integrand.lower integrand.upper
        I.endpoint_valid)
    exact I.equivalent

/-- Replace the public general construction in a general definite-integral
identity by an equivalent general construction. -/
def transportConstruction
    {integrand primitive : FunctionOnInterval}
    (I : GeneralDefiniteIdentityFor integrand primitive)
    (construction' : Integral.GeneralConstructionFor integrand)
    (hconstruction :
      (Integral.generalIntegralFor integrand construction').Equiv
        (Integral.generalIntegralFor integrand I.construction)) :
    GeneralDefiniteIdentityFor integrand primitive where
  same_lower := I.same_lower
  same_upper := I.same_upper
  construction := construction'
  endpoint_valid := I.endpoint_valid
  equivalent := by
    exact RealRaw.equiv_trans
      (Integral.generalIntegralFor_valid integrand construction')
      I.integral_valid
      I.endpoint_raw_valid
      hconstruction
      I.equivalent

/-- Promote an ordinary domain-aware definite-integral identity to the public
general-integral interface when a general construction computes an equivalent
raw real. -/
def ofDefiniteIdentityFor
    {integrand primitive : FunctionOnInterval}
    (I : DefiniteIdentityFor integrand primitive)
    (construction : Integral.GeneralConstructionFor integrand)
    (hconstruction :
      (Integral.generalIntegralFor integrand construction).Equiv
        (Integral.integralFor integrand I.construction)) :
    GeneralDefiniteIdentityFor integrand primitive where
  same_lower := I.same_lower
  same_upper := I.same_upper
  construction := construction
  endpoint_valid := I.endpoint_valid
  equivalent := by
    exact RealRaw.equiv_trans
      (Integral.generalIntegralFor_valid integrand construction)
      I.integral_valid
      I.endpoint_raw_valid
      hconstruction
      I.equivalent

/-- Two general definite-integral identities for the same integrand and
primitive have equivalent general-integral raw reals. -/
theorem integral_equiv_integral
    {integrand primitive : FunctionOnInterval}
    (I J : GeneralDefiniteIdentityFor integrand primitive) :
    (Integral.generalIntegralFor integrand I.construction).Equiv
      (Integral.generalIntegralFor integrand J.construction) := by
  exact RealRaw.equiv_trans
    I.integral_valid
    I.endpoint_raw_valid
    J.integral_valid
    I.equivalent
    (RealRaw.equiv_symm J.equivalent)

/-- General-integral version of
`DefiniteIdentityFor.integral_add_equiv_of_endpoint_additive`. -/
theorem integral_add_equiv_of_endpoint_additive
    {integrandAB primitiveAB integrandBC primitiveBC integrandAC primitiveAC :
      FunctionOnInterval}
    (Iab : GeneralDefiniteIdentityFor integrandAB primitiveAB)
    (Ibc : GeneralDefiniteIdentityFor integrandBC primitiveBC)
    (Iac : GeneralDefiniteIdentityFor integrandAC primitiveAC)
    (hendpoint :
      ((endpointDifferenceRaw primitiveAB.toRealFunRaw
          integrandAB.lower integrandAB.upper Iab.endpoint_valid) +
        (endpointDifferenceRaw primitiveBC.toRealFunRaw
          integrandBC.lower integrandBC.upper Ibc.endpoint_valid)).Equiv
          (endpointDifferenceRaw primitiveAC.toRealFunRaw
            integrandAC.lower integrandAC.upper Iac.endpoint_valid)) :
    ((Integral.generalIntegralFor integrandAB Iab.construction) +
      (Integral.generalIntegralFor integrandBC Ibc.construction)).Equiv
        (Integral.generalIntegralFor integrandAC Iac.construction) := by
  simpa [GeneralDefiniteIdentityFor.toDefiniteIdentityFor,
    Integral.integralFor] using
    DefiniteIdentityFor.integral_add_equiv_of_endpoint_additive
      Iab.toDefiniteIdentityFor Ibc.toDefiniteIdentityFor
      Iac.toDefiniteIdentityFor hendpoint

/-- General-integral version of
`DefiniteIdentityFor.integral_equiv_add_of_endpoint_add`. -/
theorem integral_equiv_add_of_endpoint_add
    {integrandF primitiveF integrandG primitiveG integrandH primitiveH :
      FunctionOnInterval}
    (IF : GeneralDefiniteIdentityFor integrandF primitiveF)
    (IG : GeneralDefiniteIdentityFor integrandG primitiveG)
    (IH : GeneralDefiniteIdentityFor integrandH primitiveH)
    (hendpoint :
      (endpointDifferenceRaw primitiveH.toRealFunRaw
        integrandH.lower integrandH.upper IH.endpoint_valid).Equiv
          ((endpointDifferenceRaw primitiveF.toRealFunRaw
              integrandF.lower integrandF.upper IF.endpoint_valid) +
            (endpointDifferenceRaw primitiveG.toRealFunRaw
              integrandG.lower integrandG.upper IG.endpoint_valid))) :
    (Integral.generalIntegralFor integrandH IH.construction).Equiv
      ((Integral.generalIntegralFor integrandF IF.construction) +
        (Integral.generalIntegralFor integrandG IG.construction)) := by
  simpa [GeneralDefiniteIdentityFor.toDefiniteIdentityFor,
    Integral.integralFor] using
    DefiniteIdentityFor.integral_equiv_add_of_endpoint_add
      IF.toDefiniteIdentityFor IG.toDefiniteIdentityFor
      IH.toDefiniteIdentityFor hendpoint

/-- General-integral version of
`DefiniteIdentityFor.integral_scaleRat_equiv_of_endpoint_scaleRat`. -/
theorem integral_scaleRat_equiv_of_endpoint_scaleRat
    {integrand primitive scaledIntegrand scaledPrimitive : FunctionOnInterval}
    {r : Rat}
    (I : GeneralDefiniteIdentityFor integrand primitive)
    (J : GeneralDefiniteIdentityFor scaledIntegrand scaledPrimitive)
    (hendpoint :
      (endpointDifferenceRaw scaledPrimitive.toRealFunRaw
        scaledIntegrand.lower scaledIntegrand.upper J.endpoint_valid).Equiv
        (RealRaw.scaleRat r
          (endpointDifferenceRaw primitive.toRealFunRaw
            integrand.lower integrand.upper I.endpoint_valid))) :
    (Integral.generalIntegralFor scaledIntegrand J.construction).Equiv
      (RealRaw.scaleRat r
        (Integral.generalIntegralFor integrand I.construction)) := by
  simpa [GeneralDefiniteIdentityFor.toDefiniteIdentityFor,
    Integral.integralFor] using
    DefiniteIdentityFor.integral_scaleRat_equiv_of_endpoint_scaleRat
      I.toDefiniteIdentityFor J.toDefiniteIdentityFor hendpoint

/-- General-integral version of
`DefiniteIdentityFor.integral_le_of_endpoint_le`. -/
theorem integral_le_of_endpoint_le
    {integrandF primitiveF integrandG primitiveG : FunctionOnInterval}
    (IF : GeneralDefiniteIdentityFor integrandF primitiveF)
    (IG : GeneralDefiniteIdentityFor integrandG primitiveG)
    (hendpoint :
      (endpointDifferenceRaw primitiveF.toRealFunRaw
        integrandF.lower integrandF.upper IF.endpoint_valid).Le
        (endpointDifferenceRaw primitiveG.toRealFunRaw
          integrandG.lower integrandG.upper IG.endpoint_valid)) :
    (Integral.generalIntegralFor integrandF IF.construction).Le
      (Integral.generalIntegralFor integrandG IG.construction) := by
  simpa [GeneralDefiniteIdentityFor.toDefiniteIdentityFor,
    Integral.integralFor] using
    DefiniteIdentityFor.integral_le_of_endpoint_le
      IF.toDefiniteIdentityFor IG.toDefiniteIdentityFor hendpoint

/-- Promote a one-piece monotone endpoint identity to the public general
integral interface. -/
noncomputable def ofMonotone
    {integrand primitive : FunctionOnInterval}
    (I : MonotoneDefiniteIdentityFor integrand primitive)
    (hinterval : integrand.lower <= integrand.upper) :
    GeneralDefiniteIdentityFor integrand primitive where
  same_lower := I.same_lower
  same_upper := I.same_upper
  construction :=
    Integral.PiecewiseMonotoneConstructionFor.ofMonotone
      I.construction hinterval
  endpoint_valid := I.endpoint_valid
  equivalent := by
    have hgeneral :
        (Integral.generalIntegralFor integrand
          (Integral.PiecewiseMonotoneConstructionFor.ofMonotone
            I.construction hinterval)).Equiv
          (Integral.monotoneIntegralFor integrand I.construction) :=
      Integral.generalIntegralFor_ofMonotone_equiv
        I.construction hinterval
    exact RealRaw.equiv_trans
      (Integral.generalIntegralFor_valid integrand
        (Integral.PiecewiseMonotoneConstructionFor.ofMonotone
          I.construction hinterval))
      I.integral_valid
      I.endpoint_raw_valid
      hgeneral
      I.equivalent

end GeneralDefiniteIdentityFor

def definiteIdentity_of_effectiveFTC
    {primitive integrand : RealFunRaw} {a b : Rat}
    (h : EffectiveFTC primitive integrand a b)
    (c : Integral.Construction integrand a b)
    (hendpoint :
      RealRaw.ValidCompute (endpointDifferenceCompute primitive a b))
    (hplan : c.plan = FTC.integralPlanOfEffectiveFTC h)
    (hscheduledEndpoint : (FTC.endpointRawOfEffectiveFTC h).Valid)
    (hendpoint_equiv :
      (FTC.endpointRawOfEffectiveFTC h).Equiv
        (endpointDifferenceRaw primitive a b hendpoint)) :
    DefiniteIdentity integrand primitive a b where
  construction := c
  endpoint_valid := hendpoint
  equivalent :=
    FTC.effectiveFTC_definiteIntegralEqualsEndpoint
      h c hendpoint hplan hscheduledEndpoint hendpoint_equiv

def definiteIdentity_of_staticDyadicEffectiveFTC
    {primitive integrand : RealFunRaw} {a b : Rat}
    (h : StaticDyadicEffectiveFTC primitive integrand a b)
    (c : Integral.Construction integrand a b)
    (hendpoint :
      RealRaw.ValidCompute (endpointDifferenceCompute primitive a b))
    (hplan : c.plan = FTC.integralPlanOfStaticDyadicEffectiveFTC h)
    (hscheduledEndpoint : (FTC.endpointRawOfEffectiveFTC h.toEffectiveFTC).Valid)
    (hendpoint_equiv :
      (FTC.endpointRawOfEffectiveFTC h.toEffectiveFTC).Equiv
        (endpointDifferenceRaw primitive a b hendpoint)) :
    DefiniteIdentity integrand primitive a b where
  construction := c
  endpoint_valid := hendpoint
  equivalent :=
    FTC.staticDyadicEffectiveFTC_definiteIntegralEqualsEndpoint
      h c hendpoint hplan hscheduledEndpoint hendpoint_equiv

def definiteIdentity_of_effectiveFTC_endpointAgreement
    {primitive integrand : RealFunRaw} {a b : Rat}
    (h : EffectiveFTC primitive integrand a b)
    (c : Integral.Construction integrand a b)
    (hplan : c.plan = FTC.integralPlanOfEffectiveFTC h)
    (endpoint :
      FTC.EndpointScheduleAgreement primitive a b
        (FTC.endpointRawOfEffectiveFTC h)) :
    DefiniteIdentity integrand primitive a b where
  construction := c
  endpoint_valid := endpoint.endpoint_valid
  equivalent :=
    FTC.effectiveFTC_definiteIntegralEqualsEndpoint_of_endpointAgreement
      h c hplan endpoint

def definiteIdentity_of_staticDyadicEffectiveFTC_endpointAgreement
    {primitive integrand : RealFunRaw} {a b : Rat}
    (h : StaticDyadicEffectiveFTC primitive integrand a b)
    (c : Integral.Construction integrand a b)
    (hplan : c.plan = FTC.integralPlanOfStaticDyadicEffectiveFTC h)
    (endpoint :
      FTC.EndpointScheduleAgreement primitive a b
        (FTC.endpointRawOfEffectiveFTC h.toEffectiveFTC)) :
    DefiniteIdentity integrand primitive a b where
  construction := c
  endpoint_valid := endpoint.endpoint_valid
  equivalent :=
    FTC.staticDyadicEffectiveFTC_definiteIntegralEqualsEndpoint_of_endpointAgreement
      h c hplan endpoint

/-- Package the scheduled Riemann algorithm from an `EffectiveFTC` certificate
as a domain-aware integral construction. -/
def constructionFor_of_effectiveFTC
    {integrand primitive : FunctionOnInterval}
    (h : EffectiveFTC primitive.toRealFunRaw integrand.toRealFunRaw
      integrand.lower integrand.upper)
    (hvalid : (FTC.riemannRawOfEffectiveFTC h).Valid) :
    Integral.ConstructionFor integrand where
  compute := FTC.riemannComputeOfEffectiveFTC h
  certificate := by
    simpa [RealRaw.Valid, FTC.riemannRawOfEffectiveFTC] using hvalid

theorem integralFor_effectiveFTC_compute_eq
    {integrand primitive : FunctionOnInterval}
    (h : EffectiveFTC primitive.toRealFunRaw integrand.toRealFunRaw
      integrand.lower integrand.upper)
    (hvalid : (FTC.riemannRawOfEffectiveFTC h).Valid) :
    (Integral.integralFor integrand
      (constructionFor_of_effectiveFTC h hvalid)).compute =
        FTC.riemannComputeOfEffectiveFTC h := rfl

/-- Turn an `EffectiveFTC` certificate into the domain-aware definite-integral
identity interface.

As in the derivative-bound route, validity of the scheduled Riemann and
endpoint algorithms is kept explicit.  The `EffectiveFTC` certificate supplies
the same-stage overlap; the endpoint-equivalence hypothesis identifies the
scheduled endpoint algorithm with the canonical endpoint-difference raw real. -/
def definiteIdentityFor_of_effectiveFTC
    {integrand primitive : FunctionOnInterval}
    (same_lower : primitive.lower = integrand.lower)
    (same_upper : primitive.upper = integrand.upper)
    (h : EffectiveFTC primitive.toRealFunRaw integrand.toRealFunRaw
      integrand.lower integrand.upper)
    (hriemann : (FTC.riemannRawOfEffectiveFTC h).Valid)
    (hscheduledEndpoint : (FTC.endpointRawOfEffectiveFTC h).Valid)
    (hendpoint :
      RealRaw.ValidCompute
        (endpointDifferenceCompute
          primitive.toRealFunRaw integrand.lower integrand.upper))
    (hendpoint_equiv :
      (FTC.endpointRawOfEffectiveFTC h).Equiv
        (endpointDifferenceRaw
          primitive.toRealFunRaw integrand.lower integrand.upper hendpoint)) :
    DefiniteIdentityFor integrand primitive where
  same_lower := same_lower
  same_upper := same_upper
  construction := constructionFor_of_effectiveFTC h hriemann
  endpoint_valid := hendpoint
  equivalent := by
    have hbridge :
        (Integral.integralFor integrand
          (constructionFor_of_effectiveFTC h hriemann)).Equiv
            (FTC.endpointRawOfEffectiveFTC h) := by
      simpa [Integral.integralFor, constructionFor_of_effectiveFTC,
        FTC.riemannRawOfEffectiveFTC] using
        FTC.effectiveFTC_equiv_endpoint h
    exact RealRaw.equiv_trans
      (Integral.integralFor_valid integrand
        (constructionFor_of_effectiveFTC h hriemann))
      hscheduledEndpoint
      hendpoint
      hbridge
      hendpoint_equiv

/-- Static-dyadic specialization of
`constructionFor_of_effectiveFTC`. -/
def constructionFor_of_staticDyadicEffectiveFTC
    {integrand primitive : FunctionOnInterval}
    (h : StaticDyadicEffectiveFTC primitive.toRealFunRaw integrand.toRealFunRaw
      integrand.lower integrand.upper)
    (hvalid : (FTC.riemannRawOfEffectiveFTC h.toEffectiveFTC).Valid) :
    Integral.ConstructionFor integrand :=
  constructionFor_of_effectiveFTC h.toEffectiveFTC hvalid

theorem integralFor_staticDyadicEffectiveFTC_compute_eq
    {integrand primitive : FunctionOnInterval}
    (h : StaticDyadicEffectiveFTC primitive.toRealFunRaw integrand.toRealFunRaw
      integrand.lower integrand.upper)
    (hvalid : (FTC.riemannRawOfEffectiveFTC h.toEffectiveFTC).Valid) :
    (Integral.integralFor integrand
      (constructionFor_of_staticDyadicEffectiveFTC h hvalid)).compute =
        FTC.riemannComputeOfEffectiveFTC h.toEffectiveFTC := rfl

/-- Domain-aware definite-integral identity produced by a static-dyadic
`EffectiveFTC` certificate. -/
def definiteIdentityFor_of_staticDyadicEffectiveFTC
    {integrand primitive : FunctionOnInterval}
    (same_lower : primitive.lower = integrand.lower)
    (same_upper : primitive.upper = integrand.upper)
    (h : StaticDyadicEffectiveFTC primitive.toRealFunRaw integrand.toRealFunRaw
      integrand.lower integrand.upper)
    (hriemann : (FTC.riemannRawOfEffectiveFTC h.toEffectiveFTC).Valid)
    (hscheduledEndpoint : (FTC.endpointRawOfEffectiveFTC h.toEffectiveFTC).Valid)
    (hendpoint :
      RealRaw.ValidCompute
        (endpointDifferenceCompute
          primitive.toRealFunRaw integrand.lower integrand.upper))
    (hendpoint_equiv :
      (FTC.endpointRawOfEffectiveFTC h.toEffectiveFTC).Equiv
        (endpointDifferenceRaw
          primitive.toRealFunRaw integrand.lower integrand.upper hendpoint)) :
    DefiniteIdentityFor integrand primitive :=
  definiteIdentityFor_of_effectiveFTC
    same_lower same_upper h.toEffectiveFTC
    hriemann hscheduledEndpoint hendpoint hendpoint_equiv

def definiteIdentityFor_of_effectiveFTC_endpointAgreement
    {integrand primitive : FunctionOnInterval}
    (same_lower : primitive.lower = integrand.lower)
    (same_upper : primitive.upper = integrand.upper)
    (h : EffectiveFTC primitive.toRealFunRaw integrand.toRealFunRaw
      integrand.lower integrand.upper)
    (hriemann : (FTC.riemannRawOfEffectiveFTC h).Valid)
    (endpoint :
      FTC.EndpointScheduleAgreement primitive.toRealFunRaw
        integrand.lower integrand.upper
        (FTC.endpointRawOfEffectiveFTC h)) :
    DefiniteIdentityFor integrand primitive :=
  definiteIdentityFor_of_effectiveFTC
    same_lower same_upper h hriemann
    endpoint.scheduled_valid endpoint.endpoint_valid endpoint.equivalent

def definiteIdentityFor_of_effectiveFTC_stageSchedule
    {integrand primitive : FunctionOnInterval}
    (same_lower : primitive.lower = integrand.lower)
    (same_upper : primitive.upper = integrand.upper)
    (h : EffectiveFTC primitive.toRealFunRaw integrand.toRealFunRaw
      integrand.lower integrand.upper)
    (hriemann : (FTC.riemannRawOfEffectiveFTC h).Valid)
    (hendpoint :
      RealRaw.ValidCompute
        (endpointDifferenceCompute
          primitive.toRealFunRaw integrand.lower integrand.upper))
    (sigma : RealRaw.StageSchedule)
    (hsigma :
      forall n, h.chooseEvalPrecision (FTC.requestedPrecision n) =
        sigma.stage n) :
    DefiniteIdentityFor integrand primitive :=
  definiteIdentityFor_of_effectiveFTC_endpointAgreement
    same_lower same_upper h hriemann
    (FTC.endpointScheduleAgreement_of_effectiveFTC_stageSchedule
      h hendpoint sigma hsigma)

def definiteIdentityFor_of_staticDyadicEffectiveFTC_endpointAgreement
    {integrand primitive : FunctionOnInterval}
    (same_lower : primitive.lower = integrand.lower)
    (same_upper : primitive.upper = integrand.upper)
    (h : StaticDyadicEffectiveFTC primitive.toRealFunRaw integrand.toRealFunRaw
      integrand.lower integrand.upper)
    (hriemann : (FTC.riemannRawOfEffectiveFTC h.toEffectiveFTC).Valid)
    (endpoint :
      FTC.EndpointScheduleAgreement primitive.toRealFunRaw
        integrand.lower integrand.upper
        (FTC.endpointRawOfEffectiveFTC h.toEffectiveFTC)) :
    DefiniteIdentityFor integrand primitive :=
  definiteIdentityFor_of_staticDyadicEffectiveFTC
    same_lower same_upper h hriemann
    endpoint.scheduled_valid endpoint.endpoint_valid endpoint.equivalent

def definiteIdentityFor_of_staticDyadicEffectiveFTC_stageSchedule
    {integrand primitive : FunctionOnInterval}
    (same_lower : primitive.lower = integrand.lower)
    (same_upper : primitive.upper = integrand.upper)
    (h : StaticDyadicEffectiveFTC primitive.toRealFunRaw integrand.toRealFunRaw
      integrand.lower integrand.upper)
    (hriemann : (FTC.riemannRawOfEffectiveFTC h.toEffectiveFTC).Valid)
    (hendpoint :
      RealRaw.ValidCompute
        (endpointDifferenceCompute
          primitive.toRealFunRaw integrand.lower integrand.upper))
    (sigma : RealRaw.StageSchedule)
    (hsigma :
      forall n, h.chooseEvalPrecision (FTC.requestedPrecision n) =
        sigma.stage n) :
    DefiniteIdentityFor integrand primitive :=
  definiteIdentityFor_of_staticDyadicEffectiveFTC_endpointAgreement
    same_lower same_upper h hriemann
    (FTC.endpointScheduleAgreement_of_staticDyadicEffectiveFTC_stageSchedule
      h hendpoint sigma hsigma)

/-- Package a derivative-bound FTC cell-sum algorithm as a domain-aware
integral construction.

The derivative-bound certificate supplies the comparison with endpoint
differences.  The validity of the bounded-sum raw algorithm is kept as an
explicit hypothesis because validity in this project includes nestedness and
shrinking, not just same-stage overlap. -/
def constructionFor_of_derivativeBoundFTC
    {integrand primitive : FunctionOnInterval}
    (h : DerivativeBoundFTC primitive.toRealFunRaw integrand.toRealFunRaw
      integrand.lower integrand.upper)
    (hvalid : h.boundedIntegralRaw.Valid) :
    Integral.ConstructionFor integrand where
  compute := h.boundedIntegralCompute
  certificate := by
    simpa [RealRaw.Valid, DerivativeBoundFTC.boundedIntegralRaw] using hvalid

theorem integralFor_derivativeBoundFTC_compute_eq
    {integrand primitive : FunctionOnInterval}
    (h : DerivativeBoundFTC primitive.toRealFunRaw integrand.toRealFunRaw
      integrand.lower integrand.upper)
    (hvalid : h.boundedIntegralRaw.Valid) :
    (Integral.integralFor integrand
      (constructionFor_of_derivativeBoundFTC h hvalid)).compute =
        h.boundedIntegralCompute := rfl

/-- Turn a derivative-bound FTC certificate into the domain-aware definite
integral identity interface.

Two representation obligations remain explicit: the derivative-bound integral
algorithm must be a valid `RealRaw`, and the scheduled endpoint algorithm must
be equivalent to the canonical endpoint-difference algorithm.  Those are
formula-specific bookkeeping facts, while the FTC overlap itself is supplied
by `DerivativeBoundFTC.equiv_endpoint`. -/
def definiteIdentityFor_of_derivativeBoundFTC
    {integrand primitive : FunctionOnInterval}
    (same_lower : primitive.lower = integrand.lower)
    (same_upper : primitive.upper = integrand.upper)
    (h : DerivativeBoundFTC primitive.toRealFunRaw integrand.toRealFunRaw
      integrand.lower integrand.upper)
    (hbounded : h.boundedIntegralRaw.Valid)
    (hscheduledEndpoint : h.endpointRaw.Valid)
    (hendpoint :
      RealRaw.ValidCompute
        (endpointDifferenceCompute
          primitive.toRealFunRaw integrand.lower integrand.upper))
    (hendpoint_equiv :
      h.endpointRaw.Equiv
        (endpointDifferenceRaw
          primitive.toRealFunRaw integrand.lower integrand.upper hendpoint)) :
    DefiniteIdentityFor integrand primitive where
  same_lower := same_lower
  same_upper := same_upper
  construction := constructionFor_of_derivativeBoundFTC h hbounded
  endpoint_valid := hendpoint
  equivalent := by
    have hbridge :
        (Integral.integralFor integrand
          (constructionFor_of_derivativeBoundFTC h hbounded)).Equiv
            h.endpointRaw := by
      simpa [Integral.integralFor, constructionFor_of_derivativeBoundFTC,
        DerivativeBoundFTC.boundedIntegralRaw] using h.equiv_endpoint
    exact RealRaw.equiv_trans
      (Integral.integralFor_valid integrand
        (constructionFor_of_derivativeBoundFTC h hbounded))
      hscheduledEndpoint
      hendpoint
      hbridge
      hendpoint_equiv

def definiteIdentityFor_of_derivativeBoundFTC_endpointAgreement
    {integrand primitive : FunctionOnInterval}
    (same_lower : primitive.lower = integrand.lower)
    (same_upper : primitive.upper = integrand.upper)
    (h : DerivativeBoundFTC primitive.toRealFunRaw integrand.toRealFunRaw
      integrand.lower integrand.upper)
    (hbounded : h.boundedIntegralRaw.Valid)
    (endpoint :
      FTC.EndpointScheduleAgreement primitive.toRealFunRaw
        integrand.lower integrand.upper h.endpointRaw) :
    DefiniteIdentityFor integrand primitive :=
  definiteIdentityFor_of_derivativeBoundFTC
    same_lower same_upper h hbounded
    endpoint.scheduled_valid endpoint.endpoint_valid endpoint.equivalent

def definiteIdentityFor_of_derivativeBoundFTC_stageSchedule
    {integrand primitive : FunctionOnInterval}
    (same_lower : primitive.lower = integrand.lower)
    (same_upper : primitive.upper = integrand.upper)
    (h : DerivativeBoundFTC primitive.toRealFunRaw integrand.toRealFunRaw
      integrand.lower integrand.upper)
    (hbounded : h.boundedIntegralRaw.Valid)
    (hendpoint :
      RealRaw.ValidCompute
        (endpointDifferenceCompute
          primitive.toRealFunRaw integrand.lower integrand.upper))
    (sigma : RealRaw.StageSchedule)
    (hsigma :
      forall n, h.chooseEndpointPrecision (precisionAtStage n) =
        sigma.stage n) :
    DefiniteIdentityFor integrand primitive :=
  definiteIdentityFor_of_derivativeBoundFTC_endpointAgreement
    same_lower same_upper h hbounded
    (FTC.endpointScheduleAgreement_of_derivativeBoundFTC_stageSchedule
      h hendpoint sigma hsigma)

/-- Candidate-derivative specialization of
`constructionFor_of_derivativeBoundFTC`. -/
def constructionFor_of_candidateDerivativeFTC
    {integrand primitive : FunctionOnInterval}
    (h : CandidateDerivativeFTC primitive.toRealFunRaw integrand.toRealFunRaw
      integrand.lower integrand.upper)
    (hvalid : h.toDerivativeBoundFTC.boundedIntegralRaw.Valid) :
    Integral.ConstructionFor integrand :=
  constructionFor_of_derivativeBoundFTC h.toDerivativeBoundFTC hvalid

theorem integralFor_candidateDerivativeFTC_compute_eq
    {integrand primitive : FunctionOnInterval}
    (h : CandidateDerivativeFTC primitive.toRealFunRaw integrand.toRealFunRaw
      integrand.lower integrand.upper)
    (hvalid : h.toDerivativeBoundFTC.boundedIntegralRaw.Valid) :
    (Integral.integralFor integrand
      (constructionFor_of_candidateDerivativeFTC h hvalid)).compute =
        h.toDerivativeBoundFTC.boundedIntegralCompute := rfl

/-- Turn a candidate-derivative FTC certificate into the domain-aware
definite-integral identity interface. -/
def definiteIdentityFor_of_candidateDerivativeFTC
    {integrand primitive : FunctionOnInterval}
    (same_lower : primitive.lower = integrand.lower)
    (same_upper : primitive.upper = integrand.upper)
    (h : CandidateDerivativeFTC primitive.toRealFunRaw integrand.toRealFunRaw
      integrand.lower integrand.upper)
    (hbounded : h.toDerivativeBoundFTC.boundedIntegralRaw.Valid)
    (hscheduledEndpoint : h.toDerivativeBoundFTC.endpointRaw.Valid)
    (hendpoint :
      RealRaw.ValidCompute
        (endpointDifferenceCompute
          primitive.toRealFunRaw integrand.lower integrand.upper))
    (hendpoint_equiv :
      h.toDerivativeBoundFTC.endpointRaw.Equiv
        (endpointDifferenceRaw
          primitive.toRealFunRaw integrand.lower integrand.upper hendpoint)) :
    DefiniteIdentityFor integrand primitive :=
  definiteIdentityFor_of_derivativeBoundFTC
    same_lower same_upper h.toDerivativeBoundFTC
    hbounded hscheduledEndpoint hendpoint hendpoint_equiv

def definiteIdentityFor_of_candidateDerivativeFTC_endpointAgreement
    {integrand primitive : FunctionOnInterval}
    (same_lower : primitive.lower = integrand.lower)
    (same_upper : primitive.upper = integrand.upper)
    (h : CandidateDerivativeFTC primitive.toRealFunRaw integrand.toRealFunRaw
      integrand.lower integrand.upper)
    (hbounded : h.toDerivativeBoundFTC.boundedIntegralRaw.Valid)
    (endpoint :
      FTC.EndpointScheduleAgreement primitive.toRealFunRaw
        integrand.lower integrand.upper
        h.toDerivativeBoundFTC.endpointRaw) :
    DefiniteIdentityFor integrand primitive :=
  definiteIdentityFor_of_candidateDerivativeFTC
    same_lower same_upper h hbounded
    endpoint.scheduled_valid endpoint.endpoint_valid endpoint.equivalent

def definiteIdentityFor_of_candidateDerivativeFTC_stageSchedule
    {integrand primitive : FunctionOnInterval}
    (same_lower : primitive.lower = integrand.lower)
    (same_upper : primitive.upper = integrand.upper)
    (h : CandidateDerivativeFTC primitive.toRealFunRaw integrand.toRealFunRaw
      integrand.lower integrand.upper)
    (hbounded : h.toDerivativeBoundFTC.boundedIntegralRaw.Valid)
    (hendpoint :
      RealRaw.ValidCompute
        (endpointDifferenceCompute
          primitive.toRealFunRaw integrand.lower integrand.upper))
    (sigma : RealRaw.StageSchedule)
    (hsigma :
      forall n,
        h.toDerivativeBoundFTC.chooseEndpointPrecision
            (precisionAtStage n) =
          sigma.stage n) :
    DefiniteIdentityFor integrand primitive :=
  definiteIdentityFor_of_candidateDerivativeFTC_endpointAgreement
    same_lower same_upper h hbounded
    (FTC.endpointScheduleAgreement_of_candidateDerivativeFTC_stageSchedule
      h hendpoint sigma hsigma)

/-- Convexity-facing specialization of
`definiteIdentityFor_of_derivativeBoundFTC`.

The public convex FTC certificate first turns into a derivative-bound FTC
certificate, then uses the same domain-aware endpoint-identity bridge. -/
def constructionFor_of_curvatureFTC
    {integrand primitive : FunctionOnInterval}
    (h : CurvatureFTCCertificate primitive.toRealFunRaw integrand.toRealFunRaw
      integrand.lower integrand.upper)
    (hvalid : h.toDerivativeBoundFTC.boundedIntegralRaw.Valid) :
    Integral.ConstructionFor integrand :=
  constructionFor_of_derivativeBoundFTC h.toDerivativeBoundFTC hvalid

theorem integralFor_curvatureFTC_compute_eq
    {integrand primitive : FunctionOnInterval}
    (h : CurvatureFTCCertificate primitive.toRealFunRaw integrand.toRealFunRaw
      integrand.lower integrand.upper)
    (hvalid : h.toDerivativeBoundFTC.boundedIntegralRaw.Valid) :
    (Integral.integralFor integrand
      (constructionFor_of_curvatureFTC h hvalid)).compute =
        h.toDerivativeBoundFTC.boundedIntegralCompute := rfl

/-- Turn a curvature FTC certificate into the domain-aware definite-integral
identity interface.  This covers both convex and concave curvature data. -/
def definiteIdentityFor_of_curvatureFTC
    {integrand primitive : FunctionOnInterval}
    (same_lower : primitive.lower = integrand.lower)
    (same_upper : primitive.upper = integrand.upper)
    (h : CurvatureFTCCertificate primitive.toRealFunRaw integrand.toRealFunRaw
      integrand.lower integrand.upper)
    (hbounded : h.toDerivativeBoundFTC.boundedIntegralRaw.Valid)
    (hscheduledEndpoint : h.toDerivativeBoundFTC.endpointRaw.Valid)
    (hendpoint :
      RealRaw.ValidCompute
        (endpointDifferenceCompute
          primitive.toRealFunRaw integrand.lower integrand.upper))
    (hendpoint_equiv :
      h.toDerivativeBoundFTC.endpointRaw.Equiv
        (endpointDifferenceRaw
          primitive.toRealFunRaw integrand.lower integrand.upper hendpoint)) :
    DefiniteIdentityFor integrand primitive :=
  definiteIdentityFor_of_derivativeBoundFTC
    same_lower same_upper h.toDerivativeBoundFTC
    hbounded hscheduledEndpoint hendpoint hendpoint_equiv

def definiteIdentityFor_of_curvatureFTC_endpointAgreement
    {integrand primitive : FunctionOnInterval}
    (same_lower : primitive.lower = integrand.lower)
    (same_upper : primitive.upper = integrand.upper)
    (h : CurvatureFTCCertificate primitive.toRealFunRaw integrand.toRealFunRaw
      integrand.lower integrand.upper)
    (hbounded : h.toDerivativeBoundFTC.boundedIntegralRaw.Valid)
    (endpoint :
      FTC.EndpointScheduleAgreement primitive.toRealFunRaw
        integrand.lower integrand.upper
        h.toDerivativeBoundFTC.endpointRaw) :
    DefiniteIdentityFor integrand primitive :=
  definiteIdentityFor_of_curvatureFTC
    same_lower same_upper h hbounded
    endpoint.scheduled_valid endpoint.endpoint_valid endpoint.equivalent

def definiteIdentityFor_of_curvatureFTC_stageSchedule
    {integrand primitive : FunctionOnInterval}
    (same_lower : primitive.lower = integrand.lower)
    (same_upper : primitive.upper = integrand.upper)
    (h : CurvatureFTCCertificate primitive.toRealFunRaw integrand.toRealFunRaw
      integrand.lower integrand.upper)
    (hbounded : h.toDerivativeBoundFTC.boundedIntegralRaw.Valid)
    (hendpoint :
      RealRaw.ValidCompute
        (endpointDifferenceCompute
          primitive.toRealFunRaw integrand.lower integrand.upper))
    (sigma : RealRaw.StageSchedule)
    (hsigma :
      forall n,
        h.toDerivativeBoundFTC.chooseEndpointPrecision
            (precisionAtStage n) =
          sigma.stage n) :
    DefiniteIdentityFor integrand primitive :=
  definiteIdentityFor_of_curvatureFTC_endpointAgreement
    same_lower same_upper h hbounded
    (FTC.endpointScheduleAgreement_of_curvatureFTC_stageSchedule
      h hendpoint sigma hsigma)

def constructionFor_of_convexFTC
    {integrand primitive : FunctionOnInterval}
    (h : ConvexFTCCertificate primitive.toRealFunRaw integrand.toRealFunRaw
      integrand.lower integrand.upper)
    (hvalid : h.toDerivativeBoundFTC.boundedIntegralRaw.Valid) :
    Integral.ConstructionFor integrand :=
  constructionFor_of_curvatureFTC h.toCurvatureFTCCertificate hvalid

theorem integralFor_convexFTC_compute_eq
    {integrand primitive : FunctionOnInterval}
    (h : ConvexFTCCertificate primitive.toRealFunRaw integrand.toRealFunRaw
      integrand.lower integrand.upper)
    (hvalid : h.toDerivativeBoundFTC.boundedIntegralRaw.Valid) :
    (Integral.integralFor integrand
      (constructionFor_of_convexFTC h hvalid)).compute =
        h.toDerivativeBoundFTC.boundedIntegralCompute := rfl

def definiteIdentityFor_of_convexFTC
    {integrand primitive : FunctionOnInterval}
    (same_lower : primitive.lower = integrand.lower)
    (same_upper : primitive.upper = integrand.upper)
    (h : ConvexFTCCertificate primitive.toRealFunRaw integrand.toRealFunRaw
      integrand.lower integrand.upper)
    (hbounded : h.toDerivativeBoundFTC.boundedIntegralRaw.Valid)
    (hscheduledEndpoint : h.toDerivativeBoundFTC.endpointRaw.Valid)
    (hendpoint :
      RealRaw.ValidCompute
        (endpointDifferenceCompute
          primitive.toRealFunRaw integrand.lower integrand.upper))
    (hendpoint_equiv :
      h.toDerivativeBoundFTC.endpointRaw.Equiv
        (endpointDifferenceRaw
          primitive.toRealFunRaw integrand.lower integrand.upper hendpoint)) :
    DefiniteIdentityFor integrand primitive :=
  definiteIdentityFor_of_curvatureFTC
    same_lower same_upper h.toCurvatureFTCCertificate
    hbounded hscheduledEndpoint hendpoint hendpoint_equiv

def definiteIdentityFor_of_convexFTC_endpointAgreement
    {integrand primitive : FunctionOnInterval}
    (same_lower : primitive.lower = integrand.lower)
    (same_upper : primitive.upper = integrand.upper)
    (h : ConvexFTCCertificate primitive.toRealFunRaw integrand.toRealFunRaw
      integrand.lower integrand.upper)
    (hbounded : h.toDerivativeBoundFTC.boundedIntegralRaw.Valid)
    (endpoint :
      FTC.EndpointScheduleAgreement primitive.toRealFunRaw
        integrand.lower integrand.upper
        h.toDerivativeBoundFTC.endpointRaw) :
    DefiniteIdentityFor integrand primitive :=
  definiteIdentityFor_of_convexFTC
    same_lower same_upper h hbounded
    endpoint.scheduled_valid endpoint.endpoint_valid endpoint.equivalent

def definiteIdentityFor_of_convexFTC_stageSchedule
    {integrand primitive : FunctionOnInterval}
    (same_lower : primitive.lower = integrand.lower)
    (same_upper : primitive.upper = integrand.upper)
    (h : ConvexFTCCertificate primitive.toRealFunRaw integrand.toRealFunRaw
      integrand.lower integrand.upper)
    (hbounded : h.toDerivativeBoundFTC.boundedIntegralRaw.Valid)
    (hendpoint :
      RealRaw.ValidCompute
        (endpointDifferenceCompute
          primitive.toRealFunRaw integrand.lower integrand.upper))
    (sigma : RealRaw.StageSchedule)
    (hsigma :
      forall n,
        h.toDerivativeBoundFTC.chooseEndpointPrecision
            (precisionAtStage n) =
          sigma.stage n) :
    DefiniteIdentityFor integrand primitive :=
  definiteIdentityFor_of_convexFTC_endpointAgreement
    same_lower same_upper h hbounded
    (FTC.endpointScheduleAgreement_of_convexFTC_stageSchedule
      h hendpoint sigma hsigma)

def constructionFor_of_concaveFTC
    {integrand primitive : FunctionOnInterval}
    (h : ConcaveFTCCertificate primitive.toRealFunRaw integrand.toRealFunRaw
      integrand.lower integrand.upper)
    (hvalid : h.toDerivativeBoundFTC.boundedIntegralRaw.Valid) :
    Integral.ConstructionFor integrand :=
  constructionFor_of_curvatureFTC h.toCurvatureFTCCertificate hvalid

theorem integralFor_concaveFTC_compute_eq
    {integrand primitive : FunctionOnInterval}
    (h : ConcaveFTCCertificate primitive.toRealFunRaw integrand.toRealFunRaw
      integrand.lower integrand.upper)
    (hvalid : h.toDerivativeBoundFTC.boundedIntegralRaw.Valid) :
    (Integral.integralFor integrand
      (constructionFor_of_concaveFTC h hvalid)).compute =
        h.toDerivativeBoundFTC.boundedIntegralCompute := rfl

def definiteIdentityFor_of_concaveFTC
    {integrand primitive : FunctionOnInterval}
    (same_lower : primitive.lower = integrand.lower)
    (same_upper : primitive.upper = integrand.upper)
    (h : ConcaveFTCCertificate primitive.toRealFunRaw integrand.toRealFunRaw
      integrand.lower integrand.upper)
    (hbounded : h.toDerivativeBoundFTC.boundedIntegralRaw.Valid)
    (hscheduledEndpoint : h.toDerivativeBoundFTC.endpointRaw.Valid)
    (hendpoint :
      RealRaw.ValidCompute
        (endpointDifferenceCompute
          primitive.toRealFunRaw integrand.lower integrand.upper))
    (hendpoint_equiv :
      h.toDerivativeBoundFTC.endpointRaw.Equiv
        (endpointDifferenceRaw
          primitive.toRealFunRaw integrand.lower integrand.upper hendpoint)) :
    DefiniteIdentityFor integrand primitive :=
  definiteIdentityFor_of_curvatureFTC
    same_lower same_upper h.toCurvatureFTCCertificate
    hbounded hscheduledEndpoint hendpoint hendpoint_equiv

def definiteIdentityFor_of_concaveFTC_endpointAgreement
    {integrand primitive : FunctionOnInterval}
    (same_lower : primitive.lower = integrand.lower)
    (same_upper : primitive.upper = integrand.upper)
    (h : ConcaveFTCCertificate primitive.toRealFunRaw integrand.toRealFunRaw
      integrand.lower integrand.upper)
    (hbounded : h.toDerivativeBoundFTC.boundedIntegralRaw.Valid)
    (endpoint :
      FTC.EndpointScheduleAgreement primitive.toRealFunRaw
        integrand.lower integrand.upper
        h.toDerivativeBoundFTC.endpointRaw) :
    DefiniteIdentityFor integrand primitive :=
  definiteIdentityFor_of_concaveFTC
    same_lower same_upper h hbounded
    endpoint.scheduled_valid endpoint.endpoint_valid endpoint.equivalent

def definiteIdentityFor_of_concaveFTC_stageSchedule
    {integrand primitive : FunctionOnInterval}
    (same_lower : primitive.lower = integrand.lower)
    (same_upper : primitive.upper = integrand.upper)
    (h : ConcaveFTCCertificate primitive.toRealFunRaw integrand.toRealFunRaw
      integrand.lower integrand.upper)
    (hbounded : h.toDerivativeBoundFTC.boundedIntegralRaw.Valid)
    (hendpoint :
      RealRaw.ValidCompute
        (endpointDifferenceCompute
          primitive.toRealFunRaw integrand.lower integrand.upper))
    (sigma : RealRaw.StageSchedule)
    (hsigma :
      forall n,
        h.toDerivativeBoundFTC.chooseEndpointPrecision
            (precisionAtStage n) =
          sigma.stage n) :
    DefiniteIdentityFor integrand primitive :=
  definiteIdentityFor_of_concaveFTC_endpointAgreement
    same_lower same_upper h hbounded
    (FTC.endpointScheduleAgreement_of_concaveFTC_stageSchedule
      h hendpoint sigma hsigma)

def generalDefiniteIdentityFor_of_effectiveFTC_stageSchedule
    {integrand primitive : FunctionOnInterval}
    (same_lower : primitive.lower = integrand.lower)
    (same_upper : primitive.upper = integrand.upper)
    (h : EffectiveFTC primitive.toRealFunRaw integrand.toRealFunRaw
      integrand.lower integrand.upper)
    (hriemann : (FTC.riemannRawOfEffectiveFTC h).Valid)
    (hendpoint :
      RealRaw.ValidCompute
        (endpointDifferenceCompute
          primitive.toRealFunRaw integrand.lower integrand.upper))
    (sigma : RealRaw.StageSchedule)
    (hsigma :
      forall n, h.chooseEvalPrecision (FTC.requestedPrecision n) =
        sigma.stage n)
    (construction : Integral.GeneralConstructionFor integrand)
    (hconstruction :
      (Integral.generalIntegralFor integrand construction).Equiv
        (Integral.integralFor integrand
          (constructionFor_of_effectiveFTC h hriemann))) :
    GeneralDefiniteIdentityFor integrand primitive :=
  GeneralDefiniteIdentityFor.ofDefiniteIdentityFor
    (definiteIdentityFor_of_effectiveFTC_stageSchedule
      same_lower same_upper h hriemann hendpoint sigma hsigma)
    construction hconstruction

def generalDefiniteIdentityFor_of_staticDyadicEffectiveFTC_stageSchedule
    {integrand primitive : FunctionOnInterval}
    (same_lower : primitive.lower = integrand.lower)
    (same_upper : primitive.upper = integrand.upper)
    (h : StaticDyadicEffectiveFTC primitive.toRealFunRaw integrand.toRealFunRaw
      integrand.lower integrand.upper)
    (hriemann : (FTC.riemannRawOfEffectiveFTC h.toEffectiveFTC).Valid)
    (hendpoint :
      RealRaw.ValidCompute
        (endpointDifferenceCompute
          primitive.toRealFunRaw integrand.lower integrand.upper))
    (sigma : RealRaw.StageSchedule)
    (hsigma :
      forall n, h.chooseEvalPrecision (FTC.requestedPrecision n) =
        sigma.stage n)
    (construction : Integral.GeneralConstructionFor integrand)
    (hconstruction :
      (Integral.generalIntegralFor integrand construction).Equiv
        (Integral.integralFor integrand
          (constructionFor_of_staticDyadicEffectiveFTC h hriemann))) :
    GeneralDefiniteIdentityFor integrand primitive :=
  GeneralDefiniteIdentityFor.ofDefiniteIdentityFor
    (definiteIdentityFor_of_staticDyadicEffectiveFTC_stageSchedule
      same_lower same_upper h hriemann hendpoint sigma hsigma)
    construction hconstruction

def generalDefiniteIdentityFor_of_derivativeBoundFTC_stageSchedule
    {integrand primitive : FunctionOnInterval}
    (same_lower : primitive.lower = integrand.lower)
    (same_upper : primitive.upper = integrand.upper)
    (h : DerivativeBoundFTC primitive.toRealFunRaw integrand.toRealFunRaw
      integrand.lower integrand.upper)
    (hbounded : h.boundedIntegralRaw.Valid)
    (hendpoint :
      RealRaw.ValidCompute
        (endpointDifferenceCompute
          primitive.toRealFunRaw integrand.lower integrand.upper))
    (sigma : RealRaw.StageSchedule)
    (hsigma :
      forall n, h.chooseEndpointPrecision (precisionAtStage n) =
        sigma.stage n)
    (construction : Integral.GeneralConstructionFor integrand)
    (hconstruction :
      (Integral.generalIntegralFor integrand construction).Equiv
        (Integral.integralFor integrand
          (constructionFor_of_derivativeBoundFTC h hbounded))) :
    GeneralDefiniteIdentityFor integrand primitive :=
  GeneralDefiniteIdentityFor.ofDefiniteIdentityFor
    (definiteIdentityFor_of_derivativeBoundFTC_stageSchedule
      same_lower same_upper h hbounded hendpoint sigma hsigma)
    construction hconstruction

def generalDefiniteIdentityFor_of_candidateDerivativeFTC_stageSchedule
    {integrand primitive : FunctionOnInterval}
    (same_lower : primitive.lower = integrand.lower)
    (same_upper : primitive.upper = integrand.upper)
    (h : CandidateDerivativeFTC primitive.toRealFunRaw integrand.toRealFunRaw
      integrand.lower integrand.upper)
    (hbounded : h.toDerivativeBoundFTC.boundedIntegralRaw.Valid)
    (hendpoint :
      RealRaw.ValidCompute
        (endpointDifferenceCompute
          primitive.toRealFunRaw integrand.lower integrand.upper))
    (sigma : RealRaw.StageSchedule)
    (hsigma :
      forall n,
        h.toDerivativeBoundFTC.chooseEndpointPrecision
            (precisionAtStage n) =
          sigma.stage n)
    (construction : Integral.GeneralConstructionFor integrand)
    (hconstruction :
      (Integral.generalIntegralFor integrand construction).Equiv
        (Integral.integralFor integrand
          (constructionFor_of_candidateDerivativeFTC h hbounded))) :
    GeneralDefiniteIdentityFor integrand primitive :=
  GeneralDefiniteIdentityFor.ofDefiniteIdentityFor
    (definiteIdentityFor_of_candidateDerivativeFTC_stageSchedule
      same_lower same_upper h hbounded hendpoint sigma hsigma)
    construction hconstruction

def generalDefiniteIdentityFor_of_curvatureFTC_stageSchedule
    {integrand primitive : FunctionOnInterval}
    (same_lower : primitive.lower = integrand.lower)
    (same_upper : primitive.upper = integrand.upper)
    (h : CurvatureFTCCertificate primitive.toRealFunRaw integrand.toRealFunRaw
      integrand.lower integrand.upper)
    (hbounded : h.toDerivativeBoundFTC.boundedIntegralRaw.Valid)
    (hendpoint :
      RealRaw.ValidCompute
        (endpointDifferenceCompute
          primitive.toRealFunRaw integrand.lower integrand.upper))
    (sigma : RealRaw.StageSchedule)
    (hsigma :
      forall n,
        h.toDerivativeBoundFTC.chooseEndpointPrecision
            (precisionAtStage n) =
          sigma.stage n)
    (construction : Integral.GeneralConstructionFor integrand)
    (hconstruction :
      (Integral.generalIntegralFor integrand construction).Equiv
        (Integral.integralFor integrand
          (constructionFor_of_curvatureFTC h hbounded))) :
    GeneralDefiniteIdentityFor integrand primitive :=
  GeneralDefiniteIdentityFor.ofDefiniteIdentityFor
    (definiteIdentityFor_of_curvatureFTC_stageSchedule
      same_lower same_upper h hbounded hendpoint sigma hsigma)
    construction hconstruction

def generalDefiniteIdentityFor_of_convexFTC_stageSchedule
    {integrand primitive : FunctionOnInterval}
    (same_lower : primitive.lower = integrand.lower)
    (same_upper : primitive.upper = integrand.upper)
    (h : ConvexFTCCertificate primitive.toRealFunRaw integrand.toRealFunRaw
      integrand.lower integrand.upper)
    (hbounded : h.toDerivativeBoundFTC.boundedIntegralRaw.Valid)
    (hendpoint :
      RealRaw.ValidCompute
        (endpointDifferenceCompute
          primitive.toRealFunRaw integrand.lower integrand.upper))
    (sigma : RealRaw.StageSchedule)
    (hsigma :
      forall n,
        h.toDerivativeBoundFTC.chooseEndpointPrecision
            (precisionAtStage n) =
          sigma.stage n)
    (construction : Integral.GeneralConstructionFor integrand)
    (hconstruction :
      (Integral.generalIntegralFor integrand construction).Equiv
        (Integral.integralFor integrand
          (constructionFor_of_convexFTC h hbounded))) :
    GeneralDefiniteIdentityFor integrand primitive :=
  GeneralDefiniteIdentityFor.ofDefiniteIdentityFor
    (definiteIdentityFor_of_convexFTC_stageSchedule
      same_lower same_upper h hbounded hendpoint sigma hsigma)
    construction hconstruction

def generalDefiniteIdentityFor_of_concaveFTC_stageSchedule
    {integrand primitive : FunctionOnInterval}
    (same_lower : primitive.lower = integrand.lower)
    (same_upper : primitive.upper = integrand.upper)
    (h : ConcaveFTCCertificate primitive.toRealFunRaw integrand.toRealFunRaw
      integrand.lower integrand.upper)
    (hbounded : h.toDerivativeBoundFTC.boundedIntegralRaw.Valid)
    (hendpoint :
      RealRaw.ValidCompute
        (endpointDifferenceCompute
          primitive.toRealFunRaw integrand.lower integrand.upper))
    (sigma : RealRaw.StageSchedule)
    (hsigma :
      forall n,
        h.toDerivativeBoundFTC.chooseEndpointPrecision
            (precisionAtStage n) =
          sigma.stage n)
    (construction : Integral.GeneralConstructionFor integrand)
    (hconstruction :
      (Integral.generalIntegralFor integrand construction).Equiv
        (Integral.integralFor integrand
          (constructionFor_of_concaveFTC h hbounded))) :
    GeneralDefiniteIdentityFor integrand primitive :=
  GeneralDefiniteIdentityFor.ofDefiniteIdentityFor
    (definiteIdentityFor_of_concaveFTC_stageSchedule
      same_lower same_upper h hbounded hendpoint sigma hsigma)
    construction hconstruction

theorem endpointDifference_linearPrimitive_compute
    (c a b : Rat) (n : Nat) :
    endpointDifferenceCompute (Integral.linearPrimitiveFunRaw c) a b n =
      { lo := c * b - c * a, hi := c * b - c * a } := by
  unfold endpointDifferenceCompute endpointDifferenceInterval
    Integral.linearPrimitiveFunRaw RealFunRaw.exact
  simp

theorem constantPrimitiveEndpoint_valid (c a b : Rat) :
    RealRaw.ValidCompute
      (endpointDifferenceCompute (Integral.linearPrimitiveFunRaw c) a b) := by
  have hcompute :
      endpointDifferenceCompute (Integral.linearPrimitiveFunRaw c) a b =
        fun _ : Nat => { lo := c * b - c * a, hi := c * b - c * a } := by
    funext n
    exact endpointDifference_linearPrimitive_compute c a b n
  rw [hcompute]
  exact RealRaw.ofRat_valid (c * b - c * a)

/-- The first fully verified definite-integral identity: the one-cell
Riemann-sum integral of the constant function `c` equals the endpoint
difference of the primitive `x ↦ c*x`. -/
theorem constant_integral_equiv_endpoint (c a b : Rat) :
    DefiniteIntegralEqualsEndpointDifference
      (Integral.linearPrimitiveFunRaw c) (Integral.constantFunRaw c)
      a b (Integral.constantConstruction c a b)
      (constantPrimitiveEndpoint_valid c a b) := by
  apply RealRaw.sameStageOverlap_equiv
  intro n
  apply (RealRaw.compareAt_overlap_iff _ _ n n).2
  rw [Integral.constantIntegral_compute]
  simp [endpointDifferenceRaw, endpointDifference_linearPrimitive_compute]
  have harea : (b - a) * c = c * b - c * a := by
    grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
      Rat.mul_assoc, Rat.mul_comm]
  rw [harea]
  exact ⟨Rat.le_refl, Rat.le_refl⟩

def constantDefiniteIdentity (c a b : Rat) :
    DefiniteIdentity
      (Integral.constantFunRaw c) (Integral.linearPrimitiveFunRaw c) a b where
  construction := Integral.constantConstruction c a b
  endpoint_valid := constantPrimitiveEndpoint_valid c a b
  equivalent := constant_integral_equiv_endpoint c a b

end Integral

namespace IntegralIdentities

/-- The rational kernel `x ↦ 1 / (1 + x^2)` used by the integral
representation of arctangent. -/
def oneOverOnePlusSquareRaw : PartialRealFunRaw where
  definedAt := fun _ => True
  compute := fun x _ _ =>
    let y : Rat := 1 / (1 + x * x)
    { lo := y, hi := y }

/-- The kernel `1 / (1 + x^2)` certified on an arbitrary rational interval. -/
def oneOverOnePlusSquareOnInterval (a b : Rat) : FunctionOnInterval where
  raw := oneOverOnePlusSquareRaw
  lower := a
  upper := b
  defined_on := fun _ _ => trivial
  valid_on := by
    intro x hx
    simpa [oneOverOnePlusSquareRaw] using
      RealRaw.ofRat_valid (1 / (1 + x * x))

theorem oneOverOnePlusSquareOnInterval_valid (a b : Rat) :
    (oneOverOnePlusSquareOnInterval a b).toRealFunRaw.Valid :=
  FunctionOnInterval.toRealFunRaw_valid _

theorem oneOverOnePlusSquareOnInterval_toRealFunRaw_point
    (a b x : Rat) (n : Nat) :
    ((oneOverOnePlusSquareOnInterval a b).toRealFunRaw.compute x n).lo =
      ((oneOverOnePlusSquareOnInterval a b).toRealFunRaw.compute x n).hi := by
  by_cases hleft : a <= x
  · by_cases hright : x <= b
    · simp [FunctionOnInterval.toRealFunRaw, FunctionOnInterval.compute,
        oneOverOnePlusSquareOnInterval, oneOverOnePlusSquareRaw,
        hleft, hright]
    · simp [FunctionOnInterval.toRealFunRaw, oneOverOnePlusSquareOnInterval,
        hleft, hright]
  · simp [FunctionOnInterval.toRealFunRaw, oneOverOnePlusSquareOnInterval,
      hleft]

theorem oneOverOnePlusSquareRaw_compute_eq_sectorAreaDensity
    (u : Rat) (h : oneOverOnePlusSquareRaw.definedAt u) (n : Nat) :
    oneOverOnePlusSquareRaw.compute u h n =
      { lo := RationalCircle.Stage.sectorAreaDensity u,
        hi := RationalCircle.Stage.sectorAreaDensity u } := by
  rw [RationalCircle.Stage.sectorAreaDensity_eq_one_over_one_plus_square]
  simp [oneOverOnePlusSquareRaw]

/-- The arctangent kernel on `[0, x]`, as a domain-aware function. -/
abbrev arctanKernelInterval (x : Rat) : FunctionOnInterval :=
  oneOverOnePlusSquareOnInterval 0 x

/-- The arctangent kernel on the unit interval, as a domain-aware function. -/
abbrev arctanKernelIntervalAtOne : FunctionOnInterval :=
  arctanKernelInterval 1

/-- The verified midpoint-rectangle construction for
`∫_0^x dt / (1 + t^2)`, for rational `x` in `[0, 1]`. -/
def arctanIntegralRectangleConstruction
    (x : Rat) (hx0 : 0 <= x) (hx1 : x <= 1) :
    Integral.ConstructionFor (arctanKernelInterval x) where
  compute := ArctanGeometry.arctanIntegralRectangleCompute x
  certificate := by
    simpa [ArctanGeometry.arctanIntegralRectangleRaw] using
      ArctanGeometry.arctanIntegralRectangleRaw_valid hx0 hx1

/-- The domain-aware integral raw real supplied by the rectangle construction
for the arctangent kernel on `[0, x]`, with `0 <= x <= 1`. -/
def arctanIntegralRectangleFor
    (x : Rat) (hx0 : 0 <= x) (hx1 : x <= 1) : RealRaw :=
  Integral.integralFor (arctanKernelInterval x)
    (arctanIntegralRectangleConstruction x hx0 hx1)

theorem arctanIntegralRectangleFor_valid
    (x : Rat) (hx0 : 0 <= x) (hx1 : x <= 1) :
    (arctanIntegralRectangleFor x hx0 hx1).Valid :=
  Integral.integralFor_valid (arctanKernelInterval x)
    (arctanIntegralRectangleConstruction x hx0 hx1)

theorem arctanIntegralRectangleFor_compute_eq
    (x : Rat) (hx0 : 0 <= x) (hx1 : x <= 1) (n : Nat) :
    (arctanIntegralRectangleFor x hx0 hx1).compute n =
      ArctanGeometry.arctanIntegralRectangleCompute x n := rfl

theorem arctanIntegralRectangleFor_equiv_raw
    (x : Rat) (hx0 : 0 <= x) (hx1 : x <= 1) :
    (arctanIntegralRectangleFor x hx0 hx1).Equiv
      (ArctanGeometry.arctanIntegralRectangleRaw x) := by
  apply RealRaw.sameStageOverlap_equiv
  intro n
  apply (RealRaw.compareAt_overlap_iff
    (arctanIntegralRectangleFor x hx0 hx1)
    (ArctanGeometry.arctanIntegralRectangleRaw x) n n).2
  have hordered :=
    ArctanGeometry.arctanIntegralRectangleCompute_ordered hx0 n
  have hle :
      (ArctanGeometry.arctanIntegralRectangleCompute x n).lo <=
        (ArctanGeometry.arctanIntegralRectangleCompute x n).hi := by
    unfold QInterval.width at hordered
    grind [Rat.sub_eq_add_neg]
  change QInterval.Overlaps
    (ArctanGeometry.arctanIntegralRectangleCompute x n)
    (ArctanGeometry.arctanIntegralRectangleCompute x n)
  exact ⟨hle, hle⟩

/-- The arctangent kernel is nonincreasing on every interval `[0,x]`. -/
def arctanKernelInterval_monotone (x : Rat) :
    MonotoneOnInterval (arctanKernelInterval x) where
  increasing := False
  monotone_inc := by
    intro h
    cases h
  monotone_dec := by
    intro _hdec p q hp _hq hpq n
    have hkernel :
        ArctanGeometry.integralKernel q <=
          ArctanGeometry.integralKernel p :=
      ArctanGeometry.integralKernel_antitone_nonneg hp.1 hpq
    simpa [arctanKernelInterval, oneOverOnePlusSquareOnInterval,
      FunctionOnInterval.compute, oneOverOnePlusSquareRaw,
      ArctanGeometry.integralKernel] using hkernel

/-- The rectangle construction for `∫_0^x dt/(1+t^2)`, packaged as a
monotone integral for rational `x` in `[0,1]`. -/
def arctanIntegralRectangleMonotoneConstruction
    (x : Rat) (hx0 : 0 <= x) (hx1 : x <= 1) :
    Integral.MonotoneConstructionFor (arctanKernelInterval x) where
  monotone := arctanKernelInterval_monotone x
  construction := arctanIntegralRectangleConstruction x hx0 hx1

/-- The monotone-integral packaging of the rectangle arctangent computation
throughout the rational unit branch. -/
def arctanIntegralRectangleMonotoneFor
    (x : Rat) (hx0 : 0 <= x) (hx1 : x <= 1) : RealRaw :=
  Integral.monotoneIntegralFor (arctanKernelInterval x)
    (arctanIntegralRectangleMonotoneConstruction x hx0 hx1)

theorem arctanIntegralRectangleMonotoneFor_valid
    (x : Rat) (hx0 : 0 <= x) (hx1 : x <= 1) :
    (arctanIntegralRectangleMonotoneFor x hx0 hx1).Valid :=
  Integral.monotoneIntegralFor_valid (arctanKernelInterval x)
    (arctanIntegralRectangleMonotoneConstruction x hx0 hx1)

theorem arctanIntegralRectangleMonotoneFor_compute_eq
    (x : Rat) (hx0 : 0 <= x) (hx1 : x <= 1) (n : Nat) :
    (arctanIntegralRectangleMonotoneFor x hx0 hx1).compute n =
      (arctanIntegralRectangleFor x hx0 hx1).compute n := by
  change (arctanIntegralRectangleFor x hx0 hx1).compute n =
    (arctanIntegralRectangleFor x hx0 hx1).compute n
  rfl

theorem arctanIntegralRectangleMonotoneFor_equiv_rectangleFor
    (x : Rat) (hx0 : 0 <= x) (hx1 : x <= 1) :
    (arctanIntegralRectangleMonotoneFor x hx0 hx1).Equiv
      (arctanIntegralRectangleFor x hx0 hx1) := by
  change (arctanIntegralRectangleFor x hx0 hx1).Equiv
    (arctanIntegralRectangleFor x hx0 hx1)
  exact RealRaw.equiv_refl (arctanIntegralRectangleFor x hx0 hx1)
    (arctanIntegralRectangleFor_valid x hx0 hx1)

theorem arctanIntegralRectangleFor_equiv_arctanGeom
    (x : Rat) (hx0 : 0 <= x) (hx1 : x <= 1) :
    (arctanIntegralRectangleFor x hx0 hx1).Equiv
      (ArctanGeometry.arctanGeom x) := by
  intro n
  apply (RealRaw.compareAt_overlap_iff
    (arctanIntegralRectangleFor x hx0 hx1)
    (ArctanGeometry.arctanGeom x) n n).2
  have hover := (RealRaw.compareAt_overlap_iff
    (ArctanGeometry.arctanIntegralRectangleRaw x)
    (ArctanGeometry.arctanGeom x) n n).1
      (ArctanGeometry.arctanIntegralRectangleRaw_equiv_arctanGeom hx0 n)
  simpa [arctanIntegralRectangleFor, Integral.integralFor,
    arctanIntegralRectangleConstruction,
    ArctanGeometry.arctanIntegralRectangleRaw] using hover

theorem arctanIntegralRectangleMonotoneFor_equiv_arctanGeom
    (x : Rat) (hx0 : 0 <= x) (hx1 : x <= 1) :
    (arctanIntegralRectangleMonotoneFor x hx0 hx1).Equiv
      (ArctanGeometry.arctanGeom x) := by
  have hleft :
      (arctanIntegralRectangleMonotoneFor x hx0 hx1).Valid :=
    arctanIntegralRectangleMonotoneFor_valid x hx0 hx1
  have hmid :
      (arctanIntegralRectangleFor x hx0 hx1).Valid :=
    arctanIntegralRectangleFor_valid x hx0 hx1
  have hright : (ArctanGeometry.arctanGeom x).Valid :=
    ArctanGeometry.arctanGeom_valid_on_unit hx0 hx1
  exact RealRaw.equiv_trans
    hleft hmid hright
    (arctanIntegralRectangleMonotoneFor_equiv_rectangleFor x hx0 hx1)
    (arctanIntegralRectangleFor_equiv_arctanGeom x hx0 hx1)

/-- The verified rectangle-integral arctangent as a partial function on the
rational unit branch. -/
def arctanIntegralRectangleFunctionRaw : PartialRealFunRaw where
  definedAt := fun x => 0 <= x ∧ x <= 1
  compute := fun x hx => (arctanIntegralRectangleFor x hx.1 hx.2).compute
  rate := fun x hx => (arctanIntegralRectangleFor x hx.1 hx.2).rate

def arctanIntegralRectangleRepresentation :
    Elementary.Arctan.FunctionRepresentation where
  name := "arctan.integral.rectangle"
  raw := arctanIntegralRectangleFunctionRaw

theorem arctanIntegralRectangleFunctionRaw_valid :
    forall x h, RealRaw.ValidCompute
      (arctanIntegralRectangleFunctionRaw.compute x h) := by
  intro x hx
  simpa [arctanIntegralRectangleFunctionRaw] using
    arctanIntegralRectangleFor_valid x hx.1 hx.2

theorem arctanIntegralRectangleFunctionAgreement :
    Elementary.Arctan.Equivalent
      arctanIntegralRectangleRepresentation
      ArctanGeometry.representation := by
  intro x hx _hgeom
  simpa [Elementary.Arctan.Equivalent,
    arctanIntegralRectangleRepresentation,
    arctanIntegralRectangleFunctionRaw,
    ArctanGeometry.representation, ArctanGeometry.functionRaw,
    PartialRealFunRaw.evalRaw] using
    arctanIntegralRectangleFor_equiv_arctanGeom x hx.1 hx.2

/-- The rectangle-integral arctangent as a monotone-integral partial function
on the rational unit branch. -/
def arctanIntegralRectangleMonotoneFunctionRaw : PartialRealFunRaw where
  definedAt := fun x => 0 <= x ∧ x <= 1
  compute := fun x hx =>
    (arctanIntegralRectangleMonotoneFor x hx.1 hx.2).compute
  rate := fun x hx =>
    (arctanIntegralRectangleMonotoneFor x hx.1 hx.2).rate

def arctanIntegralRectangleMonotoneRepresentation :
    Elementary.Arctan.FunctionRepresentation where
  name := "arctan.integral.rectangle.monotone"
  raw := arctanIntegralRectangleMonotoneFunctionRaw

theorem arctanIntegralRectangleMonotoneFunctionRaw_valid :
    forall x h, RealRaw.ValidCompute
      (arctanIntegralRectangleMonotoneFunctionRaw.compute x h) := by
  intro x hx
  simpa [arctanIntegralRectangleMonotoneFunctionRaw] using
    arctanIntegralRectangleMonotoneFor_valid x hx.1 hx.2

theorem arctanIntegralRectangleMonotoneFunctionAgreement :
    Elementary.Arctan.Equivalent
      arctanIntegralRectangleMonotoneRepresentation
      ArctanGeometry.representation := by
  intro x hx _hgeom
  simpa [Elementary.Arctan.Equivalent,
    arctanIntegralRectangleMonotoneRepresentation,
    arctanIntegralRectangleMonotoneFunctionRaw,
    ArctanGeometry.representation, ArctanGeometry.functionRaw,
    PartialRealFunRaw.evalRaw] using
    arctanIntegralRectangleMonotoneFor_equiv_arctanGeom x hx.1 hx.2

/-- A unit-branch integral arctangent construction.  This is the domain-aware
version of the integral route currently proved by rectangle sums: it only asks
for integral constructions on inputs `0 <= x <= 1`. -/
def arctanIntegralUnit
    (x : Rat) (c : Integral.ConstructionFor (arctanKernelInterval x)) :
    RealRaw :=
  Integral.integralFor (arctanKernelInterval x) c

def ArctanIntegralUnitComputes
    (x : Rat) (_hx0 : 0 <= x) (_hx1 : x <= 1)
    (arctanBranch : RealRaw) : Prop :=
  Exists fun c : Integral.ConstructionFor (arctanKernelInterval x) =>
    (arctanIntegralUnit x c).Equiv arctanBranch

structure ArctanIntegralUnitData where
  constructionAt :
    forall x, 0 <= x -> x <= 1 ->
      Integral.ConstructionFor (arctanKernelInterval x)

def arctanIntegralUnitFunctionRaw
    (data : ArctanIntegralUnitData) : PartialRealFunRaw where
  definedAt := fun x => 0 <= x ∧ x <= 1
  compute := fun x hx =>
    (arctanIntegralUnit x
      (data.constructionAt x hx.1 hx.2)).compute
  rate := fun x hx =>
    (arctanIntegralUnit x
      (data.constructionAt x hx.1 hx.2)).rate

def arctanIntegralUnitRepresentation
    (data : ArctanIntegralUnitData) :
    Elementary.Arctan.FunctionRepresentation where
  name := "arctan.integral.unit"
  raw := arctanIntegralUnitFunctionRaw data

theorem arctanIntegralUnitFunctionRaw_valid
    (data : ArctanIntegralUnitData) :
    forall x h, RealRaw.ValidCompute
      ((arctanIntegralUnitFunctionRaw data).compute x h) := by
  intro x hx
  simpa [arctanIntegralUnitFunctionRaw, arctanIntegralUnit] using
    Integral.integralFor_valid (arctanKernelInterval x)
      (data.constructionAt x hx.1 hx.2)

def ArctanIntegralUnitGeomFunctionAgreement
    (data : ArctanIntegralUnitData) : Prop :=
  Elementary.Arctan.Equivalent
    (arctanIntegralUnitRepresentation data)
    ArctanGeometry.representation

theorem arctanIntegralUnit_equiv_arctanGeom_of_functionAgreement
    (data : ArctanIntegralUnitData)
    (h : ArctanIntegralUnitGeomFunctionAgreement data)
    {x : Rat} (hx0 : 0 <= x) (hx1 : x <= 1) :
    (arctanIntegralUnit x
      (data.constructionAt x hx0 hx1)).Equiv
        (ArctanGeometry.arctanGeom x) := by
  have hgeom : ArctanGeometry.representation.raw.definedAt x := by
    simp [ArctanGeometry.representation, ArctanGeometry.functionRaw]
  simpa [ArctanIntegralUnitGeomFunctionAgreement,
    arctanIntegralUnitRepresentation, arctanIntegralUnitFunctionRaw,
    ArctanGeometry.representation, ArctanGeometry.functionRaw,
    PartialRealFunRaw.evalRaw] using
    h x ⟨hx0, hx1⟩ hgeom

theorem arctanIntegralUnitComputes_arctanGeom_of_functionAgreement
    (data : ArctanIntegralUnitData)
    (h : ArctanIntegralUnitGeomFunctionAgreement data)
    (x : Rat) (hx0 : 0 <= x) (hx1 : x <= 1) :
    ArctanIntegralUnitComputes x hx0 hx1
      (ArctanGeometry.arctanGeom x) :=
  ⟨data.constructionAt x hx0 hx1,
    arctanIntegralUnit_equiv_arctanGeom_of_functionAgreement
      data h hx0 hx1⟩

theorem arctanIntegralUnitGeomAgreement_one_of_functionAgreement
    (data : ArctanIntegralUnitData)
    (h : ArctanIntegralUnitGeomFunctionAgreement data) :
    ArctanIntegralUnitComputes (1 : Rat)
      (by native_decide) (by native_decide)
      (ArctanGeometry.arctanGeom (1 : Rat)) :=
  arctanIntegralUnitComputes_arctanGeom_of_functionAgreement
    data h (1 : Rat) (by native_decide) (by native_decide)

/-- The rectangle construction supplies the verified unit-branch integral
arctangent data. -/
def arctanIntegralRectangleUnitData : ArctanIntegralUnitData where
  constructionAt := arctanIntegralRectangleConstruction

theorem arctanIntegralRectangleUnit_equiv_arctanGeom
    (x : Rat) (hx0 : 0 <= x) (hx1 : x <= 1) :
    (arctanIntegralUnit x
      (arctanIntegralRectangleUnitData.constructionAt x hx0 hx1)).Equiv
        (ArctanGeometry.arctanGeom x) := by
  simpa [arctanIntegralUnit, arctanIntegralRectangleUnitData,
    arctanIntegralRectangleFor] using
    arctanIntegralRectangleFor_equiv_arctanGeom x hx0 hx1

theorem arctanIntegralRectangleUnitFunctionAgreement :
    ArctanIntegralUnitGeomFunctionAgreement
      arctanIntegralRectangleUnitData := by
  intro x hx _hgeom
  simpa [ArctanIntegralUnitGeomFunctionAgreement,
    arctanIntegralUnitRepresentation, arctanIntegralUnitFunctionRaw,
    arctanIntegralUnit, arctanIntegralRectangleUnitData,
    arctanIntegralRectangleFor, ArctanGeometry.representation,
    ArctanGeometry.functionRaw, PartialRealFunRaw.evalRaw] using
    arctanIntegralRectangleFor_equiv_arctanGeom x hx.1 hx.2

theorem arctanIntegralRectangleUnitComputes
    (x : Rat) (hx0 : 0 <= x) (hx1 : x <= 1) :
    ArctanIntegralUnitComputes x hx0 hx1
      (ArctanGeometry.arctanGeom x) :=
  ⟨arctanIntegralRectangleUnitData.constructionAt x hx0 hx1,
    arctanIntegralRectangleUnit_equiv_arctanGeom x hx0 hx1⟩

theorem arctanIntegralRectangleUnitComputes_one :
    ArctanIntegralUnitComputes (1 : Rat)
      (by native_decide) (by native_decide)
      (ArctanGeometry.arctanGeom (1 : Rat)) :=
  arctanIntegralRectangleUnitComputes
    (1 : Rat) (by native_decide) (by native_decide)

/-- The rectangle construction supplies the same unit-branch integral
arctangent data through the monotone-integral interface. -/
def arctanIntegralRectangleMonotoneUnitData : ArctanIntegralUnitData where
  constructionAt := fun x hx0 hx1 =>
    (arctanIntegralRectangleMonotoneConstruction x hx0 hx1).construction

theorem arctanIntegralRectangleMonotoneUnit_equiv_arctanGeom
    (x : Rat) (hx0 : 0 <= x) (hx1 : x <= 1) :
    (arctanIntegralUnit x
      (arctanIntegralRectangleMonotoneUnitData.constructionAt
        x hx0 hx1)).Equiv
        (ArctanGeometry.arctanGeom x) := by
  simpa [arctanIntegralUnit, arctanIntegralRectangleMonotoneUnitData,
    arctanIntegralRectangleMonotoneFor,
    Integral.monotoneIntegralFor] using
    arctanIntegralRectangleMonotoneFor_equiv_arctanGeom x hx0 hx1

theorem arctanIntegralRectangleMonotoneUnitFunctionAgreement :
    ArctanIntegralUnitGeomFunctionAgreement
      arctanIntegralRectangleMonotoneUnitData := by
  intro x hx _hgeom
  simpa [ArctanIntegralUnitGeomFunctionAgreement,
    arctanIntegralUnitRepresentation, arctanIntegralUnitFunctionRaw,
    arctanIntegralUnit, arctanIntegralRectangleMonotoneUnitData,
    arctanIntegralRectangleMonotoneFor,
    Integral.monotoneIntegralFor, ArctanGeometry.representation,
    ArctanGeometry.functionRaw, PartialRealFunRaw.evalRaw] using
    arctanIntegralRectangleMonotoneFor_equiv_arctanGeom x hx.1 hx.2

theorem arctanIntegralRectangleMonotoneUnitComputes
    (x : Rat) (hx0 : 0 <= x) (hx1 : x <= 1) :
    ArctanIntegralUnitComputes x hx0 hx1
      (ArctanGeometry.arctanGeom x) :=
  ⟨arctanIntegralRectangleMonotoneUnitData.constructionAt x hx0 hx1,
    arctanIntegralRectangleMonotoneUnit_equiv_arctanGeom x hx0 hx1⟩

theorem arctanIntegralRectangleMonotoneUnitComputes_one :
    ArctanIntegralUnitComputes (1 : Rat)
      (by native_decide) (by native_decide)
      (ArctanGeometry.arctanGeom (1 : Rat)) :=
  arctanIntegralRectangleMonotoneUnitComputes
    (1 : Rat) (by native_decide) (by native_decide)

def arctanGeomOnUnit : FunctionOnInterval where
  raw := {
    definedAt := fun x => 0 <= x ∧ x <= 1
    compute := fun x _hx => (ArctanGeometry.arctanGeom x).compute
    rate := fun x _hx => (ArctanGeometry.arctanGeom x).rate
  }
  lower := 0
  upper := 1
  defined_on := fun _ hx => hx
  valid_on := by
    intro x hx
    exact ArctanGeometry.arctanGeom_valid_on_unit hx.1 hx.2

/-- Checked data for the first-octant inverse-arctangent step.

The forward branch is required to be the actual geometric arctangent on the
unit slope interval, and every normalized quarter-turn target is required to
be a valid, explicitly range-enclosed target for that branch.  The bisection
field is consequently an `InverseBisectionSearch`, not a pair of opaque
inverse-law propositions.  A concrete inhabitant still requires the pending
interval-regularity and effective-separation proofs for `arctanGeomOnUnit`.
-/
structure ArctanInverseBisection where
  branch : InvertibleFunctionOnInterval
  branch_is_geometric : branch.function = arctanGeomOnUnit
  targetAt : forall t : RationalCircle.GeometricTrig.QuarterTurn,
    RationalCircle.GeometricTrig.firstOctantBranch t -> InRangeRaw branch
  targetAt_equiv_quarterTurn :
    forall t ht, (targetAt t ht).value.Equiv
      (RationalCircle.GeometricTrig.quarterTurnRaw t)
  bisectionAt : forall y : InRangeRaw branch,
    InverseBisectionSearch branch y

namespace ArctanInverseBisection

/-- The inverse evaluator obtained from the supplied certified bisection
searches. -/
def inverseRaw (B : ArctanInverseBisection) : InverseRaw B.branch :=
  inverseRawOfSearch B.bisectionAt

/-- The tangent/slope raw real at a normalized first-octant angle. -/
def tangentAt (B : ArctanInverseBisection)
    (t : RationalCircle.GeometricTrig.QuarterTurn)
    (ht : RationalCircle.GeometricTrig.firstOctantBranch t) : RealRaw :=
  (B.inverseRaw).apply (B.targetAt t ht)

/-- The first-octant tangent function produced by the constructive inverse
theorem.  Its outputs are rational boxes for the slope in `[0,1]`; the circle
coordinates can therefore be evaluated from the rational parametrization. -/
def tangentRaw (B : ArctanInverseBisection) : PartialRealFunRaw where
  definedAt := RationalCircle.GeometricTrig.firstOctantBranch
  compute := fun t ht => (B.tangentAt t ht).compute

theorem tangentAt_valid (B : ArctanInverseBisection)
    (t : RationalCircle.GeometricTrig.QuarterTurn)
    (ht : RationalCircle.GeometricTrig.firstOctantBranch t) :
    (B.tangentAt t ht).Valid :=
  (B.inverseRaw).apply_valid (B.targetAt t ht)

theorem tangentRaw_valid (B : ArctanInverseBisection) :
    forall t ht, RealRaw.ValidCompute (B.tangentRaw.compute t ht) := by
  intro t ht
  simpa [tangentRaw] using B.tangentAt_valid t ht

theorem tangentAt_stays_in_source (B : ArctanInverseBisection)
    (t : RationalCircle.GeometricTrig.QuarterTurn)
    (ht : RationalCircle.GeometricTrig.firstOctantBranch t) :
    forall n, subintervalOf ((B.tangentAt t ht).compute n)
      B.branch.function.lower B.branch.function.upper :=
  (B.inverseRaw).apply_stays_in_source (B.targetAt t ht)

/-- The first-octant inverse output lies in the actual unit slope interval,
because its forward branch is certified equal to `arctanGeomOnUnit`. -/
theorem tangentAt_stays_in_unitSlope (B : ArctanInverseBisection)
    (t : RationalCircle.GeometricTrig.QuarterTurn)
    (ht : RationalCircle.GeometricTrig.firstOctantBranch t) :
    forall n, subintervalOf ((B.tangentAt t ht).compute n) 0 1 := by
  simpa [B.branch_is_geometric, arctanGeomOnUnit] using
    B.tangentAt_stays_in_source t ht

/-- The forward interval evaluator overlaps the certified target box at each
stage.  Together with `targetAt_equiv_quarterTurn`, this is the computable
inverse law relating the recovered slope to the requested quarter-turn angle.
-/
theorem tangentAt_forward_overlaps_target
    (B : ArctanInverseBisection)
    (t : RationalCircle.GeometricTrig.QuarterTurn)
    (ht : RationalCircle.GeometricTrig.firstOctantBranch t) :
    forall n, QInterval.Overlaps
      (B.branch.continuous.regular.evalInterval
        ((B.tangentAt t ht).compute n)
        (B.tangentAt_stays_in_source t ht n) n)
      ((B.targetAt t ht).value.compute n) :=
  (B.inverseRaw).apply_value_overlaps_target (B.targetAt t ht)

theorem targetAt_quarterTurn_equiv
    (B : ArctanInverseBisection)
    (t : RationalCircle.GeometricTrig.QuarterTurn)
    (ht : RationalCircle.GeometricTrig.firstOctantBranch t) :
    (B.targetAt t ht).value.Equiv
      (RationalCircle.GeometricTrig.quarterTurnRaw t) :=
  B.targetAt_equiv_quarterTurn t ht

end ArctanInverseBisection

theorem arctanGeomOnUnit_toRealFunRaw_compute_zero (n : Nat) :
    arctanGeomOnUnit.toRealFunRaw.compute 0 n =
      (ArctanGeometry.arctanGeom (0 : Rat)).compute n := by
  rw [FunctionOnInterval.toRealFunRaw_compute_of_mem
    arctanGeomOnUnit (x := 0)
      (hx := ⟨by native_decide, by native_decide⟩) n]
  rfl

theorem arctanGeomOnUnit_toRealFunRaw_compute_one (n : Nat) :
    arctanGeomOnUnit.toRealFunRaw.compute 1 n =
      (ArctanGeometry.arctanGeom (1 : Rat)).compute n := by
  rw [FunctionOnInterval.toRealFunRaw_compute_of_mem
    arctanGeomOnUnit (x := 1)
      (hx := ⟨by native_decide, by native_decide⟩) n]
  rfl

theorem arctanGeomOnUnit_endpointDifference_compute_eq (n : Nat) :
    endpointDifferenceCompute arctanGeomOnUnit.toRealFunRaw 0 1 n =
      (ArctanGeometry.arctanGeom (1 : Rat) -
        ArctanGeometry.arctanGeom (0 : Rat)).compute n := by
  unfold endpointDifferenceCompute endpointDifferenceInterval
  rw [arctanGeomOnUnit_toRealFunRaw_compute_one n,
    arctanGeomOnUnit_toRealFunRaw_compute_zero n]
  rfl

theorem arctanGeomOnUnit_endpointDifference_valid :
    RealRaw.ValidCompute
      (endpointDifferenceCompute arctanGeomOnUnit.toRealFunRaw 0 1) := by
  have hsub :
      (ArctanGeometry.arctanGeom (1 : Rat) -
        ArctanGeometry.arctanGeom (0 : Rat)).Valid :=
    RealRaw.sub_valid
      (ArctanGeometry.arctanGeom_valid_on_unit
        (x := (1 : Rat)) (by native_decide) (by native_decide))
      (ArctanGeometry.arctanGeom_valid_on_unit
        (x := (0 : Rat)) (by native_decide) (by native_decide))
  have hcompute :
      endpointDifferenceCompute arctanGeomOnUnit.toRealFunRaw 0 1 =
        (ArctanGeometry.arctanGeom (1 : Rat) -
          ArctanGeometry.arctanGeom (0 : Rat)).compute := by
    funext n
    exact arctanGeomOnUnit_endpointDifference_compute_eq n
  rw [hcompute]
  exact hsub

theorem arctanGeomOnUnit_endpointDifference_equiv_sub :
    (endpointDifferenceRaw arctanGeomOnUnit.toRealFunRaw 0 1
      arctanGeomOnUnit_endpointDifference_valid).Equiv
        (ArctanGeometry.arctanGeom (1 : Rat) -
          ArctanGeometry.arctanGeom (0 : Rat)) := by
  apply RealRaw.sameStageOverlap_equiv
  intro n
  apply (RealRaw.compareAt_overlap_iff
    (endpointDifferenceRaw arctanGeomOnUnit.toRealFunRaw 0 1
      arctanGeomOnUnit_endpointDifference_valid)
    (ArctanGeometry.arctanGeom (1 : Rat) -
      ArctanGeometry.arctanGeom (0 : Rat)) n n).2
  change QInterval.Overlaps
    (endpointDifferenceCompute arctanGeomOnUnit.toRealFunRaw 0 1 n)
    ((ArctanGeometry.arctanGeom (1 : Rat) -
      ArctanGeometry.arctanGeom (0 : Rat)).compute n)
  rw [arctanGeomOnUnit_endpointDifference_compute_eq n]
  have hvalid :
      (ArctanGeometry.arctanGeom (1 : Rat) -
        ArctanGeometry.arctanGeom (0 : Rat)).Valid :=
    RealRaw.sub_valid
      (ArctanGeometry.arctanGeom_valid_on_unit
        (x := (1 : Rat)) (by native_decide) (by native_decide))
      (ArctanGeometry.arctanGeom_valid_on_unit
        (x := (0 : Rat)) (by native_decide) (by native_decide))
  have horder := RealRaw.interval_order_of_valid
    (ArctanGeometry.arctanGeom (1 : Rat) -
      ArctanGeometry.arctanGeom (0 : Rat)) hvalid n
  exact ⟨horder, horder⟩

theorem arctanGeom_one_sub_zero_equiv :
    (ArctanGeometry.arctanGeom (1 : Rat) -
      ArctanGeometry.arctanGeom (0 : Rat)).Equiv
        (ArctanGeometry.arctanGeom (1 : Rat)) := by
  rw [ArctanGeometry.arctanGeom_zero]
  apply RealRaw.sameStageOverlap_equiv
  intro n
  apply (RealRaw.compareAt_overlap_iff
    (ArctanGeometry.arctanGeom (1 : Rat) - RealRaw.ofRat 0)
    (ArctanGeometry.arctanGeom (1 : Rat)) n n).2
  change QInterval.Overlaps
    { lo := ((ArctanGeometry.arctanGeom (1 : Rat)).compute n).lo - 0,
      hi := ((ArctanGeometry.arctanGeom (1 : Rat)).compute n).hi - 0 }
    ((ArctanGeometry.arctanGeom (1 : Rat)).compute n)
  have horder := RealRaw.interval_order_of_valid
    (ArctanGeometry.arctanGeom (1 : Rat))
    (ArctanGeometry.arctanGeom_valid_on_unit
      (x := (1 : Rat)) (by native_decide) (by native_decide)) n
  constructor <;> grind [Rat.sub_eq_add_neg]

theorem arctanGeomOnUnit_endpointDifference_equiv_arctanGeom_one :
    (endpointDifferenceRaw arctanGeomOnUnit.toRealFunRaw 0 1
      arctanGeomOnUnit_endpointDifference_valid).Equiv
        (ArctanGeometry.arctanGeom (1 : Rat)) := by
  have hendpoint :
      (endpointDifferenceRaw arctanGeomOnUnit.toRealFunRaw 0 1
        arctanGeomOnUnit_endpointDifference_valid).Valid := by
    simpa [endpointDifferenceRaw, RealRaw.Valid] using
      arctanGeomOnUnit_endpointDifference_valid
  have hsub :
      (ArctanGeometry.arctanGeom (1 : Rat) -
        ArctanGeometry.arctanGeom (0 : Rat)).Valid :=
    RealRaw.sub_valid
      (ArctanGeometry.arctanGeom_valid_on_unit
        (x := (1 : Rat)) (by native_decide) (by native_decide))
      (ArctanGeometry.arctanGeom_valid_on_unit
        (x := (0 : Rat)) (by native_decide) (by native_decide))
  exact RealRaw.equiv_trans
    hendpoint
    hsub
    (ArctanGeometry.arctanGeom_valid_on_unit
      (x := (1 : Rat)) (by native_decide) (by native_decide))
    arctanGeomOnUnit_endpointDifference_equiv_sub
    arctanGeom_one_sub_zero_equiv

/-- The verified rectangle-sum construction for
`∫_0^1 dt / (1 + t^2)`, packaged as a `ConstructionFor` on the arctangent
kernel interval. -/
def arctanIntegralRectangleConstructionAtOne :
    Integral.ConstructionFor arctanKernelIntervalAtOne where
  compute := ArctanGeometry.arctanIntegralRectangleComputeAtOne
  certificate := by
    simpa [ArctanGeometry.arctanIntegralRectangleRawAtOne] using
      ArctanGeometry.arctanIntegralRectangleRawAtOne_valid

/-- The domain-aware integral raw real supplied by the rectangle construction
for the arctangent kernel on `[0, 1]`. -/
def arctanIntegralRectangleForAtOne : RealRaw :=
  Integral.integralFor arctanKernelIntervalAtOne
    arctanIntegralRectangleConstructionAtOne

theorem arctanIntegralRectangleForAtOne_valid :
    arctanIntegralRectangleForAtOne.Valid :=
  Integral.integralFor_valid arctanKernelIntervalAtOne
    arctanIntegralRectangleConstructionAtOne

theorem arctanIntegralRectangleForAtOne_compute_eq (n : Nat) :
    arctanIntegralRectangleForAtOne.compute n =
      ArctanGeometry.arctanIntegralRectangleComputeAtOne n := rfl

theorem arctanIntegralRectangleForAtOne_equiv_raw :
    arctanIntegralRectangleForAtOne.Equiv
      ArctanGeometry.arctanIntegralRectangleRawAtOne := by
  apply RealRaw.sameStageOverlap_equiv
  intro n
  apply (RealRaw.compareAt_overlap_iff
    arctanIntegralRectangleForAtOne
    ArctanGeometry.arctanIntegralRectangleRawAtOne n n).2
  have hordered :=
    ArctanGeometry.arctanIntegralRectangleComputeAtOne_ordered n
  have hle :
      (ArctanGeometry.arctanIntegralRectangleComputeAtOne n).lo <=
        (ArctanGeometry.arctanIntegralRectangleComputeAtOne n).hi := by
    unfold QInterval.width at hordered
    grind [Rat.sub_eq_add_neg]
  change QInterval.Overlaps
    (ArctanGeometry.arctanIntegralRectangleComputeAtOne n)
    (ArctanGeometry.arctanIntegralRectangleComputeAtOne n)
  exact ⟨hle, hle⟩

/-- The arctangent kernel is nonincreasing on the unit interval. -/
def arctanKernelIntervalAtOne_monotone :
    MonotoneOnInterval arctanKernelIntervalAtOne :=
  arctanKernelInterval_monotone 1

/-- The rectangle construction for `∫_0^1 dx/(1+x^2)` as a monotone integral. -/
def arctanIntegralRectangleMonotoneConstructionAtOne :
    Integral.MonotoneConstructionFor arctanKernelIntervalAtOne where
  monotone := arctanKernelIntervalAtOne_monotone
  construction := arctanIntegralRectangleConstructionAtOne

/-- The monotone-integral packaging of the rectangle arctangent computation. -/
def arctanIntegralRectangleMonotoneForAtOne : RealRaw :=
  Integral.monotoneIntegralFor arctanKernelIntervalAtOne
    arctanIntegralRectangleMonotoneConstructionAtOne

theorem arctanIntegralRectangleMonotoneForAtOne_valid :
    arctanIntegralRectangleMonotoneForAtOne.Valid :=
  Integral.monotoneIntegralFor_valid arctanKernelIntervalAtOne
    arctanIntegralRectangleMonotoneConstructionAtOne

theorem arctanIntegralRectangleMonotoneForAtOne_compute_eq (n : Nat) :
    arctanIntegralRectangleMonotoneForAtOne.compute n =
      arctanIntegralRectangleForAtOne.compute n := by
  change arctanIntegralRectangleForAtOne.compute n =
    arctanIntegralRectangleForAtOne.compute n
  rfl

theorem arctanIntegralRectangleMonotoneForAtOne_equiv_rectangleForAtOne :
    arctanIntegralRectangleMonotoneForAtOne.Equiv
      arctanIntegralRectangleForAtOne :=
  by
    change arctanIntegralRectangleForAtOne.Equiv
      arctanIntegralRectangleForAtOne
    exact RealRaw.equiv_refl arctanIntegralRectangleForAtOne
      arctanIntegralRectangleForAtOne_valid

theorem arctanIntegralRectangleForAtOne_equiv_arctanGeom_one :
    arctanIntegralRectangleForAtOne.Equiv
      (ArctanGeometry.arctanGeom (1 : Rat)) :=
  by
    intro n
    apply (RealRaw.compareAt_overlap_iff
      arctanIntegralRectangleForAtOne
      (ArctanGeometry.arctanGeom (1 : Rat)) n n).2
    have hover := (RealRaw.compareAt_overlap_iff
      ArctanGeometry.arctanIntegralRectangleRawAtOne
      (ArctanGeometry.arctanGeom (1 : Rat)) n n).1
        (ArctanGeometry.arctanIntegralRectangleRawAtOne_equiv_arctanGeom_one n)
    simpa [arctanIntegralRectangleForAtOne, Integral.integralFor,
      arctanIntegralRectangleConstructionAtOne,
      ArctanGeometry.arctanIntegralRectangleRawAtOne] using hover

/-- Rectangle-sum unit arctangent as a definite-integral identity: the
verified midpoint construction of `∫_0^1 dx/(1+x^2)` computes the endpoint
difference of the geometric arctangent primitive. -/
def arctanGeomUnitRectangleDefiniteIdentity :
    Integral.DefiniteIdentityFor
      (oneOverOnePlusSquareOnInterval 0 1) arctanGeomOnUnit where
  same_lower := rfl
  same_upper := rfl
  construction := arctanIntegralRectangleConstructionAtOne
  endpoint_valid := arctanGeomOnUnit_endpointDifference_valid
  equivalent := by
    have hleft : arctanIntegralRectangleForAtOne.Valid :=
      arctanIntegralRectangleForAtOne_valid
    have hmid : (ArctanGeometry.arctanGeom (1 : Rat)).Valid :=
      ArctanGeometry.arctanGeom_valid_on_unit
        (x := (1 : Rat)) (by native_decide) (by native_decide)
    have hright :
        (endpointDifferenceRaw arctanGeomOnUnit.toRealFunRaw 0 1
          arctanGeomOnUnit_endpointDifference_valid).Valid := by
      simpa [endpointDifferenceRaw, RealRaw.Valid] using
        arctanGeomOnUnit_endpointDifference_valid
    simpa [arctanIntegralRectangleForAtOne] using
      RealRaw.equiv_trans hleft hmid hright
        arctanIntegralRectangleForAtOne_equiv_arctanGeom_one
        (RealRaw.equiv_symm
          arctanGeomOnUnit_endpointDifference_equiv_arctanGeom_one)

/-- The same unit arctangent endpoint identity, but with the integral side
explicitly packaged as a monotone integral for the decreasing kernel. -/
def arctanGeomUnitRectangleMonotoneDefiniteIdentity :
    Integral.MonotoneDefiniteIdentityFor
      (oneOverOnePlusSquareOnInterval 0 1) arctanGeomOnUnit where
  same_lower := rfl
  same_upper := rfl
  construction := arctanIntegralRectangleMonotoneConstructionAtOne
  endpoint_valid := arctanGeomOnUnit_endpointDifference_valid
  equivalent := by
    have hleft : arctanIntegralRectangleMonotoneForAtOne.Valid :=
      arctanIntegralRectangleMonotoneForAtOne_valid
    have hrect : arctanIntegralRectangleForAtOne.Valid :=
      arctanIntegralRectangleForAtOne_valid
    have hgeom : (ArctanGeometry.arctanGeom (1 : Rat)).Valid :=
      ArctanGeometry.arctanGeom_valid_on_unit
        (x := (1 : Rat)) (by native_decide) (by native_decide)
    have hendpoint :
        (endpointDifferenceRaw arctanGeomOnUnit.toRealFunRaw 0 1
          arctanGeomOnUnit_endpointDifference_valid).Valid := by
      simpa [endpointDifferenceRaw, RealRaw.Valid] using
        arctanGeomOnUnit_endpointDifference_valid
    have hmonoGeom :
        arctanIntegralRectangleMonotoneForAtOne.Equiv
          (ArctanGeometry.arctanGeom (1 : Rat)) :=
      RealRaw.equiv_trans hleft hrect hgeom
        arctanIntegralRectangleMonotoneForAtOne_equiv_rectangleForAtOne
        arctanIntegralRectangleForAtOne_equiv_arctanGeom_one
    simpa [arctanIntegralRectangleMonotoneForAtOne,
      Integral.monotoneIntegralFor] using
      RealRaw.equiv_trans hleft hgeom hendpoint
        hmonoGeom
        (RealRaw.equiv_symm
          arctanGeomOnUnit_endpointDifference_equiv_arctanGeom_one)

/-- The monotone rectangle endpoint identity, forgetting the monotonicity
certificate and viewed through the ordinary `DefiniteIdentityFor` interface. -/
def arctanGeomUnitRectangleMonotoneDefiniteIdentityFor :
    Integral.DefiniteIdentityFor
      (oneOverOnePlusSquareOnInterval 0 1) arctanGeomOnUnit :=
  arctanGeomUnitRectangleMonotoneDefiniteIdentity.toDefiniteIdentityFor

/-- The same unit arctangent endpoint identity, now viewed through the public
piecewise-monotone/general integral interface. -/
noncomputable def arctanGeomUnitRectangleGeneralDefiniteIdentity :
    Integral.GeneralDefiniteIdentityFor
      (oneOverOnePlusSquareOnInterval 0 1) arctanGeomOnUnit :=
  Integral.GeneralDefiniteIdentityFor.ofMonotone
    arctanGeomUnitRectangleMonotoneDefiniteIdentity
    (by native_decide)

/-- The construction-transport version of the monotone rectangle endpoint
identity.  This is a small sanity check for the generic transport lemma:
changing the construction by an equivalent integral preserves the endpoint
identity. -/
def arctanGeomUnitRectangleMonotoneTransportedDefiniteIdentity :
    Integral.DefiniteIdentityFor
      (oneOverOnePlusSquareOnInterval 0 1) arctanGeomOnUnit :=
  Integral.DefiniteIdentityFor.transportConstruction
    arctanGeomUnitRectangleDefiniteIdentity
    arctanIntegralRectangleMonotoneConstructionAtOne.construction
    (by
      change arctanIntegralRectangleForAtOne.Equiv
        arctanIntegralRectangleForAtOne
      exact RealRaw.equiv_refl arctanIntegralRectangleForAtOne
        arctanIntegralRectangleForAtOne_valid)

/-- The ordinary and monotone rectangle endpoint identities have equivalent
integral raw reals. -/
theorem arctanGeomUnitRectangleMonotoneDefiniteIdentity_equiv_rectangle :
    (Integral.integralFor
      (oneOverOnePlusSquareOnInterval 0 1)
      arctanGeomUnitRectangleMonotoneDefiniteIdentityFor.construction).Equiv
      (Integral.integralFor
        (oneOverOnePlusSquareOnInterval 0 1)
        arctanGeomUnitRectangleDefiniteIdentity.construction) :=
  Integral.DefiniteIdentityFor.integral_equiv_integral
    arctanGeomUnitRectangleMonotoneDefiniteIdentityFor
    arctanGeomUnitRectangleDefiniteIdentity

/-- The theorem target for the integral arctangent comparison on `[0, x]`.
It says that the integral of `1 / (1 + t^2)` computes the chosen arctangent
branch. -/
abbrev ArctanIntegralConstruction (x : Rat) :=
  Integral.Construction
    (oneOverOnePlusSquareOnInterval 0 x).toRealFunRaw 0 x

def arctanIntegral (x : Rat)
    (c : ArctanIntegralConstruction x) : RealRaw :=
  Integral.integral
    (oneOverOnePlusSquareOnInterval 0 x).toRealFunRaw 0 x c

theorem arctanIntegral_valid (x : Rat)
    (c : ArctanIntegralConstruction x) :
    (arctanIntegral x c).Valid :=
  by
    simpa [arctanIntegral] using FTC.integral_valid_of_construction c

/-- The legacy `Integral.Construction` wrapper uses exact point evaluations of
`1/(1+x^2)`.  Hence every scheduled left-Riemann sum is a point interval. -/
theorem arctanIntegral_compute_width_zero (x : Rat)
    (c : ArctanIntegralConstruction x) (n : Nat) :
    ((arctanIntegral x c).compute n).width = 0 := by
  simpa [arctanIntegral, Integral.integral, Integral.Certificate.realRaw,
    Integral.Raw.toRealRaw, Integral.Raw.compute, Integral.algorithm] using
    riemannLeftInterval_point_width_zero
      (oneOverOnePlusSquareOnInterval 0 x).toRealFunRaw
      0 x (c.plan n).subdivisions (c.plan n).evalPrecision
      (fun y =>
        oneOverOnePlusSquareOnInterval_toRealFunRaw_point
          0 x y (c.plan n).evalPrecision)

/-- Consequently, a valid old-style `arctanIntegral` construction has no
stage-to-stage refinement: all of its intervals are equal.  This records why
the newer `ConstructionFor` interface is the meaningful arctangent-integral
route in the scoreboard. -/
theorem arctanIntegral_stages_constant (x : Rat)
    (c : ArctanIntegralConstruction x) (n m : Nat) :
    (arctanIntegral x c).compute n =
      (arctanIntegral x c).compute m :=
  RealRaw.stage_eq_of_valid_zero_width
    (arctanIntegral x c)
    (arctanIntegral_valid x c)
    (arctanIntegral_compute_width_zero x c)
    n m

def ArctanIntegralComputes (x : Rat) (arctanBranch : RealRaw) : Prop :=
  Exists fun c : ArctanIntegralConstruction x =>
    (arctanIntegral x c).Equiv arctanBranch

/-- Pointwise version of the integral/geometric arctangent comparison.  The
function-level statement below is the preferred interface; this pointwise form
is useful for pi at `x = 1`. -/
def ArctanIntegralGeomAgreement (x : Rat) : Prop :=
  ArctanIntegralComputes x (ArctanGeometry.arctanGeom x)

/-- A choice of integral construction for each nonnegative rational input.

The current definite-integral wrapper is oriented from `0` to `x`, so this
first integral-arctangent representation is naturally defined on `0 <= x`.
The overlap convention then compares it with total geometric arctangent exactly
on the nonnegative rationals. -/
structure ArctanIntegralData where
  constructionAt : forall x, 0 <= x -> ArctanIntegralConstruction x

def arctanIntegralFunctionRaw
    (data : ArctanIntegralData) : PartialRealFunRaw where
  definedAt := fun x => 0 <= x
  compute := fun x hx => (arctanIntegral x (data.constructionAt x hx)).compute
  rate := fun x hx => (arctanIntegral x (data.constructionAt x hx)).rate

def arctanIntegralRepresentation
    (data : ArctanIntegralData) :
    Elementary.Arctan.FunctionRepresentation where
  name := "arctan.integral"
  raw := arctanIntegralFunctionRaw data

def ArctanIntegralGeomFunctionAgreement
    (data : ArctanIntegralData) : Prop :=
  Elementary.Arctan.Equivalent
    (arctanIntegralRepresentation data)
    ArctanGeometry.representation

theorem arctanIntegral_equiv_arctanGeom_of_functionAgreement
    (data : ArctanIntegralData)
    (h : ArctanIntegralGeomFunctionAgreement data)
    {x : Rat} (hx : 0 <= x) :
    (arctanIntegral x (data.constructionAt x hx)).Equiv
      (ArctanGeometry.arctanGeom x) := by
  have hgeom : ArctanGeometry.representation.raw.definedAt x := by
    simp [ArctanGeometry.representation, ArctanGeometry.functionRaw]
  simpa [ArctanIntegralGeomFunctionAgreement,
    arctanIntegralRepresentation, arctanIntegralFunctionRaw,
    ArctanGeometry.representation, ArctanGeometry.functionRaw,
    PartialRealFunRaw.AgreeOnOverlap, RealRaw.Equiv] using
    h x hx hgeom

theorem arctanIntegralGeomAgreement_one_of_functionAgreement
    (data : ArctanIntegralData)
    (h : ArctanIntegralGeomFunctionAgreement data) :
    ArctanIntegralGeomAgreement (1 : Rat) := by
  exact ⟨data.constructionAt (1 : Rat) (by native_decide),
    arctanIntegral_equiv_arctanGeom_of_functionAgreement
      data h (by native_decide)⟩

/-- A resulting pi computation from the integral arctangent at `1`. -/
def PiFromArctanIntegral (arctanAtOne : RealRaw) : RealRaw :=
  RealRaw.scaleRat 4 arctanAtOne

/-- The geometric-pi comparison target for the integral arctangent computation. -/
def PiFromArctanIntegralAgrees (arctanAtOne : RealRaw) : Prop :=
  (PiFromArctanIntegral arctanAtOne).Equiv piCircleArea

/-- The integral-arctangent route to geometric pi, isolated into the two
mathematical bridges that still need estimates: first show the integral kernel
computes the geometric arctangent at `1`, then identify `4 * arctanGeom 1`
with the geometric area definition of pi. -/
structure ArctanIntegralPiRoute where
  integral_computes_geom_at_one :
    ArctanIntegralComputes 1 (ArctanGeometry.arctanGeom 1)
  four_geom_arctan_one_eq_pi :
    PiFromArctanIntegralAgrees (ArctanGeometry.arctanGeom 1)

namespace ArctanIntegralPiRoute

theorem pi_agrees (R : ArctanIntegralPiRoute) :
    PiFromArctanIntegralAgrees (ArctanGeometry.arctanGeom 1) :=
  R.four_geom_arctan_one_eq_pi

end ArctanIntegralPiRoute

/-- The compactified positive-half-line density for the Cauchy kernel.  The
second summand is the reciprocal tail after the change of variables
`x ↦ 1 / x`. -/
def cauchyProjectiveFoldDensity (x : Rat) : Rat :=
  ArctanGeometry.integralKernel x +
    (1 / (x * x)) * ArctanGeometry.integralKernel (1 / x)

/-- Reciprocal compactification of the Cauchy kernel is exact on nonzero
rational inputs.  Together with evenness, this is the finite rational algebra
behind the full-line Cauchy integral being represented by four copies of the
unit-interval integral. -/
theorem cauchyProjectiveFoldDensity_eq_two_integralKernel
    (x : Rat) (hx : x ≠ 0) :
    cauchyProjectiveFoldDensity x =
      2 * ArctanGeometry.integralKernel x := by
  have hx2 : x * x ≠ 0 := by
    exact Rat.ne_of_gt
      (RationalCircle.Trigonometry.ratSquare_pos_of_ne_zero hx)
  have hden : 1 + (1 / x) * (1 / x) = (1 + x * x) / (x * x) := by
    rw [Rat.div_def]
    grind [Rat.mul_add, Rat.add_mul, Rat.add_assoc, Rat.add_comm,
      Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
  unfold cauchyProjectiveFoldDensity ArctanGeometry.integralKernel
  rw [hden]
  rw [Rat.div_def, Rat.div_def, Rat.div_def]
  grind [Rat.mul_add, Rat.add_mul, Rat.add_assoc, Rat.add_comm,
    Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

/-- A rational compactification of an even full-line integral by folding the
positive reciprocal tail back onto the unit interval.

For an even kernel `kernel`, the intended value is
\[
  2\int_0^1\left(k(x)+x^{-2}k(1/x)\right)\,dx.
\]
The compact density includes its removable value at zero, so the construction
is an ordinary finite interval integral.  The `fold_agrees` field is the
finite rational identity on the punctured unit interval; no improper limit or
completed-real endpoint is built into this definition. -/
structure ReciprocalTailCompactification
    (kernel compactDensity : Rat -> Rat) where
  even : forall x, kernel (-x) = kernel x
  fold_agrees : forall x, 0 < x -> x <= 1 ->
    compactDensity x = kernel x +
      (1 / (x * x)) * kernel (1 / x)
  construction : Integral.ConstructionFor
    (FunctionOnInterval.exactRat compactDensity 0 1)

namespace ReciprocalTailCompactification

/-- The finite compact integral representing the folded positive half of the
even full-line integral. -/
def compactIntegral
    {kernel compactDensity : Rat -> Rat}
    (C : ReciprocalTailCompactification kernel compactDensity) : RealRaw :=
  Integral.integralFor (FunctionOnInterval.exactRat compactDensity 0 1)
    C.construction

theorem compactIntegral_valid
    {kernel compactDensity : Rat -> Rat}
    (C : ReciprocalTailCompactification kernel compactDensity) :
    C.compactIntegral.Valid :=
  Integral.integralFor_valid _ C.construction

/-- The projective full-line integral defined by reciprocal-tail folding. -/
def fullLineIntegral
    {kernel compactDensity : Rat -> Rat}
    (C : ReciprocalTailCompactification kernel compactDensity) : RealRaw :=
  RealRaw.scaleRat 2 C.compactIntegral

theorem fullLineIntegral_valid
    {kernel compactDensity : Rat -> Rat}
    (C : ReciprocalTailCompactification kernel compactDensity) :
    C.fullLineIntegral.Valid :=
  RealRaw.scaleRat_valid C.compactIntegral_valid

end ReciprocalTailCompactification

/-- The removable compact density for the Cauchy kernel.  On the punctured
unit interval it is exactly the kernel plus its reciprocal tail. -/
def cauchyReciprocalTailDensity (x : Rat) : Rat :=
  2 * ArctanGeometry.integralKernel x

theorem cauchyReciprocalTailDensity_even (x : Rat) :
    cauchyReciprocalTailDensity (-x) = cauchyReciprocalTailDensity x := by
  unfold cauchyReciprocalTailDensity ArctanGeometry.integralKernel
  congr 2
  grind [Rat.neg_mul, Rat.mul_neg, Rat.neg_neg]

theorem integralKernel_even (x : Rat) :
    ArctanGeometry.integralKernel (-x) = ArctanGeometry.integralKernel x := by
  unfold ArctanGeometry.integralKernel
  congr 1
  grind [Rat.neg_mul, Rat.mul_neg, Rat.neg_neg]

theorem cauchyReciprocalTailDensity_fold_agrees
    (x : Rat) (hx : 0 < x) (_hx1 : x <= 1) :
    cauchyReciprocalTailDensity x = ArctanGeometry.integralKernel x +
      (1 / (x * x)) * ArctanGeometry.integralKernel (1 / x) := by
  have hxne : x ≠ 0 := Rat.ne_of_gt hx
  unfold cauchyReciprocalTailDensity
  exact (cauchyProjectiveFoldDensity_eq_two_integralKernel x hxne).symm

/-- The Cauchy compact density is computed by exactly twice the verified
rectangle bracket for `1 / (1+x^2)`.  This is a cellwise rational scaling,
not a new arctangent representation. -/
def cauchyReciprocalTailConstruction :
    Integral.ConstructionFor
      (FunctionOnInterval.exactRat cauchyReciprocalTailDensity 0 1) where
  compute := RealRaw.scaleRatCompute 2 arctanIntegralRectangleForAtOne
  certificate := by
    simpa [RealRaw.scaleRat] using
      (RealRaw.scaleRat_valid (r := (2 : Rat))
        arctanIntegralRectangleForAtOne_valid)

/-- The completed rational compactification of the Cauchy full-line integral.
Its outer factor accounts for the negative half-line, and its density's inner
factor accounts for the reciprocal positive tail. -/
def cauchyReciprocalTailCompactification :
    ReciprocalTailCompactification
      ArctanGeometry.integralKernel cauchyReciprocalTailDensity where
  even := integralKernel_even
  fold_agrees := cauchyReciprocalTailDensity_fold_agrees
  construction := cauchyReciprocalTailConstruction

/-- The full-line Cauchy integral, defined entirely by the rational
reciprocal-tail compactification. -/
def cauchyFullLineIntegral : RealRaw :=
  cauchyReciprocalTailCompactification.fullLineIntegral

theorem cauchyFullLineIntegral_valid : cauchyFullLineIntegral.Valid :=
  cauchyReciprocalTailCompactification.fullLineIntegral_valid

theorem cauchyFullLineIntegral_compute_eq_four_rectangle (n : Nat) :
    cauchyFullLineIntegral.compute n =
      (RealRaw.scaleRat 4 arctanIntegralRectangleForAtOne).compute n := by
  simp [cauchyFullLineIntegral,
    ReciprocalTailCompactification.fullLineIntegral,
    ReciprocalTailCompactification.compactIntegral,
    cauchyReciprocalTailCompactification,
    cauchyReciprocalTailConstruction, Integral.integralFor,
    RealRaw.scaleRat, RealRaw.scaleRatCompute]
  grind [Rat.mul_assoc]

/-- The denominator of the reciprocal quartic test integrand. -/
def reciprocalQuarticDenominator (a x : Rat) : Rat :=
  x * x * x * x + a * (x * x) + 1

/-- The reciprocal quartic kernel
`x ↦ 1 / (x^4 + a*x^2 + 1)`, written without powers so the finite algebra is
transparent to Lean. -/
def reciprocalQuarticKernel (a x : Rat) : Rat :=
  1 / reciprocalQuarticDenominator a x

/-- The projective-line substitution used on the positive half-line. -/
def reciprocalDifference (x : Rat) : Rat :=
  x - 1 / x

/-- The formal derivative of `x - 1/x`, expressed as a rational function. -/
def reciprocalDifferenceJacobian (x : Rat) : Rat :=
  1 + 1 / (x * x)

/-- The denominator of the shifted Cauchy kernel obtained after the substitution
`u = x - 1/x`. -/
def shiftedCauchyDenominator (a u : Rat) : Rat :=
  u * u + a + 2

/-- The shifted Cauchy kernel `u ↦ 1 / (u^2 + a + 2)`. -/
def shiftedCauchyKernel (a u : Rat) : Rat :=
  1 / shiftedCauchyDenominator a u

/-- At `a = -1`, the shifted Cauchy denominator is exactly the arctangent
denominator. -/
theorem shiftedCauchyDenominator_minus_one_eq_one_plus_square (u : Rat) :
    shiftedCauchyDenominator (-1) u = 1 + u * u := by
  unfold shiftedCauchyDenominator
  grind [Rat.add_assoc, Rat.add_comm]

/-- At `a = -1`, the shifted Cauchy kernel is the arctangent kernel. -/
theorem shiftedCauchyKernel_minus_one_eq_integralKernel (u : Rat) :
    shiftedCauchyKernel (-1) u = ArctanGeometry.integralKernel u := by
  unfold shiftedCauchyKernel ArctanGeometry.integralKernel
  rw [shiftedCauchyDenominator_minus_one_eq_one_plus_square]

/-- The raw arctangent kernel computes the shifted Cauchy kernel in the
pi-producing case `a = -1`. -/
theorem oneOverOnePlusSquareRaw_compute_eq_shiftedCauchyKernel_minus_one
    (u : Rat) (h : oneOverOnePlusSquareRaw.definedAt u) (n : Nat) :
    oneOverOnePlusSquareRaw.compute u h n =
      { lo := shiftedCauchyKernel (-1) u,
        hi := shiftedCauchyKernel (-1) u } := by
  rw [shiftedCauchyKernel_minus_one_eq_integralKernel]
  simp [oneOverOnePlusSquareRaw, ArctanGeometry.integralKernel]

/-- The symmetrized quartic density that appears after pairing `x` with
`1/x` on the positive half-line. -/
def reciprocalQuarticSymmetricDensity (a x : Rat) : Rat :=
  (1 + x * x) * reciprocalQuarticKernel a x

/-- The folded positive-half-line density obtained by sending the tail
`[1, infinity)` back to `[0,1]` by `x ↦ 1/x`. -/
def reciprocalQuarticUnitFoldDensity (a x : Rat) : Rat :=
  reciprocalQuarticKernel a x +
    (1 / (x * x)) * reciprocalQuarticKernel a (1 / x)

/-- Expected value of the full-line reciprocal quartic test integral when
`a + 2 = b^2` and `0 < b`: it should be `pi / b`. -/
def reciprocalQuarticExpectedPiMultiple (b : Rat) : RealRaw :=
  RealRaw.scaleRat (1 / b) piCircleArea

/-- Expected raw value of the clean projective test
`∫_(-∞)^∞ dx/(x^4 - x^2 + 1)`, namely `pi`.  This is only the expected value;
the projective integral construction still has to be supplied separately. -/
def reciprocalQuarticMinusOneExpectedPi : RealRaw :=
  reciprocalQuarticExpectedPiMultiple 1

/-- The rational parameter condition under which the reciprocal quartic integral
is expected to reduce to a rational multiple of pi. -/
def ReciprocalQuarticPiParameter (a b : Rat) : Prop :=
  0 < b ∧ a + 2 = b * b

theorem reciprocalQuarticPiParameter_minus_one :
    ReciprocalQuarticPiParameter (-1) 1 := by
  unfold ReciprocalQuarticPiParameter
  constructor <;> native_decide

private theorem rat_square_pos_of_ne_zero {x : Rat} (hx : x ≠ 0) :
    0 < x * x := by
  by_cases hxpos : 0 < x
  · exact Rat.mul_pos hxpos hxpos
  · have hxneg : x < 0 := by grind
    have hnegpos : 0 < -x := by grind
    have hsq : 0 < (-x) * (-x) := Rat.mul_pos hnegpos hnegpos
    grind [Rat.neg_mul, Rat.mul_neg, Rat.neg_neg]

private theorem rat_square_nonneg (x : Rat) : 0 <= x * x := by
  by_cases hx : 0 <= x
  · exact Rat.mul_nonneg hx hx
  · have hneg : 0 <= -x := by grind
    have hsq : 0 <= (-x) * (-x) := Rat.mul_nonneg hneg hneg
    grind [Rat.mul_neg, Rat.neg_mul, Rat.neg_neg]

private theorem rat_eq_of_mul_eq_mul_ne {a b c : Rat}
    (hc : c ≠ 0) (h : a * c = b * c) : a = b := by
  calc
    a = (a * c) * c⁻¹ := by
      have hcancel : c * c⁻¹ = 1 := Rat.mul_inv_cancel c hc
      grind [Rat.mul_assoc, Rat.mul_comm]
    _ = (b * c) * c⁻¹ := by rw [h]
    _ = b := by
      have hcancel : c * c⁻¹ = 1 := Rat.mul_inv_cancel c hc
      grind [Rat.mul_assoc, Rat.mul_comm]

/-- Clearing denominators in the projective substitution:
\[
  x^2\left((x-1/x)^2+a+2\right)=x^4+a x^2+1.
\]
This is the finite rational identity behind the quartic test integral. -/
theorem reciprocalDifference_quartic_denominator
    (a x : Rat) (hx : x ≠ 0) :
    x * x * shiftedCauchyDenominator a (reciprocalDifference x) =
      reciprocalQuarticDenominator a x := by
  unfold shiftedCauchyDenominator reciprocalDifference
    reciprocalQuarticDenominator
  rw [Rat.div_def]
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.add_assoc,
    Rat.add_comm, Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

/-- The quartic denominator is reciprocal after clearing the expected
projective factor \(x^4\). -/
theorem reciprocalQuarticDenominator_reciprocal_cleared
    (a x : Rat) (hx : x ≠ 0) :
    x * x * x * x * reciprocalQuarticDenominator a (1 / x) =
      reciprocalQuarticDenominator a x := by
  unfold reciprocalQuarticDenominator
  rw [Rat.div_def]
  grind [Rat.mul_add, Rat.add_mul, Rat.add_assoc, Rat.add_comm,
    Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

/-- Clearing the denominator in the formal derivative of `x - 1/x`. -/
theorem reciprocalDifferenceJacobian_square_cleared
    (x : Rat) (hx : x ≠ 0) :
    reciprocalDifferenceJacobian x * (x * x) = 1 + x * x := by
  have hx2 : x * x ≠ 0 := Rat.ne_of_gt (rat_square_pos_of_ne_zero hx)
  unfold reciprocalDifferenceJacobian
  rw [Rat.div_def]
  grind [Rat.mul_add, Rat.add_mul, Rat.add_assoc, Rat.add_comm,
    Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

/-- The two denominator-cleared identities that convert the reciprocal quartic
kernel into the shifted Cauchy kernel under `u = x - 1/x`.  This is the algebraic
core of the test integral over the projective line; the later integral theorem
will supply the improper-integral bookkeeping. -/
theorem reciprocalQuartic_projective_substitution_data
    (a x : Rat) (hx : x ≠ 0) :
    x * x * shiftedCauchyDenominator a (reciprocalDifference x) =
        reciprocalQuarticDenominator a x ∧
      reciprocalDifferenceJacobian x * (x * x) = 1 + x * x :=
  ⟨reciprocalDifference_quartic_denominator a x hx,
    reciprocalDifferenceJacobian_square_cleared x hx⟩

/-- In the clean pi case \(a=-1\), the shifted Cauchy denominator is
`u^2 + 1`, hence strictly positive on rational inputs. -/
theorem shiftedCauchyDenominator_minus_one_pos (u : Rat) :
    0 < shiftedCauchyDenominator (-1) u := by
  unfold shiftedCauchyDenominator
  have hs : 0 <= u * u := rat_square_nonneg u
  grind

/-- In the clean pi case \(a=-1\), the reciprocal quartic denominator is
strictly positive on rational inputs. -/
theorem reciprocalQuarticDenominator_minus_one_pos (x : Rat) :
    0 < reciprocalQuarticDenominator (-1) x := by
  by_cases hxzero : x = 0
  · subst x
    unfold reciprocalQuarticDenominator
    native_decide
  · have hden := reciprocalDifference_quartic_denominator (-1) x hxzero
    have hx2pos : 0 < x * x := rat_square_pos_of_ne_zero hxzero
    have hEpos :
        0 < shiftedCauchyDenominator (-1) (reciprocalDifference x) :=
      shiftedCauchyDenominator_minus_one_pos (reciprocalDifference x)
    have hprod :
        0 < x * x *
          shiftedCauchyDenominator (-1) (reciprocalDifference x) :=
      Rat.mul_pos hx2pos hEpos
    rw [hden] at hprod
    exact hprod

/-- The clean reciprocal-quartic denominator is uniformly separated from
zero by a rational constant.  This is the denominator estimate needed for a
future compact-interval regularity certificate. -/
theorem reciprocalQuarticDenominator_minus_one_ge_three_quarters (x : Rat) :
    (3 : Rat) / 4 <= reciprocalQuarticDenominator (-1) x := by
  have hsq : 0 <= (2 * x * x - 1) * (2 * x * x - 1) :=
    rat_square_nonneg (2 * x * x - 1)
  have hid :
      4 * reciprocalQuarticDenominator (-1) x - 3 =
        (2 * x * x - 1) * (2 * x * x - 1) := by
    unfold reciprocalQuarticDenominator
    grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.add_assoc,
      Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
  have hfour : 3 <= 4 * reciprocalQuarticDenominator (-1) x := by
    have hnonneg : 0 <= 4 * reciprocalQuarticDenominator (-1) x - 3 := by
      rw [hid]
      exact hsq
    grind [Rat.sub_eq_add_neg]
  have hscaled := Rat.mul_le_mul_of_nonneg_right hfour
    (by native_decide : (0 : Rat) <= 1 / 4)
  calc
    (3 : Rat) / 4 = 3 * (1 / 4) := by
      rw [Rat.div_def, Rat.div_def, Rat.one_mul]
    _ <= (4 * reciprocalQuarticDenominator (-1) x) * (1 / 4) := hscaled
    _ = reciprocalQuarticDenominator (-1) x := by
      rw [Rat.div_def]
      have hcancel : (4 : Rat) * (4 : Rat)⁻¹ = 1 := by native_decide
      grind [Rat.mul_assoc, Rat.mul_comm]

/-- The compact reciprocal-quartic density is nonnegative at every rational
point.  Together with the uniform denominator bound, this supplies the basic
range information for its forthcoming interval-regularity certificate. -/
theorem reciprocalQuarticSymmetricDensity_minus_one_nonneg (x : Rat) :
    0 <= reciprocalQuarticSymmetricDensity (-1) x := by
  unfold reciprocalQuarticSymmetricDensity reciprocalQuarticKernel
  apply Rat.mul_nonneg
  · have hsq : 0 <= x * x := rat_square_nonneg x
    grind
  · rw [Rat.div_def, Rat.one_mul]
    exact Rat.le_of_lt ((Rat.inv_pos).2
      (reciprocalQuarticDenominator_minus_one_pos x))

/-- A uniform rational upper bound for the clean compact density on its
closed chart interval.  It supplies the explicit removable-endpoint tail
budget for the projective quadrature schedule. -/
theorem reciprocalQuarticSymmetricDensity_minus_one_le_eight_thirds_on_unit
    {x : Rat} (hxlo : -1 <= x) (hxhi : x <= 1) :
    reciprocalQuarticSymmetricDensity (-1) x <= (8 : Rat) / 3 := by
  let q : Rat := reciprocalQuarticDenominator (-1) x
  have hx0sq : 0 <= x * x := rat_square_nonneg x
  have hx2le : x * x <= 1 := by
    by_cases hx0 : 0 <= x
    · calc
        x * x <= 1 * x := Rat.mul_le_mul_of_nonneg_right hxhi hx0
        _ <= 1 * 1 := Rat.mul_le_mul_of_nonneg_left hxhi (by native_decide)
        _ = 1 := by native_decide
    · have hxneg : x < 0 := by grind
      have hxneg0 : 0 <= -x := by grind
      have hnegx : -x <= 1 := by grind
      have hsq : (-x) * (-x) <= 1 * 1 := by
        calc
          (-x) * (-x) <= 1 * (-x) :=
            Rat.mul_le_mul_of_nonneg_right hnegx hxneg0
          _ <= 1 * 1 := Rat.mul_le_mul_of_nonneg_left hnegx (by native_decide)
      calc
        x * x = (-x) * (-x) := by
          grind [Rat.neg_mul, Rat.mul_neg, Rat.neg_neg]
        _ <= 1 * 1 := hsq
        _ = 1 := by native_decide
  have hnum : 1 + x * x <= 2 := by grind
  have hq : (3 : Rat) / 4 <= q := by
    simpa [q] using reciprocalQuarticDenominator_minus_one_ge_three_quarters x
  have hqpos : 0 < q := by grind
  have hqinv0 : 0 <= q⁻¹ := Rat.le_of_lt ((Rat.inv_pos).2 hqpos)
  have hscale : 1 <= ((4 : Rat) / 3) * q := by
    have h := Rat.mul_le_mul_of_nonneg_left hq
      (by native_decide : (0 : Rat) <= (4 : Rat) / 3)
    have hconst : ((4 : Rat) / 3) * ((3 : Rat) / 4) = 1 := by
      native_decide
    rw [hconst] at h
    exact h
  have hqinv : q⁻¹ <= (4 : Rat) / 3 := by
    calc
      q⁻¹ = 1 * q⁻¹ := by grind
      _ <= (((4 : Rat) / 3) * q) * q⁻¹ :=
        Rat.mul_le_mul_of_nonneg_right hscale hqinv0
      _ = (4 : Rat) / 3 := by
        have hcancel : q * q⁻¹ = 1 := Rat.mul_inv_cancel q (Rat.ne_of_gt hqpos)
        grind [Rat.mul_assoc, Rat.mul_comm]
  unfold reciprocalQuarticSymmetricDensity reciprocalQuarticKernel
  change (1 + x * x) * (1 / q) <= (8 : Rat) / 3
  rw [Rat.div_def]
  simp only [Rat.one_mul]
  calc
    (1 + x * x) * q⁻¹ <= 2 * q⁻¹ :=
      Rat.mul_le_mul_of_nonneg_right hnum hqinv0
    _ <= 2 * ((4 : Rat) / 3) :=
      Rat.mul_le_mul_of_nonneg_left hqinv (by native_decide)
    _ = (8 : Rat) / 3 := by native_decide

/-- The one-cell Lipschitz upper enclosure of the compact density on the
remaining interval from s to 1. -/
def projectiveCompactTailUpperCell (s : Rat) : Rat :=
  (1 - s) *
    (reciprocalQuarticSymmetricDensity (-1) s + 8 * (1 - s))

/-- The endpoint cell of the compact projective schedule has a rational tail
budget that is linear in its distance to the chart endpoint. -/
theorem projectiveCompactTailUpperCell_le
    {s : Rat} (hs0 : 0 <= s) (hs1 : s <= 1) :
    projectiveCompactTailUpperCell s <= ((32 : Rat) / 3) * (1 - s) := by
  have hwidth : 0 <= 1 - s := by grind
  have hwidth_le_one : 1 - s <= 1 := by grind
  have hvalue : reciprocalQuarticSymmetricDensity (-1) s <= (8 : Rat) / 3 :=
    reciprocalQuarticSymmetricDensity_minus_one_le_eight_thirds_on_unit
      (by grind) hs1
  unfold projectiveCompactTailUpperCell
  calc
    (1 - s) * (reciprocalQuarticSymmetricDensity (-1) s + 8 * (1 - s)) <=
        (1 - s) * ((8 : Rat) / 3 + 8 * (1 - s)) :=
      Rat.mul_le_mul_of_nonneg_left ((Rat.add_le_add_right).2 hvalue) hwidth
    _ <= (1 - s) * ((8 : Rat) / 3 + 8 * 1) :=
      Rat.mul_le_mul_of_nonneg_left
        ((Rat.add_le_add_left).2
          (Rat.mul_le_mul_of_nonneg_left hwidth_le_one (by native_decide))) hwidth
    _ = ((32 : Rat) / 3) * (1 - s) := by
      grind [Rat.mul_assoc, Rat.mul_comm]

/-- Exact finite-difference factorization for the compact reciprocal-quartic
density.  It exposes the denominator and polynomial factors from which a
finite-interval Lipschitz modulus will be derived. -/
theorem reciprocalQuarticSymmetricDensity_minus_one_sub (x y : Rat) :
    reciprocalQuarticSymmetricDensity (-1) x -
        reciprocalQuarticSymmetricDensity (-1) y =
      ((y * y - x * x) *
          (x * x + y * y + (x * x) * (y * y) - 2)) /
        (reciprocalQuarticDenominator (-1) x *
          reciprocalQuarticDenominator (-1) y) := by
  let qx := reciprocalQuarticDenominator (-1) x
  let qy := reciprocalQuarticDenominator (-1) y
  have hqx : qx ≠ 0 := by
    simpa [qx] using Rat.ne_of_gt (reciprocalQuarticDenominator_minus_one_pos x)
  have hqy : qy ≠ 0 := by
    simpa [qy] using Rat.ne_of_gt (reciprocalQuarticDenominator_minus_one_pos y)
  have hprod : qx * qy ≠ 0 := by
    intro hzero
    rcases Rat.mul_eq_zero.mp hzero with hzero | hzero
    · exact hqx hzero
    · exact hqy hzero
  apply rat_eq_of_mul_eq_mul_ne (c := qx * qy) hprod
  calc
    (reciprocalQuarticSymmetricDensity (-1) x -
        reciprocalQuarticSymmetricDensity (-1) y) * (qx * qy) =
        (1 + x * x) * qy - (1 + y * y) * qx := by
      change
        ((1 + x * x) * (1 / qx) - (1 + y * y) * (1 / qy)) * (qx * qy) =
          (1 + x * x) * qy - (1 + y * y) * qx
      rw [Rat.div_def, Rat.div_def]
      have hix : qx⁻¹ * qx = 1 := by
        rw [Rat.mul_comm]
        exact Rat.mul_inv_cancel qx hqx
      have hiy : qy⁻¹ * qy = 1 := by
        rw [Rat.mul_comm]
        exact Rat.mul_inv_cancel qy hqy
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.add_assoc,
        Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
    _ = ((y * y - x * x) *
          (x * x + y * y + (x * x) * (y * y) - 2)) := by
      dsimp [qx, qy]
      unfold reciprocalQuarticDenominator
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.add_assoc,
        Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
    _ = (((y * y - x * x) *
          (x * x + y * y + (x * x) * (y * y) - 2)) /
        (qx * qy)) * (qx * qy) := by
      rw [Rat.div_def]
      symm
      calc
        (((y * y - x * x) *
          (x * x + y * y + (x * x) * (y * y) - 2)) * (qx * qy)⁻¹) *
            (qx * qy) =
            ((y * y - x * x) *
              (x * x + y * y + (x * x) * (y * y) - 2)) *
                ((qx * qy)⁻¹ * (qx * qy)) := by
              rw [Rat.mul_assoc]
        _ = ((y * y - x * x) *
          (x * x + y * y + (x * x) * (y * y) - 2)) * 1 := by
            rw [Rat.inv_mul_cancel (qx * qy) hprod]
        _ = ((y * y - x * x) *
          (x * x + y * y + (x * x) * (y * y) - 2)) := by
            rw [Rat.mul_one]

private theorem square_le_one_of_between {x : Rat}
    (hxlo : -1 <= x) (hxhi : x <= 1) : x * x <= 1 := by
  by_cases hx : 0 <= x
  · calc
      x * x <= 1 * x := Rat.mul_le_mul_of_nonneg_right hxhi hx
      _ = x := by rw [Rat.one_mul]
      _ <= 1 := hxhi
  · have hxl : x <= 0 := by grind
    have hnx : 0 <= -x := by grind
    have hnhi : -x <= 1 := by grind
    have hs : (-x) * (-x) <= 1 := by
      calc
        (-x) * (-x) <= 1 * (-x) := Rat.mul_le_mul_of_nonneg_right hnhi hnx
        _ = -x := by rw [Rat.one_mul]
        _ <= 1 := hnhi
    grind [Rat.neg_mul, Rat.mul_neg, Rat.neg_neg]

private theorem sum_abs_le_two {x y : Rat}
    (hxlo : -1 <= x) (hxhi : x <= 1)
    (hylo : -1 <= y) (hyhi : y <= 1) : qabs (y + x) <= 2 := by
  apply qabs_le_of_neg_le_le
  · grind
  · grind

private theorem reciprocalQuarticLipschitzFactor_abs_le_two {x y : Rat}
    (hxlo : -1 <= x) (hxhi : x <= 1)
    (hylo : -1 <= y) (hyhi : y <= 1) :
    qabs (x * x + y * y + (x * x) * (y * y) - 2) <= 2 := by
  have hxx0 := rat_square_nonneg x
  have hyy0 := rat_square_nonneg y
  have hxx1 := square_le_one_of_between hxlo hxhi
  have hyy1 := square_le_one_of_between hylo hyhi
  have hprod0 : 0 <= (x * x) * (y * y) := Rat.mul_nonneg hxx0 hyy0
  have hprod1 : (x * x) * (y * y) <= 1 := by
    calc
      (x * x) * (y * y) <= 1 * (y * y) :=
        Rat.mul_le_mul_of_nonneg_right hxx1 hyy0
      _ <= 1 * 1 := Rat.mul_le_mul_of_nonneg_left hyy1
        (by native_decide : (0 : Rat) <= 1)
      _ = 1 := by native_decide
  apply qabs_le_of_neg_le_le
  · grind [Rat.sub_eq_add_neg]
  · have hsum : x * x + y * y <= 2 := by
      calc
        x * x + y * y <= 1 + y * y :=
          (Rat.add_le_add_right).2 hxx1
        _ <= 1 + 1 := (Rat.add_le_add_left).2 hyy1
        _ = 2 := by native_decide
    have hall : x * x + y * y + (x * x) * (y * y) <= 3 := by
      calc
        x * x + y * y + (x * x) * (y * y) <= 2 + (x * x) * (y * y) :=
          (Rat.add_le_add_right).2 hsum
        _ <= 2 + 1 := (Rat.add_le_add_left).2 hprod1
        _ = 3 := by native_decide
    grind [Rat.sub_eq_add_neg]

private theorem reciprocalQuarticSquareDifference_abs_le_two_mul {x y : Rat}
    (hxlo : -1 <= x) (hxhi : x <= 1)
    (hylo : -1 <= y) (hyhi : y <= 1) :
    qabs (y * y - x * x) <= 2 * qabs (y - x) := by
  have hsum := sum_abs_le_two hxlo hxhi hylo hyhi
  calc
    qabs (y * y - x * x) = qabs ((y - x) * (y + x)) := by
      congr 1
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.add_assoc,
        Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
    _ = qabs (y - x) * qabs (y + x) := qabs_mul _ _
    _ <= qabs (y - x) * 2 := Rat.mul_le_mul_of_nonneg_left hsum
      (qabs_nonneg _)
    _ = 2 * qabs (y - x) := by rw [Rat.mul_comm]

/-- The reciprocal of the two compact denominator factors has a uniform
rational upper bound. -/
theorem reciprocalQuarticDenominatorProduct_minus_one_inv_le_sixteen_ninths
    (x y : Rat) :
    (reciprocalQuarticDenominator (-1) x *
      reciprocalQuarticDenominator (-1) y)⁻¹ <= (16 : Rat) / 9 := by
  let qx := reciprocalQuarticDenominator (-1) x
  let qy := reciprocalQuarticDenominator (-1) y
  change (qx * qy)⁻¹ <= (16 : Rat) / 9
  have hqx : (3 : Rat) / 4 <= qx := by
    simpa [qx] using reciprocalQuarticDenominator_minus_one_ge_three_quarters x
  have hqy : (3 : Rat) / 4 <= qy := by
    simpa [qy] using reciprocalQuarticDenominator_minus_one_ge_three_quarters y
  have hqx0 : 0 <= qx := Rat.le_trans (by native_decide) hqx
  have hqprod : (9 : Rat) / 16 <= qx * qy := by
    calc
      (9 : Rat) / 16 = ((3 : Rat) / 4) * ((3 : Rat) / 4) := by native_decide
      _ <= qx * ((3 : Rat) / 4) := Rat.mul_le_mul_of_nonneg_right hqx
        (by native_decide)
      _ <= qx * qy := Rat.mul_le_mul_of_nonneg_left hqy hqx0
  have hprodpos : 0 < qx * qy := Rat.mul_pos (by grind) (by grind)
  have hprodne : qx * qy ≠ 0 := Rat.ne_of_gt hprodpos
  have hinvnonneg : 0 <= (qx * qy)⁻¹ :=
    Rat.le_of_lt ((Rat.inv_pos).2 hprodpos)
  have hscale : 1 <= ((16 : Rat) / 9) * (qx * qy) := by
    have h := Rat.mul_le_mul_of_nonneg_left hqprod
      (by native_decide : (0 : Rat) <= (16 : Rat) / 9)
    have hconst : ((16 : Rat) / 9) * ((9 : Rat) / 16) = 1 := by
      native_decide
    rw [hconst] at h
    exact h
  calc
    (qx * qy)⁻¹ = 1 * (qx * qy)⁻¹ := by rw [Rat.one_mul]
    _ <= (((16 : Rat) / 9) * (qx * qy)) * (qx * qy)⁻¹ :=
      Rat.mul_le_mul_of_nonneg_right hscale hinvnonneg
    _ = (16 : Rat) / 9 := by
      have hcancel : (qx * qy) * (qx * qy)⁻¹ = 1 :=
        Rat.mul_inv_cancel _ hprodne
      grind [Rat.mul_assoc, Rat.mul_comm]

/-- The compact reciprocal-quartic density has an explicit rational
Lipschitz bound on the closed unit interval. -/
theorem reciprocalQuarticSymmetricDensity_minus_one_lipschitz_on_unit (x y : Rat)
    (hxlo : -1 <= x) (hxhi : x <= 1)
    (hylo : -1 <= y) (hyhi : y <= 1) :
    qabs (reciprocalQuarticSymmetricDensity (-1) x -
      reciprocalQuarticSymmetricDensity (-1) y) <= 8 * qabs (y - x) := by
  rw [reciprocalQuarticSymmetricDensity_minus_one_sub]
  have hsq := reciprocalQuarticSquareDifference_abs_le_two_mul hxlo hxhi hylo hyhi
  have hfactor := reciprocalQuarticLipschitzFactor_abs_le_two hxlo hxhi hylo hyhi
  have hnum :
      qabs ((y * y - x * x) *
          (x * x + y * y + (x * x) * (y * y) - 2)) <=
        4 * qabs (y - x) := by
    calc
      qabs ((y * y - x * x) *
          (x * x + y * y + (x * x) * (y * y) - 2)) =
          qabs (y * y - x * x) *
            qabs (x * x + y * y + (x * x) * (y * y) - 2) := qabs_mul _ _
      _ <= (2 * qabs (y - x)) *
          qabs (x * x + y * y + (x * x) * (y * y) - 2) :=
            Rat.mul_le_mul_of_nonneg_right hsq (qabs_nonneg _)
      _ <= (2 * qabs (y - x)) * 2 :=
            Rat.mul_le_mul_of_nonneg_left hfactor
              (Rat.mul_nonneg (by native_decide) (qabs_nonneg _))
      _ = 4 * qabs (y - x) := by grind [Rat.mul_assoc, Rat.mul_comm]
  have hinv :=
    reciprocalQuarticDenominatorProduct_minus_one_inv_le_sixteen_ninths x y
  have hinv0 : 0 <=
      (reciprocalQuarticDenominator (-1) x *
        reciprocalQuarticDenominator (-1) y)⁻¹ := by
    apply Rat.le_of_lt
    apply (Rat.inv_pos).2
    exact Rat.mul_pos (reciprocalQuarticDenominator_minus_one_pos x)
      (reciprocalQuarticDenominator_minus_one_pos y)
  calc
    qabs
        (((y * y - x * x) *
          (x * x + y * y + (x * x) * (y * y) - 2)) /
          (reciprocalQuarticDenominator (-1) x *
            reciprocalQuarticDenominator (-1) y)) =
        qabs ((y * y - x * x) *
          (x * x + y * y + (x * x) * (y * y) - 2)) *
          (reciprocalQuarticDenominator (-1) x *
            reciprocalQuarticDenominator (-1) y)⁻¹ := by
          rw [Rat.div_def, qabs_mul, qabs_eq_self_of_nonneg hinv0]
    _ <= (4 * qabs (y - x)) *
          (reciprocalQuarticDenominator (-1) x *
            reciprocalQuarticDenominator (-1) y)⁻¹ :=
          Rat.mul_le_mul_of_nonneg_right hnum hinv0
    _ <= (4 * qabs (y - x)) * ((16 : Rat) / 9) :=
          Rat.mul_le_mul_of_nonneg_left hinv
            (Rat.mul_nonneg (by native_decide) (qabs_nonneg _))
    _ <= 8 * qabs (y - x) := by
          have h64 : (4 : Rat) * ((16 : Rat) / 9) <= 8 := by native_decide
          calc
            (4 * qabs (y - x)) * ((16 : Rat) / 9) =
                ((4 : Rat) * ((16 : Rat) / 9)) * qabs (y - x) := by
                grind [Rat.mul_assoc, Rat.mul_comm]
            _ <= 8 * qabs (y - x) := Rat.mul_le_mul_of_nonneg_right h64
              (qabs_nonneg _)

/-- The projective coordinate compactifying the real line to the open interval
`(-1,1)`.  Its apparent poles at the endpoints disappear after multiplication
by the Cauchy kernel; the resulting density is the everywhere-defined reciprocal-quartic
kernel below. -/
def projectiveCompactCoordinate (x : Rat) : Rat :=
  x / (1 - x * x)

/-- Formal Jacobian of `projectiveCompactCoordinate`. -/
def projectiveCompactJacobian (x : Rat) : Rat :=
  (1 + x * x) / ((1 - x * x) * (1 - x * x))

/-- The compact projective coordinate is odd. -/
theorem projectiveCompactCoordinate_neg (x : Rat) :
    projectiveCompactCoordinate (-x) = -projectiveCompactCoordinate x := by
  unfold projectiveCompactCoordinate
  rw [Rat.div_def, Rat.div_def]
  grind [Rat.neg_mul, Rat.mul_neg, Rat.neg_neg, Rat.mul_assoc, Rat.mul_comm]

/-- The rational Jacobian of the compact projective coordinate is even. -/
theorem projectiveCompactJacobian_neg (x : Rat) :
    projectiveCompactJacobian (-x) = projectiveCompactJacobian x := by
  unfold projectiveCompactJacobian
  congr 2 <;>
    grind [Rat.neg_mul, Rat.mul_neg, Rat.neg_neg, Rat.mul_assoc, Rat.mul_comm]

/-- The clean compact reciprocal-quartic density is even.  This is the
finite symmetry needed to assemble the two projective chart branches. -/
theorem reciprocalQuarticSymmetricDensity_minus_one_even (x : Rat) :
    reciprocalQuarticSymmetricDensity (-1) (-x) =
      reciprocalQuarticSymmetricDensity (-1) x := by
  unfold reciprocalQuarticSymmetricDensity reciprocalQuarticKernel
    reciprocalQuarticDenominator
  congr 2 <;>
    grind [Rat.neg_mul, Rat.mul_neg, Rat.neg_neg, Rat.mul_assoc, Rat.mul_comm]

/-- The denominator of the compact projective chart is positive on its
open rational source interval. -/
theorem projectiveCompactDenominator_pos {x : Rat}
    (hxlo : -1 < x) (hxhi : x < 1) :
    0 < 1 - x * x := by
  have hleft : 0 < 1 - x := by grind
  have hright : 0 < 1 + x := by grind
  calc
    0 < (1 - x) * (1 + x) := Rat.mul_pos hleft hright
    _ = 1 - x * x := by
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.add_assoc,
        Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]

/-- The numerator controlling projective endpoint displacement is positive
when both rational endpoints lie in the open compact chart. -/
theorem projectiveCompactOneAddMul_pos {x y : Rat}
    (hxlo : -1 < x) (hxhi : x < 1)
    (hylo : -1 < y) (hyhi : y < 1) :
    0 < 1 + x * y := by
  by_cases hx0 : 0 <= x
  · by_cases hy0 : 0 <= y
    · have hxy : 0 <= x * y := Rat.mul_nonneg hx0 hy0
      grind
    · have hyneg : y < 0 := by grind
      have hypos : 0 < -y := by grind
      have hmul : x * (-y) < 1 * (-y) :=
        Rat.mul_lt_mul_of_pos_right hxhi hypos
      have hlt : y < x * y := by
        grind [Rat.mul_neg, Rat.neg_mul, Rat.neg_neg, Rat.mul_comm]
      grind
  · have hxneg : x < 0 := by grind
    by_cases hy0 : 0 <= y
    · have hxpos : 0 < -x := by grind
      have hmul : y * (-x) < 1 * (-x) :=
        Rat.mul_lt_mul_of_pos_right hyhi hxpos
      have hlt : x < x * y := by
        grind [Rat.mul_neg, Rat.neg_mul, Rat.neg_neg, Rat.mul_comm]
      grind
    · have hyneg : y < 0 := by grind
      have hxpos : 0 < -x := by grind
      have hypos : 0 < -y := by grind
      have hmul : 0 < (-x) * (-y) := Rat.mul_pos hxpos hypos
      have hxy : 0 < x * y := by
        grind [Rat.mul_neg, Rat.neg_mul, Rat.neg_neg]
      grind

/-- Denominator-cleared endpoint displacement for the compact projective
chart.  This is the finite rational identity used to transport an ordered
source partition through `x / (1 - x^2)`; the analytic change-of-variables
theorem still has to account for the removable chart endpoints. -/
theorem projectiveCompactCoordinate_sub_cleared
    (x y : Rat) (hx : 1 - x * x ≠ 0) (hy : 1 - y * y ≠ 0) :
    (projectiveCompactCoordinate y - projectiveCompactCoordinate x) *
        ((1 - y * y) * (1 - x * x)) =
      (y - x) * (1 + x * y) := by
  let dx : Rat := 1 - x * x
  let dy : Rat := 1 - y * y
  have hdx : dx ≠ 0 := by simpa [dx] using hx
  have hdy : dy ≠ 0 := by simpa [dy] using hy
  have hdx_cancel : dx * dx⁻¹ = 1 := Rat.mul_inv_cancel dx hdx
  have hdy_cancel : dy * dy⁻¹ = 1 := Rat.mul_inv_cancel dy hdy
  unfold projectiveCompactCoordinate
  change (y / dy - x / dx) * (dy * dx) = (y - x) * (1 + x * y)
  rw [Rat.div_def, Rat.div_def]
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.add_assoc,
    Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]

/-- The compact projective chart preserves the order of rational endpoints
in `(-1,1)`.  This finite theorem is the partition-order half of the
projective substitution route. -/
theorem projectiveCompactCoordinate_strictMono {x y : Rat}
    (hxlo : -1 < x) (hxy : x < y) (hyhi : y < 1) :
    projectiveCompactCoordinate x < projectiveCompactCoordinate y := by
  have hxhi : x < 1 := by grind
  have hylo : -1 < y := by grind
  have hdx : 0 < 1 - x * x := projectiveCompactDenominator_pos hxlo hxhi
  have hdy : 0 < 1 - y * y := projectiveCompactDenominator_pos hylo hyhi
  have hfactor : 0 < 1 + x * y :=
    projectiveCompactOneAddMul_pos hxlo hxhi hylo hyhi
  have hcleared := projectiveCompactCoordinate_sub_cleared x y
    (Rat.ne_of_gt hdx) (Rat.ne_of_gt hdy)
  have hright : 0 <
      (projectiveCompactCoordinate y - projectiveCompactCoordinate x) *
        ((1 - y * y) * (1 - x * x)) := by
    rw [hcleared]
    exact Rat.mul_pos (by grind) hfactor
  have hden : 0 < (1 - y * y) * (1 - x * x) := Rat.mul_pos hdy hdx
  have hlt : 0 < projectiveCompactCoordinate y - projectiveCompactCoordinate x := by
    apply Rat.lt_of_mul_lt_mul_right (c := (1 - y * y) * (1 - x * x))
      (hc := Rat.le_of_lt hden)
    calc
      0 * ((1 - y * y) * (1 - x * x)) = 0 := by rw [Rat.zero_mul]
      _ < (projectiveCompactCoordinate y - projectiveCompactCoordinate x) *
          ((1 - y * y) * (1 - x * x)) := hright
  grind

/-- Transport every endpoint of a finite rational partition through the
compact projective chart. -/
def projectiveCompactIntervals : List (Rat × Rat) -> List (Rat × Rat)
  | [] => []
  | (p, r) :: rest =>
      (projectiveCompactCoordinate p, projectiveCompactCoordinate r) ::
        projectiveCompactIntervals rest

/-- The compact projective chart is nonnegative on its nonnegative rational
source branch. -/
theorem projectiveCompactCoordinate_nonnegative {x : Rat}
    (hx0 : 0 <= x) (hx1 : x < 1) :
    0 <= projectiveCompactCoordinate x := by
  have hxlo : -1 < x := by grind
  have hden : 0 < 1 - x * x := projectiveCompactDenominator_pos hxlo hx1
  unfold projectiveCompactCoordinate
  rw [Rat.div_def]
  exact Rat.mul_nonneg hx0 (Rat.le_of_lt ((Rat.inv_pos).2 hden))

/-- An ordered finite cover of a compact rational subinterval of `(-1,1)`
remains an ordered cover after applying the compact projective chart to every
endpoint.  This is the finite partition transport needed before comparing
quadrature sums. -/
theorem projectiveCompactIntervals_covers
    (a b : Rat) (intervals : List (Rat × Rat))
    (ha : -1 < a) (hb : b < 1)
    (hcover : ArctanGeometry.CoversInterval a b intervals) :
    ArctanGeometry.CoversInterval
      (projectiveCompactCoordinate a) (projectiveCompactCoordinate b)
      (projectiveCompactIntervals intervals) := by
  induction intervals generalizing a b with
  | nil =>
      simp [projectiveCompactIntervals, ArctanGeometry.CoversInterval] at hcover ⊢
      rw [hcover]
  | cons cell rest ih =>
      rcases cell with ⟨p, r⟩
      rcases hcover with ⟨hp, hpr, hrest⟩
      subst p
      have hrlo : -1 < r := by grind
      have hrle : r <= b := ArctanGeometry.CoversInterval.start_le_end hrest
      have hrhi : r < 1 := by grind
      have hmap : projectiveCompactCoordinate a <= projectiveCompactCoordinate r := by
        by_cases har : a = r
        · subst r
          exact Rat.le_refl
        · exact Rat.le_of_lt
            (projectiveCompactCoordinate_strictMono ha (by grind) hrhi)
      simp only [projectiveCompactIntervals, ArctanGeometry.CoversInterval]
      exact ⟨trivial, hmap, ih r b hrlo hb hrest⟩

/-- A nonnegative finite source partition transports to a nonnegative
partition on the positive branch of the compact projective chart.  This is
the admissibility condition for the existing Cauchy-kernel quadrature bounds.
-/
theorem projectiveCompactIntervals_nonnegative
    (a b : Rat) (intervals : List (Rat × Rat))
    (ha : 0 <= a) (hb : b < 1)
    (hcover : ArctanGeometry.CoversInterval a b intervals) :
    ArctanGeometry.NonnegativeIntervals (projectiveCompactIntervals intervals) := by
  induction intervals generalizing a b with
  | nil =>
      simp [projectiveCompactIntervals, ArctanGeometry.NonnegativeIntervals]
  | cons cell rest ih =>
      rcases cell with ⟨p, r⟩
      rcases hcover with ⟨hp, hpr, hrest⟩
      subst p
      have hr0 : 0 <= r := Rat.le_trans ha hpr
      have hrle : r <= b := ArctanGeometry.CoversInterval.start_le_end hrest
      have hrhi : r < 1 := by grind
      have hleft : 0 <= projectiveCompactCoordinate a :=
        projectiveCompactCoordinate_nonnegative ha (by grind)
      have horder : projectiveCompactCoordinate a <= projectiveCompactCoordinate r := by
        by_cases har : a = r
        · subst r
          exact Rat.le_refl
        · have halo : -1 < a := by grind
          exact Rat.le_of_lt
            (projectiveCompactCoordinate_strictMono halo (by grind) hrhi)
      simp only [projectiveCompactIntervals, ArctanGeometry.NonnegativeIntervals]
      exact ⟨hleft, horder, ih r b hr0 hb hrest⟩

/-- On a nonnegative compact source branch, the projective chart has the
explicit rational Lipschitz bound
`2 / (1 - s^2)^2` up to a rational endpoint `s < 1`. -/
theorem projectiveCompactCoordinate_sub_le_lipschitz
    {x y s : Rat}
    (hx0 : 0 <= x) (hxy : x <= y) (hys : y <= s) (hs : s < 1) :
    projectiveCompactCoordinate y - projectiveCompactCoordinate x <=
      (2 * (y - x)) / ((1 - s * s) * (1 - s * s)) := by
  let dx : Rat := 1 - x * x
  let dy : Rat := 1 - y * y
  let ds : Rat := 1 - s * s
  have hs0 : 0 <= s := Rat.le_trans (Rat.le_trans hx0 hxy) hys
  have hx1 : x < 1 := by grind
  have hy1 : y < 1 := by grind
  have hxlo : -1 < x := by grind
  have hylo : -1 < y := by grind
  have hslo : -1 < s := by grind
  have hdx : 0 < dx := by
    simpa [dx] using projectiveCompactDenominator_pos hxlo hx1
  have hdy : 0 < dy := by
    simpa [dy] using projectiveCompactDenominator_pos hylo hy1
  have hds : 0 < ds := by
    simpa [ds] using projectiveCompactDenominator_pos hslo hs
  have hxle : x <= s := Rat.le_trans hxy hys
  have hxx : x * x <= s * s := by
    calc
      x * x <= s * x := Rat.mul_le_mul_of_nonneg_right hxle hx0
      _ <= s * s := Rat.mul_le_mul_of_nonneg_left hxle hs0
  have hyy : y * y <= s * s := by
    calc
      y * y <= s * y :=
        Rat.mul_le_mul_of_nonneg_right hys (Rat.le_trans hx0 hxy)
      _ <= s * s := Rat.mul_le_mul_of_nonneg_left hys hs0
  have hdsdx : ds <= dx := by
    dsimp [ds, dx]
    grind
  have hdsdy : ds <= dy := by
    dsimp [ds, dy]
    grind
  have hden : ds * ds <= dy * dx := by
    calc
      ds * ds <= dy * ds :=
        Rat.mul_le_mul_of_nonneg_right hdsdy (Rat.le_of_lt hds)
      _ <= dy * dx := Rat.mul_le_mul_of_nonneg_left hdsdx (Rat.le_of_lt hdy)
  have hfactor : 1 + x * y <= 2 := by
    have hxle1 : x <= 1 := by grind
    have hxy_le_y : x * y <= 1 * y :=
      Rat.mul_le_mul_of_nonneg_right hxle1 (Rat.le_trans hx0 hxy)
    have hy1le : y <= 1 := by grind
    grind
  have hdiff : 0 <= y - x := by grind
  have hclear := projectiveCompactCoordinate_sub_cleared x y
    (Rat.ne_of_gt hdx) (Rat.ne_of_gt hdy)
  have hdenpos : 0 < dy * dx := Rat.mul_pos hdy hdx
  have hdelta : projectiveCompactCoordinate y - projectiveCompactCoordinate x =
      ((y - x) * (1 + x * y)) / (dy * dx) := by
    apply rat_eq_of_mul_eq_mul_ne (c := dy * dx) (Rat.ne_of_gt hdenpos)
    rw [Rat.div_def]
    have hcancel : (dy * dx)⁻¹ * (dy * dx) = 1 :=
      Rat.inv_mul_cancel _ (Rat.ne_of_gt hdenpos)
    calc
      (projectiveCompactCoordinate y - projectiveCompactCoordinate x) *
          (dy * dx) = (y - x) * (1 + x * y) := by
            simpa [dx, dy] using hclear
      _ = ((y - x) * (1 + x * y) * (dy * dx)⁻¹) * (dy * dx) := by
            grind [Rat.mul_assoc, Rat.mul_comm]
  have hinv : (dy * dx)⁻¹ <= (ds * ds)⁻¹ := by
    apply Rat.le_of_mul_le_mul_right (c := (ds * ds) * (dy * dx))
    · calc
        (dy * dx)⁻¹ * ((ds * ds) * (dy * dx)) = ds * ds := by
          have hcancel : (dy * dx)⁻¹ * (dy * dx) = 1 :=
            Rat.inv_mul_cancel _ (Rat.ne_of_gt hdenpos)
          grind [Rat.mul_assoc, Rat.mul_comm]
        _ <= dy * dx := hden
        _ = (ds * ds)⁻¹ * ((ds * ds) * (dy * dx)) := by
          have hss : ds * ds ≠ 0 := Rat.ne_of_gt (Rat.mul_pos hds hds)
          have hcancel : (ds * ds)⁻¹ * (ds * ds) = 1 :=
            Rat.inv_mul_cancel _ hss
          grind [Rat.mul_assoc, Rat.mul_comm]
    · exact Rat.mul_pos (Rat.mul_pos hds hds) hdenpos
  rw [hdelta]
  rw [Rat.div_def]
  calc
    (y - x) * (1 + x * y) * (dy * dx)⁻¹ <=
        (y - x) * 2 * (dy * dx)⁻¹ := by
      apply Rat.mul_le_mul_of_nonneg_right
        (Rat.mul_le_mul_of_nonneg_left hfactor hdiff)
      exact Rat.le_of_lt ((Rat.inv_pos).2 hdenpos)
    _ <= (y - x) * 2 * (ds * ds)⁻¹ :=
      Rat.mul_le_mul_of_nonneg_left hinv
        (Rat.mul_nonneg hdiff (by native_decide))
    _ = 2 * (y - x) * (ds * ds)⁻¹ := by
      grind [Rat.mul_assoc, Rat.mul_comm]

/-- The projective image of a nonnegative finite partition has a controlled
squared mesh.  The explicit factor is the square of the compact-branch
Lipschitz bound and is the finite estimate needed for transported quadrature
errors. -/
theorem projectiveCompactIntervals_squareSum_le
    (a s : Rat) (intervals : List (Rat × Rat))
    (ha : 0 <= a) (hs : s < 1)
    (hcover : ArctanGeometry.CoversInterval a s intervals) :
    ArctanGeometry.intervalSquareSum (projectiveCompactIntervals intervals) <=
      (2 / ((1 - s * s) * (1 - s * s))) *
        (2 / ((1 - s * s) * (1 - s * s))) *
          ArctanGeometry.intervalSquareSum intervals := by
  let L : Rat := 2 / ((1 - s * s) * (1 - s * s))
  have hs0 : 0 <= s :=
    Rat.le_trans ha (ArctanGeometry.CoversInterval.start_le_end hcover)
  have hslo : -1 < s := by grind
  have hds : 0 < 1 - s * s := projectiveCompactDenominator_pos hslo hs
  have hL : 0 <= L := by
    dsimp [L]
    rw [Rat.div_def]
    exact Rat.mul_nonneg (by native_decide)
      (Rat.le_of_lt ((Rat.inv_pos).2 (Rat.mul_pos hds hds)))
  change ArctanGeometry.intervalSquareSum (projectiveCompactIntervals intervals) <=
    L * L * ArctanGeometry.intervalSquareSum intervals
  induction intervals generalizing a with
  | nil =>
      simp [projectiveCompactIntervals, ArctanGeometry.intervalSquareSum]
  | cons cell rest ih =>
      rcases cell with ⟨p, r⟩
      rcases hcover with ⟨hp, hpr, hrest⟩
      subst p
      have hr0 : 0 <= r := Rat.le_trans ha hpr
      have hrs : r <= s := ArctanGeometry.CoversInterval.start_le_end hrest
      have hwidth :
          projectiveCompactCoordinate r - projectiveCompactCoordinate a <=
            L * (r - a) := by
        calc
          projectiveCompactCoordinate r - projectiveCompactCoordinate a <=
              (2 * (r - a)) / ((1 - s * s) * (1 - s * s)) :=
            projectiveCompactCoordinate_sub_le_lipschitz ha hpr hrs hs
          _ = L * (r - a) := by
            dsimp [L]
            rw [Rat.div_def]
            grind [Rat.mul_assoc, Rat.mul_comm]
      have hsource : 0 <= r - a := by grind
      have horder : projectiveCompactCoordinate a <= projectiveCompactCoordinate r := by
        by_cases har : a = r
        · subst r
          exact Rat.le_refl
        · have halo : -1 < a := by grind
          have hr1 : r < 1 := by grind
          exact Rat.le_of_lt
            (projectiveCompactCoordinate_strictMono halo (by grind) hr1)
      have himage : 0 <=
          projectiveCompactCoordinate r - projectiveCompactCoordinate a := by grind
      have hscaled : 0 <= L * (r - a) := Rat.mul_nonneg hL hsource
      have hcell :
          (projectiveCompactCoordinate r - projectiveCompactCoordinate a) *
              (projectiveCompactCoordinate r - projectiveCompactCoordinate a) <=
            L * L * ((r - a) * (r - a)) := by
        calc
          (projectiveCompactCoordinate r - projectiveCompactCoordinate a) *
              (projectiveCompactCoordinate r - projectiveCompactCoordinate a) <=
            (L * (r - a)) *
              (projectiveCompactCoordinate r - projectiveCompactCoordinate a) := by
              exact Rat.mul_le_mul_of_nonneg_right hwidth himage
          _ <= (L * (r - a)) * (L * (r - a)) := by
              exact Rat.mul_le_mul_of_nonneg_left hwidth hscaled
          _ = L * L * ((r - a) * (r - a)) := by
              grind [Rat.mul_assoc, Rat.mul_comm]
      have htail := ih r hr0 hrest
      simp only [projectiveCompactIntervals, ArctanGeometry.intervalSquareSum]
      calc
        (projectiveCompactCoordinate r - projectiveCompactCoordinate a) *
              (projectiveCompactCoordinate r - projectiveCompactCoordinate a) +
            ArctanGeometry.intervalSquareSum (projectiveCompactIntervals rest) <=
          L * L * ((r - a) * (r - a)) +
            L * L * ArctanGeometry.intervalSquareSum rest := by grind
        _ = L * L * ((r - a) * (r - a) +
              ArctanGeometry.intervalSquareSum rest) := by
              grind [Rat.mul_add, Rat.mul_assoc]

/-- The standard midpoint-dyadic partition of a compact positive source
branch has an explicit transported squared-mesh bound. -/
theorem projectiveCompactAreaLoop_squareSum_le
    {s : Rat} (hs0 : 0 <= s) (hs : s < 1) (n : Nat) :
    ArctanGeometry.intervalSquareSum
      (projectiveCompactIntervals
        (ArctanGeometry.arctanAreaLoopState s n).intervals) <=
      (2 / ((1 - s * s) * (1 - s * s))) *
        (2 / ((1 - s * s) * (1 - s * s))) *
          (s * s / (((2 ^ n : Nat) : Rat))) := by
  calc
    ArctanGeometry.intervalSquareSum
        (projectiveCompactIntervals
          (ArctanGeometry.arctanAreaLoopState s n).intervals) <=
        (2 / ((1 - s * s) * (1 - s * s))) *
          (2 / ((1 - s * s) * (1 - s * s))) *
            ArctanGeometry.intervalSquareSum
              (ArctanGeometry.arctanAreaLoopState s n).intervals :=
      projectiveCompactIntervals_squareSum_le 0 s
        (ArctanGeometry.arctanAreaLoopState s n).intervals (by native_decide) hs
        (ArctanGeometry.arctanAreaLoopState_intervals_covers hs0 n)
    _ = (2 / ((1 - s * s) * (1 - s * s))) *
          (2 / ((1 - s * s) * (1 - s * s))) *
            (s * s / (((2 ^ n : Nat) : Rat))) := by
      rw [ArctanGeometry.arctanAreaLoopState_squareSum]

/-- The compact source endpoint used by the projective quadrature schedule.
At stage `n` it stops one dyadic unit short of the chart pole. -/
def projectiveCompactDyadicEndpoint (n : Nat) : Rat :=
  1 - 1 / (((2 ^ n : Nat) : Rat))

/-- The dyadic projective schedule remains on the nonnegative compact branch. -/
theorem projectiveCompactDyadicEndpoint_nonnegative (n : Nat) :
    0 <= projectiveCompactDyadicEndpoint n := by
  let D : Rat := ((2 ^ n : Nat) : Rat)
  have hDpos : 0 < D := by
    dsimp [D]
    exact (Rat.natCast_pos).2 (Nat.pow_pos (by omega : 0 < 2))
  have hDge : 1 <= D := by
    dsimp [D]
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr
      (Nat.ne_of_gt (Nat.pow_pos (by omega : 0 < 2))))
  have hinv : D⁻¹ <= 1 := by
    apply Rat.le_of_mul_le_mul_right (c := D)
    · calc
        D⁻¹ * D = 1 := Rat.inv_mul_cancel _ (Rat.ne_of_gt hDpos)
        _ <= 1 * D := by simpa using hDge
    · exact hDpos
  unfold projectiveCompactDyadicEndpoint
  rw [Rat.div_def]
  dsimp [D] at hinv
  grind [Rat.sub_eq_add_neg]

/-- The dyadic projective schedule stays strictly below the chart pole. -/
theorem projectiveCompactDyadicEndpoint_lt_one (n : Nat) :
    projectiveCompactDyadicEndpoint n < 1 := by
  let D : Rat := ((2 ^ n : Nat) : Rat)
  have hDpos : 0 < D := by
    dsimp [D]
    exact (Rat.natCast_pos).2 (Nat.pow_pos (by omega : 0 < 2))
  unfold projectiveCompactDyadicEndpoint
  rw [Rat.div_def]
  have hinv : 0 < D⁻¹ := (Rat.inv_pos).2 hDpos
  dsimp [D] at hinv
  grind [Rat.sub_eq_add_neg]

/-- At the dyadic endpoint, the projective denominator retains at least one
dyadic unit of clearance from zero. -/
theorem projectiveCompactDyadicEndpoint_denominator_ge (n : Nat) :
    1 / (((2 ^ n : Nat) : Rat)) <=
      1 - projectiveCompactDyadicEndpoint n * projectiveCompactDyadicEndpoint n := by
  let t : Rat := 1 / (((2 ^ n : Nat) : Rat))
  have htpos : 0 < t := by
    dsimp [t]
    rw [Rat.div_def]
    exact Rat.mul_pos (by native_decide)
      ((Rat.inv_pos).2 ((Rat.natCast_pos).2 (Nat.pow_pos (by omega : 0 < 2))))
  have htone : t <= 1 := by
    change 1 / (((2 ^ n : Nat) : Rat)) <= 1
    let D : Rat := ((2 ^ n : Nat) : Rat)
    have hDpos : 0 < D := by
      dsimp [D]
      exact (Rat.natCast_pos).2 (Nat.pow_pos (by omega : 0 < 2))
    have hDge : 1 <= D := by
      dsimp [D]
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr
        (Nat.ne_of_gt (Nat.pow_pos (by omega : 0 < 2))))
    rw [Rat.div_def]
    apply Rat.le_of_mul_le_mul_right (c := D)
    · calc
        (1 * D⁻¹) * D = 1 := by
          rw [Rat.mul_assoc, Rat.inv_mul_cancel _ (Rat.ne_of_gt hDpos), Rat.mul_one]
        _ <= 1 * D := by simpa using hDge
    · exact hDpos
  have hfactor : 1 <= 2 - t := by grind
  have hmul : t * 1 <= t * (2 - t) :=
    Rat.mul_le_mul_of_nonneg_left hfactor (Rat.le_of_lt htpos)
  change t <= 1 - (1 - t) * (1 - t)
  calc
    t = t * 1 := by grind
    _ <= t * (2 - t) := hmul
    _ = 1 - (1 - t) * (1 - t) := by
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.mul_assoc,
        Rat.mul_comm]

/-- The remaining endpoint cell in the dyadic projective schedule has an
explicit vanishing compact-density tail budget. -/
theorem projectiveCompactDyadicTailUpperCell_le (n : Nat) :
    projectiveCompactTailUpperCell (projectiveCompactDyadicEndpoint n) <=
      ((32 : Rat) / 3) * (1 / (((2 ^ n : Nat) : Rat))) := by
  have hs0 : 0 <= projectiveCompactDyadicEndpoint n :=
    projectiveCompactDyadicEndpoint_nonnegative n
  have hs1 : projectiveCompactDyadicEndpoint n <= 1 :=
    Rat.le_of_lt (projectiveCompactDyadicEndpoint_lt_one n)
  have htail := projectiveCompactTailUpperCell_le hs0 hs1
  calc
    projectiveCompactTailUpperCell (projectiveCompactDyadicEndpoint n) <=
        ((32 : Rat) / 3) * (1 - projectiveCompactDyadicEndpoint n) := htail
    _ = ((32 : Rat) / 3) * (1 / (((2 ^ n : Nat) : Rat))) := by
      dsimp [projectiveCompactDyadicEndpoint]
      grind [Rat.sub_eq_add_neg]

private theorem projectiveCompact_one_div_le_one_div_of_pos_of_le {a b : Rat}
    (ha : 0 < a) (hab : a <= b) :
    1 / b <= 1 / a := by
  have hb : 0 < b := by grind
  have hane : a ≠ 0 := Rat.ne_of_gt ha
  have hbne : b ≠ 0 := Rat.ne_of_gt hb
  have hprod : 0 < a * b := Rat.mul_pos ha hb
  apply Rat.le_of_mul_le_mul_right (c := a * b)
  · calc
      (1 / b) * (a * b) = a := by
        rw [Rat.div_def]
        have hcancel : b * b⁻¹ = 1 := Rat.mul_inv_cancel b hbne
        grind [Rat.mul_assoc, Rat.mul_comm]
      _ <= b := hab
      _ = (1 / a) * (a * b) := by
        rw [Rat.div_def]
        have hcancel : a * a⁻¹ = 1 := Rat.mul_inv_cancel a hane
        grind [Rat.mul_assoc, Rat.mul_comm]
  · exact hprod

/-- The projective Lipschitz coefficient along the dyadic endpoint schedule
has a purely dyadic upper bound. -/
theorem projectiveCompactDyadic_lipschitzFactor_le (n : Nat) :
    2 / ((1 - projectiveCompactDyadicEndpoint n *
      projectiveCompactDyadicEndpoint n) *
        (1 - projectiveCompactDyadicEndpoint n *
          projectiveCompactDyadicEndpoint n)) <=
      2 * (((2 ^ n : Nat) : Rat)) * (((2 ^ n : Nat) : Rat)) := by
  let D : Rat := ((2 ^ n : Nat) : Rat)
  let t : Rat := 1 / D
  let d : Rat := 1 - projectiveCompactDyadicEndpoint n *
    projectiveCompactDyadicEndpoint n
  have hDpos : 0 < D := by
    dsimp [D]
    exact (Rat.natCast_pos).2 (Nat.pow_pos (by omega : 0 < 2))
  have htpos : 0 < t := by
    dsimp [t]
    rw [Rat.div_def]
    exact Rat.mul_pos (by native_decide) ((Rat.inv_pos).2 hDpos)
  have htd : t <= d := by
    simpa [t, d, D] using projectiveCompactDyadicEndpoint_denominator_ge n
  have hdpos : 0 < d := by grind
  have hsq : t * t <= d * d := by
    calc
      t * t <= d * t := Rat.mul_le_mul_of_nonneg_right htd (Rat.le_of_lt htpos)
      _ <= d * d := Rat.mul_le_mul_of_nonneg_left htd (Rat.le_of_lt hdpos)
  have hsqpos : 0 < t * t := Rat.mul_pos htpos htpos
  have hinv : 1 / (d * d) <= 1 / (t * t) :=
    projectiveCompact_one_div_le_one_div_of_pos_of_le hsqpos hsq
  have htinv : 1 / (t * t) = D * D := by
    dsimp [t]
    rw [Rat.div_def, Rat.div_def]
    have hcancel : D⁻¹ * D = 1 := Rat.inv_mul_cancel _ (Rat.ne_of_gt hDpos)
    grind [Rat.mul_assoc, Rat.mul_comm]
  change 2 / (d * d) <= 2 * D * D
  rw [Rat.div_def]
  calc
    2 * (d * d)⁻¹ = 2 * (1 / (d * d)) := by
      simp [Rat.div_def]
    _ <= 2 * (1 / (t * t)) :=
      Rat.mul_le_mul_of_nonneg_left hinv (by native_decide)
    _ = 2 * D * D := by
      rw [htinv]
      grind [Rat.mul_assoc]

private theorem projectiveCompact_dyadic_mesh_algebra
    (D : Rat) (hD : D ≠ 0) :
    (2 * D * D) * (2 * D * D) * (1 / (D ^ 6)) = 4 / (D ^ 2) := by
  have hcancel : D * D⁻¹ = 1 := Rat.mul_inv_cancel D hD
  simp only [Rat.pow_succ, Rat.pow_zero, Rat.div_def, Rat.inv_mul_rev, Rat.one_mul]
  grind [Rat.mul_assoc, Rat.mul_comm]

/-- An explicit projective quadrature schedule whose transported squared mesh
shrinks at the dyadic rate `4 / 2^(2n)`.  The source endpoint is
`1 - 2^(-n)` and the source partition receives `6n` midpoint refinements,
which absorbs the fourth-order blowup of the chart derivative near its pole. -/
theorem projectiveCompactDyadic_schedule_squareSum_le (n : Nat) :
    ArctanGeometry.intervalSquareSum
      (projectiveCompactIntervals
        (ArctanGeometry.arctanAreaLoopState
          (projectiveCompactDyadicEndpoint n) (n * 6)).intervals) <=
      4 / (((2 ^ (n * 2) : Nat) : Rat)) := by
  let s : Rat := projectiveCompactDyadicEndpoint n
  let D : Rat := ((2 ^ n : Nat) : Rat)
  let d : Rat := 1 - s * s
  let L : Rat := 2 / (d * d)
  let R : Rat := 2 * D * D
  let Q : Rat := ((2 ^ (n * 6) : Nat) : Rat)
  have hs0 : 0 <= s := by
    simpa [s] using projectiveCompactDyadicEndpoint_nonnegative n
  have hslt : s < 1 := by
    simpa [s] using projectiveCompactDyadicEndpoint_lt_one n
  have hsone : s <= 1 := Rat.le_of_lt hslt
  have hd : 0 < d := by
    dsimp [d, s]
    exact projectiveCompactDenominator_pos (by grind) hslt
  have hL0 : 0 <= L := by
    dsimp [L]
    rw [Rat.div_def]
    exact Rat.mul_nonneg (by native_decide)
      (Rat.le_of_lt ((Rat.inv_pos).2 (Rat.mul_pos hd hd)))
  have hDpos : 0 < D := by
    dsimp [D]
    exact (Rat.natCast_pos).2 (Nat.pow_pos (by omega : 0 < 2))
  have hR0 : 0 <= R := by
    dsimp [R]
    exact Rat.mul_nonneg (Rat.mul_nonneg (by native_decide) (Rat.le_of_lt hDpos))
      (Rat.le_of_lt hDpos)
  have hLle : L <= R := by
    simpa [L, d, s, R, D] using projectiveCompactDyadic_lipschitzFactor_le n
  have hLL : L * L <= R * R := by
    calc
      L * L <= R * L := Rat.mul_le_mul_of_nonneg_right hLle hL0
      _ <= R * R := Rat.mul_le_mul_of_nonneg_left hLle hR0
  have hsq0 : 0 <= s * s := Rat.mul_nonneg hs0 hs0
  have hsqle : s * s <= 1 := by
    calc
      s * s <= 1 * s := Rat.mul_le_mul_of_nonneg_right hsone hs0
      _ <= 1 := by grind
  have hQpos : 0 < Q := by
    dsimp [Q]
    exact (Rat.natCast_pos).2 (Nat.pow_pos (by omega : 0 < 2))
  have hsource : 0 <= s * s / Q := by
    rw [Rat.div_def]
    exact Rat.mul_nonneg hsq0 (Rat.le_of_lt ((Rat.inv_pos).2 hQpos))
  have hquot : s * s / Q <= 1 / Q := by
    rw [Rat.div_def, Rat.div_def]
    exact Rat.mul_le_mul_of_nonneg_right hsqle
      (Rat.le_of_lt ((Rat.inv_pos).2 hQpos))
  have hpow6 : Q = D ^ 6 := by
    dsimp [Q, D]
    exact_mod_cast (Nat.pow_mul 2 n 6)
  have hpow2 : (((2 ^ (n * 2) : Nat) : Rat)) = D ^ 2 := by
    dsimp [D]
    exact_mod_cast (Nat.pow_mul 2 n 2)
  have hbase := projectiveCompactAreaLoop_squareSum_le hs0 hslt (n * 6)
  calc
    ArctanGeometry.intervalSquareSum
        (projectiveCompactIntervals
          (ArctanGeometry.arctanAreaLoopState
            (projectiveCompactDyadicEndpoint n) (n * 6)).intervals) =
        ArctanGeometry.intervalSquareSum
          (projectiveCompactIntervals
            (ArctanGeometry.arctanAreaLoopState s (n * 6)).intervals) := by
          rfl
    _ <= L * L * (s * s / Q) := by
      simpa [L, d, Q] using hbase
    _ <= R * R * (s * s / Q) :=
      Rat.mul_le_mul_of_nonneg_right hLL hsource
    _ <= R * R * (1 / Q) :=
      Rat.mul_le_mul_of_nonneg_left hquot (Rat.mul_nonneg hR0 hR0)
    _ = 4 / (((2 ^ (n * 2) : Nat) : Rat)) := by
      rw [hpow6, hpow2]
      exact projectiveCompact_dyadic_mesh_algebra D (Rat.ne_of_gt hDpos)

/-- Exact left-endpoint secant expansion for the compact projective chart.
The displayed remainder is nonnegative on the positive compact branch, so
this is the finite rational replacement for the lower derivative bound used
in a change-of-variables argument. -/
theorem projectiveCompactCoordinate_sub_eq_leftJacobian_add
    (p r : Rat) (hp : 1 - p * p ≠ 0) (hr : 1 - r * r ≠ 0) :
    projectiveCompactCoordinate r - projectiveCompactCoordinate p =
      projectiveCompactJacobian p * (r - p) +
        ((r - p) * (r - p) *
          (3 * p + p * p * p + (r - p) * (1 + p * p))) /
          (((1 - p * p) * (1 - p * p)) * (1 - r * r)) := by
  let dp : Rat := 1 - p * p
  let dr : Rat := 1 - r * r
  let E : Rat := 3 * p + p * p * p + (r - p) * (1 + p * p)
  have hdp : dp ≠ 0 := by simpa [dp] using hp
  have hdr : dr ≠ 0 := by simpa [dr] using hr
  have hdp2 : dp * dp ≠ 0 := by
    intro hzero
    rcases Rat.mul_eq_zero.mp hzero with hzero | hzero
    · exact hdp hzero
    · exact hdp hzero
  have hden : dp * dp * dr ≠ 0 := by
    intro hzero
    rcases Rat.mul_eq_zero.mp hzero with hzero | hzero
    · rcases Rat.mul_eq_zero.mp hzero with hzero | hzero
      · exact hdp hzero
      · exact hdp hzero
    · exact hdr hzero
  have hdp_cancel : dp * dp⁻¹ = 1 := Rat.mul_inv_cancel dp hdp
  have hdr_cancel : dr * dr⁻¹ = 1 := Rat.mul_inv_cancel dr hdr
  have hdp2_cancel : (dp * dp) * (dp * dp)⁻¹ = 1 :=
    Rat.mul_inv_cancel _ hdp2
  have hden_cancel : (dp * dp * dr) * (dp * dp * dr)⁻¹ = 1 :=
    Rat.mul_inv_cancel _ hden
  have hcleared : (r / dr - p / dp) * (dr * dp) =
      (r - p) * (1 + p * r) := by
    simpa [projectiveCompactCoordinate, dp, dr] using
      projectiveCompactCoordinate_sub_cleared p r hp hr
  have hpoly : (1 + p * r) * dp = (1 + p * p) * dr + (r - p) * E := by
    dsimp [dp, dr, E]
    grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.add_assoc,
      Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
  have hright :
      (((1 + p * p) / (dp * dp)) * (r - p) +
        ((r - p) * (r - p) * E) / (dp * dp * dr)) * (dp * dp * dr) =
        ((1 + p * p) * dr) * (r - p) + (r - p) * (r - p) * E := by
    simp only [Rat.div_def]
    grind [Rat.mul_add, Rat.add_mul, Rat.add_assoc, Rat.add_comm,
      Rat.mul_assoc, Rat.mul_comm]
  unfold projectiveCompactCoordinate projectiveCompactJacobian
  change r / dr - p / dp =
    ((1 + p * p) / (dp * dp)) * (r - p) +
      ((r - p) * (r - p) * E) /
        (dp * dp * dr)
  apply rat_eq_of_mul_eq_mul_ne (c := dp * dp * dr) hden
  calc
    (r / dr - p / dp) * (dp * dp * dr) =
        ((r / dr - p / dp) * (dr * dp)) * dp := by
          grind [Rat.mul_assoc, Rat.mul_comm]
    _ = ((r - p) * (1 + p * r)) * dp := by rw [hcleared]
    _ = (r - p) * ((1 + p * r) * dp) := by rw [Rat.mul_assoc]
    _ = (r - p) * ((1 + p * p) * dr + (r - p) * E) := by rw [hpoly]
    _ = ((1 + p * p) * dr) * (r - p) + (r - p) * (r - p) * E := by
      grind [Rat.mul_add, Rat.add_mul, Rat.add_assoc, Rat.add_comm,
        Rat.mul_assoc, Rat.mul_comm]
    _ = (((1 + p * p) / (dp * dp)) * (r - p) +
        ((r - p) * (r - p) * E) / (dp * dp * dr)) * (dp * dp * dr) :=
      hright.symm

/-- On the nonnegative compact chart branch, the projective secant is at
least its left endpoint Jacobian times the source-cell width. -/
theorem projectiveCompactJacobian_left_mul_le_coordinate_sub
    {p r : Rat} (hp0 : 0 <= p) (hpr : p <= r) (hr1 : r < 1) :
    projectiveCompactJacobian p * (r - p) <=
      projectiveCompactCoordinate r - projectiveCompactCoordinate p := by
  have hp1 : p < 1 := by grind
  have hplo : -1 < p := by grind
  have hrlo : -1 < r := by grind
  have hdp : 0 < 1 - p * p := projectiveCompactDenominator_pos hplo hp1
  have hdr : 0 < 1 - r * r := projectiveCompactDenominator_pos hrlo hr1
  have hwidth : 0 <= r - p := by grind
  have hfactor : 0 <=
      3 * p + p * p * p + (r - p) * (1 + p * p) := by
    have hp3 : 0 <= p * p * p :=
      Rat.mul_nonneg (Rat.mul_nonneg hp0 hp0) hp0
    have htail : 0 <= (r - p) * (1 + p * p) :=
      Rat.mul_nonneg hwidth (by
        have hsq : 0 <= p * p := Rat.mul_nonneg hp0 hp0
        grind)
    exact Rat.add_nonneg (Rat.add_nonneg (Rat.mul_nonneg (by native_decide) hp0) hp3)
      htail
  have hrem : 0 <=
      ((r - p) * (r - p) *
        (3 * p + p * p * p + (r - p) * (1 + p * p))) /
        (((1 - p * p) * (1 - p * p)) * (1 - r * r)) := by
    rw [Rat.div_def]
    apply Rat.mul_nonneg
    · exact Rat.mul_nonneg (Rat.mul_nonneg hwidth hwidth) hfactor
    · exact Rat.le_of_lt ((Rat.inv_pos).2
        (Rat.mul_pos (Rat.mul_pos hdp hdp) hdr))
  rw [projectiveCompactCoordinate_sub_eq_leftJacobian_add p r
    (Rat.ne_of_gt hdp) (Rat.ne_of_gt hdr)]
  grind [Rat.sub_eq_add_neg]

/-- Exact right-endpoint secant expansion for the compact projective chart.
Its remainder is again nonnegative on the positive compact branch. -/
theorem projectiveCompactCoordinate_sub_eq_rightJacobian_sub
    (p r : Rat) (hp : 1 - p * p ≠ 0) (hr : 1 - r * r ≠ 0) :
    projectiveCompactCoordinate r - projectiveCompactCoordinate p =
      projectiveCompactJacobian r * (r - p) -
        ((r - p) * (r - p) *
          (3 * r + r * r * r - (r - p) * (1 + r * r))) /
          (((1 - p * p) * (1 - r * r)) * (1 - r * r)) := by
  let dp : Rat := 1 - p * p
  let dr : Rat := 1 - r * r
  let E : Rat := 3 * r + r * r * r - (r - p) * (1 + r * r)
  have hdp : dp ≠ 0 := by simpa [dp] using hp
  have hdr : dr ≠ 0 := by simpa [dr] using hr
  have hdr2 : dr * dr ≠ 0 := by
    intro hzero
    rcases Rat.mul_eq_zero.mp hzero with hzero | hzero
    · exact hdr hzero
    · exact hdr hzero
  have hden : dp * dr * dr ≠ 0 := by
    intro hzero
    rcases Rat.mul_eq_zero.mp hzero with hzero | hzero
    · rcases Rat.mul_eq_zero.mp hzero with hzero | hzero
      · exact hdp hzero
      · exact hdr hzero
    · exact hdr hzero
  have hdp_cancel : dp * dp⁻¹ = 1 := Rat.mul_inv_cancel dp hdp
  have hdr_cancel : dr * dr⁻¹ = 1 := Rat.mul_inv_cancel dr hdr
  have hdr2_cancel : (dr * dr) * (dr * dr)⁻¹ = 1 :=
    Rat.mul_inv_cancel _ hdr2
  have hden_cancel : (dp * dr * dr) * (dp * dr * dr)⁻¹ = 1 :=
    Rat.mul_inv_cancel _ hden
  have hcleared : (r / dr - p / dp) * (dr * dp) =
      (r - p) * (1 + p * r) := by
    simpa [projectiveCompactCoordinate, dp, dr] using
      projectiveCompactCoordinate_sub_cleared p r hp hr
  have hpoly : (1 + p * r) * dr = (1 + r * r) * dp - (r - p) * E := by
    dsimp [dp, dr, E]
    grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.add_assoc,
      Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
  have hright :
      (((1 + r * r) / (dr * dr)) * (r - p) -
        ((r - p) * (r - p) * E) / (dp * dr * dr)) * (dp * dr * dr) =
        ((1 + r * r) * dp) * (r - p) - (r - p) * (r - p) * E := by
    simp only [Rat.div_def]
    grind [Rat.mul_add, Rat.add_mul, Rat.sub_eq_add_neg, Rat.add_assoc,
      Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
  unfold projectiveCompactCoordinate projectiveCompactJacobian
  change r / dr - p / dp =
    ((1 + r * r) / (dr * dr)) * (r - p) -
      ((r - p) * (r - p) * E) /
        (dp * dr * dr)
  apply rat_eq_of_mul_eq_mul_ne (c := dp * dr * dr) hden
  calc
    (r / dr - p / dp) * (dp * dr * dr) =
        ((r / dr - p / dp) * (dr * dp)) * dr := by
          grind [Rat.mul_assoc, Rat.mul_comm]
    _ = ((r - p) * (1 + p * r)) * dr := by rw [hcleared]
    _ = (r - p) * ((1 + p * r) * dr) := by rw [Rat.mul_assoc]
    _ = (r - p) * ((1 + r * r) * dp - (r - p) * E) := by rw [hpoly]
    _ = ((1 + r * r) * dp) * (r - p) - (r - p) * (r - p) * E := by
      grind [Rat.mul_add, Rat.add_mul, Rat.sub_eq_add_neg, Rat.add_assoc,
        Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
    _ = (((1 + r * r) / (dr * dr)) * (r - p) -
        ((r - p) * (r - p) * E) / (dp * dr * dr)) * (dp * dr * dr) :=
      hright.symm

/-- On the nonnegative compact chart branch, the projective secant is at
most its right endpoint Jacobian times the source-cell width. -/
theorem coordinate_sub_le_projectiveCompactJacobian_right_mul
    {p r : Rat} (hp0 : 0 <= p) (hpr : p <= r) (hr1 : r < 1) :
    projectiveCompactCoordinate r - projectiveCompactCoordinate p <=
      projectiveCompactJacobian r * (r - p) := by
  have hp1 : p < 1 := by grind
  have hplo : -1 < p := by grind
  have hrlo : -1 < r := by grind
  have hdp : 0 < 1 - p * p := projectiveCompactDenominator_pos hplo hp1
  have hdr : 0 < 1 - r * r := projectiveCompactDenominator_pos hrlo hr1
  have hwidth : 0 <= r - p := by grind
  have hwidth_le_r : r - p <= r := by grind
  have hr2 : 0 <= r * r := Rat.mul_nonneg (Rat.le_trans hp0 hpr)
    (Rat.le_trans hp0 hpr)
  have hrightFactor : 0 <=
      3 * r + r * r * r - (r - p) * (1 + r * r) := by
    have hr0 : 0 <= r := Rat.le_trans hp0 hpr
    have hmul : (r - p) * (1 + r * r) <= r * (1 + r * r) :=
      Rat.mul_le_mul_of_nonneg_right hwidth_le_r (by grind)
    calc
      0 <= 2 * r := Rat.mul_nonneg (by native_decide) hr0
      _ = (3 * r + r * r * r) - r * (1 + r * r) := by
        grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.mul_assoc,
          Rat.mul_comm]
      _ <= (3 * r + r * r * r) - (r - p) * (1 + r * r) := by
        grind [Rat.sub_eq_add_neg]
  have hrem : 0 <=
      ((r - p) * (r - p) *
        (3 * r + r * r * r - (r - p) * (1 + r * r))) /
        (((1 - p * p) * (1 - r * r)) * (1 - r * r)) := by
    rw [Rat.div_def]
    apply Rat.mul_nonneg
    · exact Rat.mul_nonneg (Rat.mul_nonneg hwidth hwidth) hrightFactor
    · exact Rat.le_of_lt ((Rat.inv_pos).2
        (Rat.mul_pos (Rat.mul_pos hdp hdr) hdr))
  rw [projectiveCompactCoordinate_sub_eq_rightJacobian_sub p r
    (Rat.ne_of_gt hdp) (Rat.ne_of_gt hdr)]
  grind [Rat.sub_eq_add_neg]

/-- Exact rational compactification of the Cauchy density.  Away from the
two chart endpoints, the pullback of `1 / (1 + u^2)` under
`u = x / (1 - x^2)` is the everywhere-defined density
`(1 + x^2) / (x^4 - x^2 + 1)`.  This is the finite algebraic core of the
reciprocal-quartic pi route; endpoint and integral certificates remain
separate analytic work. -/
theorem reciprocalQuarticSymmetricDensity_minus_one_eq_projectiveCompactPullback
    (x : Rat) (hx : 1 - x * x ≠ 0) :
    reciprocalQuarticSymmetricDensity (-1) x =
      projectiveCompactJacobian x *
        ArctanGeometry.integralKernel (projectiveCompactCoordinate x) := by
  let d : Rat := 1 - x * x
  let q : Rat := reciprocalQuarticDenominator (-1) x
  have hd : d ≠ 0 := by simpa [d] using hx
  have hd2 : d * d ≠ 0 := by
    intro hzero
    rcases Rat.mul_eq_zero.mp hzero with hzero | hzero
    · exact hd hzero
    · exact hd hzero
  have hden : 1 + (x / d) * (x / d) = q / (d * d) := by
    apply rat_eq_of_mul_eq_mul_ne (c := d * d) hd2
    rw [Rat.div_def]
    calc
      (1 + (x / d) * (x / d)) * (d * d) = d * d + x * x := by
        have hcancel : d * d⁻¹ = 1 := Rat.mul_inv_cancel d hd
        grind [Rat.mul_add, Rat.add_mul, Rat.add_assoc, Rat.add_comm,
          Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
      _ = q := by
        dsimp [d, q, reciprocalQuarticDenominator]
        grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.add_assoc,
          Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
      _ = q * (d * d)⁻¹ * (d * d) := by
        have hcancel : (d * d) * (d * d)⁻¹ = 1 :=
          Rat.mul_inv_cancel (d * d) hd2
        grind [Rat.mul_assoc, Rat.mul_comm]
  have hkernel : ArctanGeometry.integralKernel (x / d) = (d * d) / q := by
    unfold ArctanGeometry.integralKernel
    rw [hden]
    simp only [Rat.div_def, Rat.inv_mul_rev, Rat.inv_inv, Rat.one_mul]
  have hkernel' :
      ArctanGeometry.integralKernel (x / (1 - x * x)) =
        ((1 - x * x) * (1 - x * x)) /
          reciprocalQuarticDenominator (-1) x := by
    simpa [d, q] using hkernel
  unfold reciprocalQuarticSymmetricDensity reciprocalQuarticKernel
    projectiveCompactJacobian projectiveCompactCoordinate
  rw [hkernel']
  rw [Rat.div_def, Rat.div_def, Rat.div_def]
  have hcancel : (d * d)⁻¹ * (d * d) = 1 := by
    rw [Rat.mul_comm]
    exact Rat.mul_inv_cancel (d * d) hd2
  grind [Rat.mul_assoc, Rat.mul_comm]

/-- The lower Lipschitz rectangle for the compact reciprocal-quartic density
on a positive chart cell lies below the upper Cauchy-kernel rectangle on its
projective image.  This is a cellwise, finite rational half of the projective
quadrature comparison. -/
theorem projectiveCompact_lipschitzLowerCell_le_integralUpperStep
    {p r : Rat} (hp0 : 0 <= p) (hpr : p <= r) (hr1 : r < 1) :
    (r - p) *
      (reciprocalQuarticSymmetricDensity (-1) p - 8 * (r - p)) <=
      ArctanGeometry.integralUpperStep
        (projectiveCompactCoordinate p) (projectiveCompactCoordinate r) := by
  have hp1 : p < 1 := by grind
  have hplo : -1 < p := by grind
  have hrlo : -1 < r := by grind
  have hdp : 0 < 1 - p * p := projectiveCompactDenominator_pos hplo hp1
  have hwidth : 0 <= r - p := by grind
  have hsub : reciprocalQuarticSymmetricDensity (-1) p - 8 * (r - p) <=
      reciprocalQuarticSymmetricDensity (-1) p := by
    have herror : 0 <= 8 * (r - p) :=
      Rat.mul_nonneg (by native_decide) hwidth
    grind [Rat.sub_eq_add_neg]
  have hkernel : 0 <=
      ArctanGeometry.integralKernel (projectiveCompactCoordinate p) :=
    Rat.le_of_lt (ArctanGeometry.integralKernel_pos _)
  have hsecant :=
    projectiveCompactJacobian_left_mul_le_coordinate_sub hp0 hpr hr1
  have hpullback :=
    reciprocalQuarticSymmetricDensity_minus_one_eq_projectiveCompactPullback p
      (Rat.ne_of_gt hdp)
  unfold ArctanGeometry.integralUpperStep
  calc
    (r - p) *
        (reciprocalQuarticSymmetricDensity (-1) p - 8 * (r - p)) <=
      (r - p) * reciprocalQuarticSymmetricDensity (-1) p :=
        Rat.mul_le_mul_of_nonneg_left hsub hwidth
    _ = (projectiveCompactJacobian p * (r - p)) *
          ArctanGeometry.integralKernel (projectiveCompactCoordinate p) := by
        rw [hpullback]
        grind [Rat.mul_assoc, Rat.mul_comm]
    _ <= (projectiveCompactCoordinate r - projectiveCompactCoordinate p) *
          ArctanGeometry.integralKernel (projectiveCompactCoordinate p) :=
        Rat.mul_le_mul_of_nonneg_right hsecant hkernel

/-- The lower Cauchy-kernel rectangle on a positive projective image cell
lies below the upper Lipschitz rectangle for the compact reciprocal-quartic
density.  Together with the preceding theorem this gives overlap cell by
cell, without assuming a substitution theorem. -/
theorem projectiveCompact_integralLowerStep_le_lipschitzUpperCell
    {p r : Rat} (hp0 : 0 <= p) (hpr : p <= r) (hr1 : r < 1) :
    ArctanGeometry.integralLowerStep
      (projectiveCompactCoordinate p) (projectiveCompactCoordinate r) <=
      (r - p) *
        (reciprocalQuarticSymmetricDensity (-1) p + 8 * (r - p)) := by
  have hp1 : p < 1 := by grind
  have hplo : -1 < p := by grind
  have hrlo : -1 < r := by grind
  have hdp : 0 < 1 - p * p := projectiveCompactDenominator_pos hplo hp1
  have hdr : 0 < 1 - r * r := projectiveCompactDenominator_pos hrlo hr1
  have hwidth : 0 <= r - p := by grind
  have hkernel : 0 <=
      ArctanGeometry.integralKernel (projectiveCompactCoordinate r) :=
    Rat.le_of_lt (ArctanGeometry.integralKernel_pos _)
  have hsecant :=
    coordinate_sub_le_projectiveCompactJacobian_right_mul hp0 hpr hr1
  have hrpullback :=
    reciprocalQuarticSymmetricDensity_minus_one_eq_projectiveCompactPullback r
      (Rat.ne_of_gt hdr)
  have hlip := reciprocalQuarticSymmetricDensity_minus_one_lipschitz_on_unit
    p r (by grind) (by grind) (by grind) (by grind)
  have hdiff : reciprocalQuarticSymmetricDensity (-1) r -
      reciprocalQuarticSymmetricDensity (-1) p <= 8 * (r - p) := by
    calc
      reciprocalQuarticSymmetricDensity (-1) r -
          reciprocalQuarticSymmetricDensity (-1) p <=
        qabs (reciprocalQuarticSymmetricDensity (-1) r -
          reciprocalQuarticSymmetricDensity (-1) p) := self_le_qabs _
      _ = qabs (reciprocalQuarticSymmetricDensity (-1) p -
          reciprocalQuarticSymmetricDensity (-1) r) := by
          rw [show reciprocalQuarticSymmetricDensity (-1) r -
            reciprocalQuarticSymmetricDensity (-1) p =
              -(reciprocalQuarticSymmetricDensity (-1) p -
                reciprocalQuarticSymmetricDensity (-1) r) by
                grind [Rat.sub_eq_add_neg], qabs_neg]
      _ <= 8 * qabs (r - p) := hlip
      _ = 8 * (r - p) := by
          rw [qabs_eq_self_of_nonneg hwidth]
  have hpoint : reciprocalQuarticSymmetricDensity (-1) r <=
      reciprocalQuarticSymmetricDensity (-1) p + 8 * (r - p) := by
    grind [Rat.sub_eq_add_neg]
  unfold ArctanGeometry.integralLowerStep
  calc
    (projectiveCompactCoordinate r - projectiveCompactCoordinate p) *
        ArctanGeometry.integralKernel (projectiveCompactCoordinate r) <=
      (projectiveCompactJacobian r * (r - p)) *
        ArctanGeometry.integralKernel (projectiveCompactCoordinate r) :=
        Rat.mul_le_mul_of_nonneg_right hsecant hkernel
    _ = (r - p) * reciprocalQuarticSymmetricDensity (-1) r := by
        rw [hrpullback]
        grind [Rat.mul_assoc, Rat.mul_comm]
    _ <= (r - p) *
        (reciprocalQuarticSymmetricDensity (-1) p + 8 * (r - p)) :=
        Rat.mul_le_mul_of_nonneg_left hpoint hwidth

/-- Finite lower Lipschitz sum for the compact reciprocal-quartic density on
a positive compact branch. -/
def projectiveCompactLipschitzLowerSum : List (Rat × Rat) -> Rat
  | [] => 0
  | (p, r) :: rest =>
      (r - p) * (reciprocalQuarticSymmetricDensity (-1) p - 8 * (r - p)) +
        projectiveCompactLipschitzLowerSum rest

/-- Matching finite upper Lipschitz sum for the compact reciprocal-quartic
density on a positive compact branch. -/
def projectiveCompactLipschitzUpperSum : List (Rat × Rat) -> Rat
  | [] => 0
  | (p, r) :: rest =>
      (r - p) * (reciprocalQuarticSymmetricDensity (-1) p + 8 * (r - p)) +
        projectiveCompactLipschitzUpperSum rest

/-- The compact lower Lipschitz sum lies below the transported Cauchy upper
sum on every finite positive branch cover. -/
theorem projectiveCompactLipschitzLowerSum_le_integralUpperSum
    (a s : Rat) (intervals : List (Rat × Rat))
    (ha : 0 <= a) (hs : s < 1)
    (hcover : ArctanGeometry.CoversInterval a s intervals) :
    projectiveCompactLipschitzLowerSum intervals <=
      ArctanGeometry.integralUpperSum (projectiveCompactIntervals intervals) := by
  induction intervals generalizing a with
  | nil =>
      simp [projectiveCompactLipschitzLowerSum, projectiveCompactIntervals,
        ArctanGeometry.integralUpperSum]
  | cons cell rest ih =>
      rcases cell with ⟨p, r⟩
      rcases hcover with ⟨hp, hpr, hrest⟩
      subst p
      have hr0 : 0 <= r := Rat.le_trans ha hpr
      have hrs : r <= s := ArctanGeometry.CoversInterval.start_le_end hrest
      have hr1 : r < 1 := by grind
      have hcell :=
        projectiveCompact_lipschitzLowerCell_le_integralUpperStep ha hpr hr1
      have htail := ih r hr0 hrest
      simp only [projectiveCompactLipschitzLowerSum, projectiveCompactIntervals,
        ArctanGeometry.integralUpperSum]
      exact rat_add_le_add hcell htail

/-- The transported Cauchy lower sum lies below the compact upper Lipschitz
sum on every finite positive branch cover. -/
theorem projectiveCompactIntegralLowerSum_le_lipschitzUpperSum
    (a s : Rat) (intervals : List (Rat × Rat))
    (ha : 0 <= a) (hs : s < 1)
    (hcover : ArctanGeometry.CoversInterval a s intervals) :
    ArctanGeometry.integralLowerSum (projectiveCompactIntervals intervals) <=
      projectiveCompactLipschitzUpperSum intervals := by
  induction intervals generalizing a with
  | nil =>
      simp [projectiveCompactLipschitzUpperSum, projectiveCompactIntervals,
        ArctanGeometry.integralLowerSum]
  | cons cell rest ih =>
      rcases cell with ⟨p, r⟩
      rcases hcover with ⟨hp, hpr, hrest⟩
      subst p
      have hr0 : 0 <= r := Rat.le_trans ha hpr
      have hrs : r <= s := ArctanGeometry.CoversInterval.start_le_end hrest
      have hr1 : r < 1 := by grind
      have hcell :=
        projectiveCompact_integralLowerStep_le_lipschitzUpperCell ha hpr hr1
      have htail := ih r hr0 hrest
      simp only [projectiveCompactLipschitzUpperSum, projectiveCompactIntervals,
        ArctanGeometry.integralLowerSum]
      exact rat_add_le_add hcell htail

/-- The finite compact-density Lipschitz bracket overlaps the ordinary Cauchy
rectangle bracket after projective transport of the same source partition.
This is the assembled finite quadrature bridge; the remaining work is to
turn its endpoint schedule into an equivalence of the full integral raws. -/
theorem projectiveCompactLipschitzSum_overlaps_integralSum
    (a s : Rat) (intervals : List (Rat × Rat))
    (ha : 0 <= a) (hs : s < 1)
    (hcover : ArctanGeometry.CoversInterval a s intervals) :
    QInterval.Overlaps
      { lo := projectiveCompactLipschitzLowerSum intervals,
        hi := projectiveCompactLipschitzUpperSum intervals }
      (ArctanGeometry.integralSumInterval (projectiveCompactIntervals intervals)) := by
  unfold QInterval.Overlaps ArctanGeometry.integralSumInterval
  exact ⟨projectiveCompactLipschitzLowerSum_le_integralUpperSum a s intervals
      ha hs hcover,
    projectiveCompactIntegralLowerSum_le_lipschitzUpperSum a s intervals
      ha hs hcover⟩

/-- The two-branch compact quadrature bracket obtained by reflecting the
positive source branch through zero.  Evenness of the compact density makes
this an exact finite reparameterization of the symmetric compact core. -/
def projectiveCompactSymmetricLipschitzSum
    (intervals : List (Rat × Rat)) : QInterval :=
  { lo := 2 * projectiveCompactLipschitzLowerSum intervals,
    hi := 2 * projectiveCompactLipschitzUpperSum intervals }

/-- The matching two-branch Cauchy rectangle bracket for the projective image
of a positive source partition. -/
def projectiveCompactSymmetricIntegralSum
    (intervals : List (Rat × Rat)) : QInterval :=
  { lo := 2 * ArctanGeometry.integralLowerSum
      (projectiveCompactIntervals intervals),
    hi := 2 * ArctanGeometry.integralUpperSum
      (projectiveCompactIntervals intervals) }

/-- The two symmetric finite quadrature cores overlap after the projective
transport.  The proof is just positive rational scaling of the verified
one-branch cellwise bridge; the evenness lemmas above justify its intended
two-branch interpretation. -/
theorem projectiveCompactSymmetricLipschitzSum_overlaps_integralSum
    (a s : Rat) (intervals : List (Rat × Rat))
    (ha : 0 <= a) (hs : s < 1)
    (hcover : ArctanGeometry.CoversInterval a s intervals) :
    QInterval.Overlaps
      (projectiveCompactSymmetricLipschitzSum intervals)
      (projectiveCompactSymmetricIntegralSum intervals) := by
  have h := projectiveCompactLipschitzSum_overlaps_integralSum
    a s intervals ha hs hcover
  unfold QInterval.Overlaps projectiveCompactSymmetricLipschitzSum
    projectiveCompactSymmetricIntegralSum at *
  exact ⟨Rat.mul_le_mul_of_nonneg_left h.1 (by native_decide),
    Rat.mul_le_mul_of_nonneg_left h.2 (by native_decide)⟩

/-- The compactified density has finite rational endpoint values, so the
projective chart's poles are removable at the level of the intended integrand. -/
theorem reciprocalQuarticSymmetricDensity_minus_one_at_one :
    reciprocalQuarticSymmetricDensity (-1) 1 = 2 := by
  native_decide

theorem reciprocalQuarticSymmetricDensity_minus_one_at_neg_one :
    reciprocalQuarticSymmetricDensity (-1) (-1) = 2 := by
  native_decide

/-- Exact rational-name evaluator for the compactified clean quartic density.
It is defined on every rational input; later interval regularity will certify
its finite-interval integral. -/
def reciprocalQuarticMinusOneCompactRaw : PartialRealFunRaw where
  definedAt := fun _ => True
  compute := fun x _ _ =>
    let y := reciprocalQuarticSymmetricDensity (-1) x
    { lo := y, hi := y }

/-- The compact reciprocal-quartic density restricted to a rational interval. -/
def reciprocalQuarticMinusOneCompactOnInterval (a b : Rat) : FunctionOnInterval where
  raw := reciprocalQuarticMinusOneCompactRaw
  lower := a
  upper := b
  defined_on := fun _ _ => trivial
  valid_on := by
    intro x _hx
    simpa [reciprocalQuarticMinusOneCompactRaw] using
      RealRaw.ofRat_valid (reciprocalQuarticSymmetricDensity (-1) x)

theorem reciprocalQuarticMinusOneCompactOnInterval_valid (a b : Rat) :
    (reciprocalQuarticMinusOneCompactOnInterval a b).toRealFunRaw.Valid :=
  FunctionOnInterval.toRealFunRaw_valid _

theorem reciprocalQuarticMinusOneCompactRaw_compute_eq_density
    (x : Rat) (h : reciprocalQuarticMinusOneCompactRaw.definedAt x) (n : Nat) :
    reciprocalQuarticMinusOneCompactRaw.compute x h n =
      { lo := reciprocalQuarticSymmetricDensity (-1) x,
        hi := reciprocalQuarticSymmetricDensity (-1) x } := by
  simp [reciprocalQuarticMinusOneCompactRaw]

/-- The exact compact-density evaluator is rational epsilon-delta continuous
on `[-1,1]`.  The modulus uses the explicit Lipschitz constant `8`. -/
theorem reciprocalQuarticMinusOneCompact_epsilonDeltaContinuous :
    EpsilonDeltaContinuousOn
      (reciprocalQuarticMinusOneCompactOnInterval (-1) 1) := by
  intro eps
  let delta : QPos :=
    { val := eps.val / 8
      property := by
        rw [Rat.div_def]
        exact Rat.mul_pos eps.property ((Rat.inv_pos).2 (by native_decide)) }
  refine ⟨delta, 0, ?_⟩
  intro x y hx hy hxy
  rcases hx with ⟨hxlo, hxhi⟩
  rcases hy with ⟨hylo, hyhi⟩
  have hlip := reciprocalQuarticSymmetricDensity_minus_one_lipschitz_on_unit
    x y hxlo hxhi hylo hyhi
  have hdist :
      qabs (reciprocalQuarticSymmetricDensity (-1) x -
        reciprocalQuarticSymmetricDensity (-1) y) <= eps.val := by
    calc
      qabs (reciprocalQuarticSymmetricDensity (-1) x -
        reciprocalQuarticSymmetricDensity (-1) y) <= 8 * qabs (y - x) := hlip
      _ <= 8 * (eps.val / 8) := Rat.mul_le_mul_of_nonneg_left (by
        simpa [delta] using hxy)
        (by native_decide)
      _ = eps.val := by
        rw [Rat.div_def]
        have hcancel : (8 : Rat) * (8 : Rat)⁻¹ = 1 := by native_decide
        grind [Rat.mul_assoc, Rat.mul_comm]
  have hreverse :
      reciprocalQuarticSymmetricDensity (-1) y -
        reciprocalQuarticSymmetricDensity (-1) x <= eps.val := by
    calc
      reciprocalQuarticSymmetricDensity (-1) y -
          reciprocalQuarticSymmetricDensity (-1) x =
          -(reciprocalQuarticSymmetricDensity (-1) x -
            reciprocalQuarticSymmetricDensity (-1) y) := by
            grind [Rat.sub_eq_add_neg]
      _ <= qabs (-(reciprocalQuarticSymmetricDensity (-1) x -
            reciprocalQuarticSymmetricDensity (-1) y)) := self_le_qabs _
      _ = qabs (reciprocalQuarticSymmetricDensity (-1) x -
            reciprocalQuarticSymmetricDensity (-1) y) := qabs_neg _
      _ <= eps.val := hdist
  have hforward :
      reciprocalQuarticSymmetricDensity (-1) x -
        reciprocalQuarticSymmetricDensity (-1) y <= eps.val := by
    exact Rat.le_trans (self_le_qabs _) hdist
  unfold QInterval.NearAt
  change
    reciprocalQuarticSymmetricDensity (-1) x <=
        reciprocalQuarticSymmetricDensity (-1) y + eps.val /\
      reciprocalQuarticSymmetricDensity (-1) y <=
        reciprocalQuarticSymmetricDensity (-1) x + eps.val /\
      reciprocalQuarticSymmetricDensity (-1) x -
          reciprocalQuarticSymmetricDensity (-1) x <= eps.val /\
      reciprocalQuarticSymmetricDensity (-1) y -
          reciprocalQuarticSymmetricDensity (-1) y <= eps.val
  constructor
  · grind [Rat.sub_eq_add_neg]
  constructor
  · grind [Rat.sub_eq_add_neg]
  constructor <;> grind

/-- A finite rational scaling fact used by the compact-density interval
evaluator.  Splitting the zero stage is intentional: raw interval algorithms
allow stage `0`, whose target width is exactly zero. -/
private theorem reciprocalQuartic_interval_width_scale (w : Rat) (n : Nat)
    (hn : n ≠ 0)
    (hw : w <= 1 / ((16 * n : Nat) : Rat)) :
    16 * w <= 1 / (n : Rat) := by
  calc
    16 * w <= 16 * (1 / ((16 * n : Nat) : Rat)) :=
      Rat.mul_le_mul_of_nonneg_left hw (by native_decide)
    _ = 1 / (n : Rat) := by
      rw [Rat.div_def]
      rw [show ((16 * n : Nat) : Rat) = (16 : Rat) * (n : Rat) by
        exact Rat.natCast_mul 16 n]
      have h16 : (16 : Rat) ≠ 0 := by native_decide
      have hn' : (n : Rat) ≠ 0 := by
        exact Rat.ne_of_gt ((Rat.natCast_pos).2 (Nat.pos_of_ne_zero hn))
      rw [Rat.inv_mul_rev]
      grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

/-- Interval evaluator for the compact reciprocal-quartic density on
`[-1,1]`.  It evaluates the exact rational formula at the input midpoint and
enlarges by the proved `8`-Lipschitz error. -/
def reciprocalQuarticMinusOneCompact_evalInterval (I : QInterval) : QInterval :=
  let v := reciprocalQuarticSymmetricDensity (-1) I.midpoint
  { lo := v - 8 * I.width, hi := v + 8 * I.width }

theorem reciprocalQuarticMinusOneCompact_evalInterval_width (I : QInterval) :
    (reciprocalQuarticMinusOneCompact_evalInterval I).width = 16 * I.width := by
  simp [reciprocalQuarticMinusOneCompact_evalInterval, QInterval.width]
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.add_assoc,
    Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]

/-- The compact reciprocal-quartic density is interval-regular on `[-1,1]`.

Every rational input box is enclosed by midpoint evaluation widened using the
checked `8`-Lipschitz bound.  This supplies the interval-level continuity data
needed by the integral, inverse, and ODE interfaces without importing a
topology or a completed real line. -/
def reciprocalQuarticMinusOneCompact_intervalRegular :
    IntervalRegularOn (reciprocalQuarticMinusOneCompactOnInterval (-1) 1) := by
  refine
    { evalInterval := fun I _ _ => reciprocalQuarticMinusOneCompact_evalInterval I
      inputPrecision := fun n => 16 * n
      inputPrecision_pos := by
        intro n hn
        omega
      output_width := ?_
      contains_point_values := ?_ }
  · intro I hI n hwidth
    rcases hI with ⟨hlo, hord, hhi⟩
    have hwidth_nonneg : 0 <= I.width := by
      unfold QInterval.width
      grind [Rat.sub_eq_add_neg]
    constructor
    · rw [reciprocalQuarticMinusOneCompact_evalInterval_width]
      exact Rat.mul_nonneg (by native_decide) hwidth_nonneg
    · rw [reciprocalQuarticMinusOneCompact_evalInterval_width]
      by_cases hn : n = 0
      · subst n
        have hinvzero : 1 / ((16 * (0 : Nat) : Nat) : Rat) = 0 := by
          native_decide
        rw [hinvzero] at hwidth
        have hzero : I.width = 0 := Rat.le_antisymm hwidth hwidth_nonneg
        rw [hzero]
        native_decide
      · exact reciprocalQuartic_interval_width_scale I.width n hn hwidth
  · intro I hI x hx n hxlo hxhi
    rcases hI with ⟨hIlo, hordered, hIhi⟩
    have hmid := QInterval.midpoint_mem hordered
    have hmid_domain : inDomainInterval (-1) 1 I.midpoint :=
      ⟨Rat.le_trans hIlo hmid.1, Rat.le_trans hmid.2 hIhi⟩
    have hxdomain : inDomainInterval (-1) 1 x := hx
    have hdist : qabs (I.midpoint - x) <= I.width := by
      rw [show I.midpoint - x = -(x - I.midpoint) by
        grind [Rat.sub_eq_add_neg], qabs_neg]
      exact QInterval.qabs_sub_midpoint_le_width hordered hxlo hxhi
    have hlip := reciprocalQuarticSymmetricDensity_minus_one_lipschitz_on_unit
      x I.midpoint hxdomain.1 hxdomain.2 hmid_domain.1 hmid_domain.2
    have hdiff :
        qabs (reciprocalQuarticSymmetricDensity (-1) x -
          reciprocalQuarticSymmetricDensity (-1) I.midpoint) <= 8 * I.width := by
      exact Rat.le_trans hlip
        (Rat.mul_le_mul_of_nonneg_left hdist (by native_decide))
    have hupper : reciprocalQuarticSymmetricDensity (-1) x -
        reciprocalQuarticSymmetricDensity (-1) I.midpoint <= 8 * I.width :=
      Rat.le_trans (self_le_qabs _) hdiff
    have hlower : reciprocalQuarticSymmetricDensity (-1) I.midpoint -
        reciprocalQuarticSymmetricDensity (-1) x <= 8 * I.width := by
      calc
        reciprocalQuarticSymmetricDensity (-1) I.midpoint -
            reciprocalQuarticSymmetricDensity (-1) x =
            -(reciprocalQuarticSymmetricDensity (-1) x -
              reciprocalQuarticSymmetricDensity (-1) I.midpoint) := by
              grind [Rat.sub_eq_add_neg]
        _ <= qabs (-(reciprocalQuarticSymmetricDensity (-1) x -
              reciprocalQuarticSymmetricDensity (-1) I.midpoint)) := self_le_qabs _
        _ = qabs (reciprocalQuarticSymmetricDensity (-1) x -
              reciprocalQuarticSymmetricDensity (-1) I.midpoint) := qabs_neg _
        _ <= 8 * I.width := hdiff
    unfold QInterval.ContainsInterval
    change reciprocalQuarticSymmetricDensity (-1) I.midpoint - 8 * I.width <=
        reciprocalQuarticSymmetricDensity (-1) x /\
      reciprocalQuarticSymmetricDensity (-1) x <=
        reciprocalQuarticSymmetricDensity (-1) I.midpoint + 8 * I.width
    constructor <;> grind [Rat.sub_eq_add_neg]

/-- The compact reciprocal-quartic density packaged for theorem-facing
calculus consumers. -/
def reciprocalQuarticMinusOneCompact_continuous : ContinuousFunctionOnInterval where
  function := reciprocalQuarticMinusOneCompactOnInterval (-1) 1
  regular := reciprocalQuarticMinusOneCompact_intervalRegular

/-- The generic interval-regularity bridge reproduces rational
epsilon-delta continuity for the compact reciprocal-quartic density. -/
theorem reciprocalQuarticMinusOneCompact_epsilonDeltaContinuous_from_intervalRegular :
    EpsilonDeltaContinuousOn
      (reciprocalQuarticMinusOneCompactOnInterval (-1) 1) :=
  reciprocalQuarticMinusOneCompact_intervalRegular.epsilonDeltaContinuous

/-- The affine unit-interval presentation of the compact reciprocal-quartic
density.  It is exactly the change of variables `x = 2t - 1`, including the
Jacobian `2`; hence it is the form on which the ordinary midpoint-dyadic
Riemann mesh operates.  This is a finite rational function at every rational
sample point--not an appeal to a completed interval integral. -/
def reciprocalQuarticMinusOneUnitDensity (t : Rat) : Rat :=
  2 * reciprocalQuarticSymmetricDensity (-1) (2 * t - 1)

/-- The affine unit density is `32`-Lipschitz on `[0,1]`.  The factor is the
product of the compact-density constant `8`, the affine-coordinate stretch
`2`, and the Jacobian factor `2`. -/
theorem reciprocalQuarticMinusOneUnitDensity_lipschitz_on_unit
    (s t : Rat)
    (hs0 : 0 <= s) (hs1 : s <= 1)
    (ht0 : 0 <= t) (ht1 : t <= 1) :
    qabs (reciprocalQuarticMinusOneUnitDensity s -
      reciprocalQuarticMinusOneUnitDensity t) <= 32 * qabs (t - s) := by
  have hslo : -1 <= 2 * s - 1 := by grind
  have hshi : 2 * s - 1 <= 1 := by grind
  have htlo : -1 <= 2 * t - 1 := by grind
  have hthi : 2 * t - 1 <= 1 := by grind
  have hcompact := reciprocalQuarticSymmetricDensity_minus_one_lipschitz_on_unit
    (2 * s - 1) (2 * t - 1) hslo hshi htlo hthi
  have hstretch : qabs ((2 * t - 1) - (2 * s - 1)) = 2 * qabs (t - s) := by
    rw [show (2 * t - 1) - (2 * s - 1) = 2 * (t - s) by
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
        Rat.add_assoc, Rat.add_comm]]
    rw [qabs_mul, qabs_eq_self_of_nonneg (by native_decide : (0 : Rat) <= 2)]
  have hscaled :
      qabs (2 * (reciprocalQuarticSymmetricDensity (-1) (2 * s - 1) -
        reciprocalQuarticSymmetricDensity (-1) (2 * t - 1))) <=
        2 * (8 * qabs ((2 * t - 1) - (2 * s - 1))) := by
    rw [qabs_mul, qabs_eq_self_of_nonneg (by native_decide : (0 : Rat) <= 2)]
    exact Rat.mul_le_mul_of_nonneg_left hcompact (by native_decide)
  calc
    qabs (reciprocalQuarticMinusOneUnitDensity s -
        reciprocalQuarticMinusOneUnitDensity t) =
        qabs (2 * (reciprocalQuarticSymmetricDensity (-1) (2 * s - 1) -
          reciprocalQuarticSymmetricDensity (-1) (2 * t - 1))) := by
          simp only [reciprocalQuarticMinusOneUnitDensity]
          congr 1
          grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
            Rat.add_assoc, Rat.add_comm]
    _ <= 2 * (8 * qabs ((2 * t - 1) - (2 * s - 1))) := hscaled
    _ = 32 * qabs (t - s) := by rw [hstretch]; grind [Rat.mul_assoc, Rat.mul_comm]

/-- The exact left Riemann sum of the affine compact density on the ordinary
static dyadic mesh.  The stage is visibly a finite rational computation: no
limit, topology, or real-number completeness is hidden in this definition. -/
def reciprocalQuarticMinusOneUnitLeftRiemann (stage : Nat) : Rat :=
  riemannLeftExact reciprocalQuarticMinusOneUnitDensity 0 1 (2 ^ stage)

theorem reciprocalQuarticMinusOneUnitLeftRiemann_eq_finite_sum (stage : Nat) :
    reciprocalQuarticMinusOneUnitLeftRiemann stage =
      riemannLeftExact reciprocalQuarticMinusOneUnitDensity 0 1 (2 ^ stage) :=
  rfl

/-- A Lipschitz lower rectangle at the left endpoint of a unit cell.  The
subtracted term is the certified 32-Lipschitz oscillation bound over that
cell. -/
private def reciprocalQuarticMinusOneUnitLowerCell (p r : Rat) : Rat :=
  Integral.lipschitzLowerCell reciprocalQuarticMinusOneUnitDensity 32 p r

/-- The matching Lipschitz upper rectangle at the left endpoint of a unit
cell. -/
private def reciprocalQuarticMinusOneUnitUpperCell (p r : Rat) : Rat :=
  Integral.lipschitzUpperCell reciprocalQuarticMinusOneUnitDensity 32 p r

private def reciprocalQuarticMinusOneUnitLowerSum :
    List (Rat × Rat) -> Rat
  | [] => 0
  | (p, r) :: rest =>
      reciprocalQuarticMinusOneUnitLowerCell p r +
        reciprocalQuarticMinusOneUnitLowerSum rest

private def reciprocalQuarticMinusOneUnitUpperSum :
    List (Rat × Rat) -> Rat
  | [] => 0
  | (p, r) :: rest =>
      reciprocalQuarticMinusOneUnitUpperCell p r +
        reciprocalQuarticMinusOneUnitUpperSum rest

/-- The explicit two-sided dyadic bracket for the affine compact quartic
density.  Its centre is the ordinary left Riemann sum; its radius is supplied
cellwise from the proved rational Lipschitz estimate. -/
def reciprocalQuarticMinusOneUnitDyadicCompute (stage : Nat) : QInterval :=
  let cells := (ArctanGeometry.arctanAreaLoopState 1 stage).intervals
  { lo := reciprocalQuarticMinusOneUnitLowerSum cells
    hi := reciprocalQuarticMinusOneUnitUpperSum cells }

/-- Splitting one unit cell at its rational midpoint tightens the elementary
Lipschitz rectangle.  This is the finite refinement inequality from which the
raw interval algorithm will obtain nestedness. -/
private theorem reciprocalQuarticMinusOneUnit_cells_refine
    {p r : Rat} (hp0 : 0 <= p) (hpr : p <= r) (hr1 : r <= 1) :
    let q := (p + r) / 2
    reciprocalQuarticMinusOneUnitLowerCell p r <=
      reciprocalQuarticMinusOneUnitLowerCell p q +
        reciprocalQuarticMinusOneUnitLowerCell q r /\
    reciprocalQuarticMinusOneUnitUpperCell p q +
        reciprocalQuarticMinusOneUnitUpperCell q r <=
      reciprocalQuarticMinusOneUnitUpperCell p r := by
  have hlip : Integral.LipschitzOnUnit reciprocalQuarticMinusOneUnitDensity 32 :=
    ⟨by native_decide,
      fun s t hs0 hs1 ht0 ht1 =>
        reciprocalQuarticMinusOneUnitDensity_lipschitz_on_unit
          s t hs0 hs1 ht0 ht1⟩
  simpa [reciprocalQuarticMinusOneUnitLowerCell,
    reciprocalQuarticMinusOneUnitUpperCell] using
    (Integral.lipschitzCells_refine hlip hp0 hpr hr1)

private theorem reciprocalQuarticMinusOneUnit_lowerSum_refineAux
    (lo hi : Rat) (intervals : List (Rat × Rat))
    (hunit : ArctanGeometry.UnitIntervals intervals) :
    reciprocalQuarticMinusOneUnitLowerSum intervals <=
      reciprocalQuarticMinusOneUnitLowerSum
        (ArctanGeometry.AreaLoopState.refineAux lo hi intervals).intervals := by
  induction intervals generalizing lo hi with
  | nil =>
      simp [ArctanGeometry.AreaLoopState.refineAux,
        reciprocalQuarticMinusOneUnitLowerSum]
  | cons interval rest ih =>
      rcases interval with ⟨p, r⟩
      rcases hunit with ⟨hp0, hpr, hr1, hrest⟩
      let q : Rat := (p + r) / 2
      have hcell := reciprocalQuarticMinusOneUnit_cells_refine hp0 hpr hr1
      have htail := ih
        (lo + ArctanGeometry.arctanAreaIncrement p q r)
        (hi - ArctanGeometry.arctanAreaDecrement p q r) hrest
      dsimp [q] at hcell
      dsimp [q] at htail ⊢
      simp [ArctanGeometry.AreaLoopState.refineAux,
        reciprocalQuarticMinusOneUnitLowerSum] at htail ⊢
      calc
        reciprocalQuarticMinusOneUnitLowerCell p r +
            reciprocalQuarticMinusOneUnitLowerSum rest <=
            (reciprocalQuarticMinusOneUnitLowerCell p ((p + r) / 2) +
              reciprocalQuarticMinusOneUnitLowerCell ((p + r) / 2) r) +
              reciprocalQuarticMinusOneUnitLowerSum rest :=
          rat_add_le_add hcell.1 Rat.le_refl
        _ <= (reciprocalQuarticMinusOneUnitLowerCell p ((p + r) / 2) +
              reciprocalQuarticMinusOneUnitLowerCell ((p + r) / 2) r) +
              reciprocalQuarticMinusOneUnitLowerSum
                (ArctanGeometry.AreaLoopState.refineAux
                  (lo + ArctanGeometry.arctanAreaIncrement p ((p + r) / 2) r)
                  (hi - ArctanGeometry.arctanAreaDecrement p ((p + r) / 2) r)
                  rest).intervals :=
          by
            have hsum :
                (reciprocalQuarticMinusOneUnitLowerCell p ((p + r) / 2) +
                  reciprocalQuarticMinusOneUnitLowerCell ((p + r) / 2) r) +
                    reciprocalQuarticMinusOneUnitLowerSum rest <=
                (reciprocalQuarticMinusOneUnitLowerCell p ((p + r) / 2) +
                  reciprocalQuarticMinusOneUnitLowerCell ((p + r) / 2) r) +
                    reciprocalQuarticMinusOneUnitLowerSum
                      (ArctanGeometry.AreaLoopState.refineAux
                        (lo + ArctanGeometry.arctanAreaIncrement p ((p + r) / 2) r)
                        (hi - ArctanGeometry.arctanAreaDecrement p ((p + r) / 2) r)
                        rest).intervals :=
              rat_add_le_add Rat.le_refl htail
            grind [Rat.add_assoc]
        _ = reciprocalQuarticMinusOneUnitLowerCell p ((p + r) / 2) +
              (reciprocalQuarticMinusOneUnitLowerCell ((p + r) / 2) r +
                reciprocalQuarticMinusOneUnitLowerSum
                  (ArctanGeometry.AreaLoopState.refineAux
                    (lo + ArctanGeometry.arctanAreaIncrement p ((p + r) / 2) r)
                    (hi - ArctanGeometry.arctanAreaDecrement p ((p + r) / 2) r)
                    rest).intervals) := by
            grind [Rat.add_assoc]

private theorem reciprocalQuarticMinusOneUnit_upperSum_refineAux
    (lo hi : Rat) (intervals : List (Rat × Rat))
    (hunit : ArctanGeometry.UnitIntervals intervals) :
    reciprocalQuarticMinusOneUnitUpperSum
        (ArctanGeometry.AreaLoopState.refineAux lo hi intervals).intervals <=
      reciprocalQuarticMinusOneUnitUpperSum intervals := by
  induction intervals generalizing lo hi with
  | nil =>
      simp [ArctanGeometry.AreaLoopState.refineAux,
        reciprocalQuarticMinusOneUnitUpperSum]
  | cons interval rest ih =>
      rcases interval with ⟨p, r⟩
      rcases hunit with ⟨hp0, hpr, hr1, hrest⟩
      let q : Rat := (p + r) / 2
      have hcell := reciprocalQuarticMinusOneUnit_cells_refine hp0 hpr hr1
      have htail := ih
        (lo + ArctanGeometry.arctanAreaIncrement p q r)
        (hi - ArctanGeometry.arctanAreaDecrement p q r) hrest
      dsimp [q] at hcell
      dsimp [q] at htail ⊢
      simp [ArctanGeometry.AreaLoopState.refineAux,
        reciprocalQuarticMinusOneUnitUpperSum] at htail ⊢
      calc
        reciprocalQuarticMinusOneUnitUpperCell p ((p + r) / 2) +
            (reciprocalQuarticMinusOneUnitUpperCell ((p + r) / 2) r +
              reciprocalQuarticMinusOneUnitUpperSum
                (ArctanGeometry.AreaLoopState.refineAux
                  (lo + ArctanGeometry.arctanAreaIncrement p ((p + r) / 2) r)
                  (hi - ArctanGeometry.arctanAreaDecrement p ((p + r) / 2) r)
                  rest).intervals) =
            reciprocalQuarticMinusOneUnitUpperCell p ((p + r) / 2) +
              reciprocalQuarticMinusOneUnitUpperCell ((p + r) / 2) r +
                reciprocalQuarticMinusOneUnitUpperSum
                  (ArctanGeometry.AreaLoopState.refineAux
                    (lo + ArctanGeometry.arctanAreaIncrement p ((p + r) / 2) r)
                    (hi - ArctanGeometry.arctanAreaDecrement p ((p + r) / 2) r)
                    rest).intervals := by
              grind [Rat.add_assoc]
        _ <= reciprocalQuarticMinusOneUnitUpperCell p ((p + r) / 2) +
              reciprocalQuarticMinusOneUnitUpperCell ((p + r) / 2) r +
                reciprocalQuarticMinusOneUnitUpperSum rest :=
          rat_add_le_add Rat.le_refl htail
        _ <= reciprocalQuarticMinusOneUnitUpperCell p r +
              reciprocalQuarticMinusOneUnitUpperSum rest :=
          rat_add_le_add hcell.2 Rat.le_refl

theorem reciprocalQuarticMinusOneUnitDyadicCompute_step_refines (stage : Nat) :
    (reciprocalQuarticMinusOneUnitDyadicCompute stage).lo <=
      (reciprocalQuarticMinusOneUnitDyadicCompute (stage + 1)).lo /\
    (reciprocalQuarticMinusOneUnitDyadicCompute (stage + 1)).hi <=
      (reciprocalQuarticMinusOneUnitDyadicCompute stage).hi := by
  unfold reciprocalQuarticMinusOneUnitDyadicCompute
  rw [show stage + 1 = Nat.succ stage by omega,
    ArctanGeometry.arctanAreaLoopState_succ]
  dsimp
  let state := ArctanGeometry.arctanAreaLoopState 1 stage
  have hunit : ArctanGeometry.UnitIntervals state.intervals :=
    ArctanGeometry.arctanAreaLoopState_intervals_unit
      (x := 1) (by native_decide) (by native_decide) stage
  constructor
  · exact reciprocalQuarticMinusOneUnit_lowerSum_refineAux
      state.lo state.hi state.intervals hunit
  · exact reciprocalQuarticMinusOneUnit_upperSum_refineAux
      state.lo state.hi state.intervals hunit

private theorem reciprocalQuarticMinusOneUnit_lowerCell_le_upperCell
    {p r : Rat} (hpr : p <= r) :
    reciprocalQuarticMinusOneUnitLowerCell p r <=
      reciprocalQuarticMinusOneUnitUpperCell p r := by
  have hwidth : 0 <= r - p := by grind [Rat.sub_eq_add_neg]
  have hinner :
      reciprocalQuarticMinusOneUnitDensity p - 32 * (r - p) <=
        reciprocalQuarticMinusOneUnitDensity p + 32 * (r - p) := by
    have hterm : 0 <= 32 * (r - p) :=
      Rat.mul_nonneg (by native_decide) hwidth
    grind [Rat.sub_eq_add_neg]
  unfold reciprocalQuarticMinusOneUnitLowerCell
    reciprocalQuarticMinusOneUnitUpperCell
  exact Rat.mul_le_mul_of_nonneg_left hinner hwidth

private theorem reciprocalQuarticMinusOneUnit_lowerSum_le_upperSum
    (intervals : List (Rat × Rat))
    (hunit : ArctanGeometry.UnitIntervals intervals) :
    reciprocalQuarticMinusOneUnitLowerSum intervals <=
      reciprocalQuarticMinusOneUnitUpperSum intervals := by
  induction intervals with
  | nil =>
      simp [reciprocalQuarticMinusOneUnitLowerSum,
        reciprocalQuarticMinusOneUnitUpperSum]
  | cons interval rest ih =>
      rcases interval with ⟨p, r⟩
      rcases hunit with ⟨_hp0, hpr, _hr1, hrest⟩
      simp [reciprocalQuarticMinusOneUnitLowerSum,
        reciprocalQuarticMinusOneUnitUpperSum]
      exact rat_add_le_add
        (reciprocalQuarticMinusOneUnit_lowerCell_le_upperCell hpr)
        (ih hrest)

private theorem reciprocalQuarticMinusOneUnit_cell_width
    (p r : Rat) :
    reciprocalQuarticMinusOneUnitUpperCell p r -
        reciprocalQuarticMinusOneUnitLowerCell p r =
      64 * ((r - p) * (r - p)) := by
  change
    (r - p) * (reciprocalQuarticMinusOneUnitDensity p + 32 * (r - p)) -
        (r - p) * (reciprocalQuarticMinusOneUnitDensity p - 32 * (r - p)) =
      64 * ((r - p) * (r - p))
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
    Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]

private theorem reciprocalQuarticMinusOneUnit_sum_width
    (intervals : List (Rat × Rat)) :
    reciprocalQuarticMinusOneUnitUpperSum intervals -
        reciprocalQuarticMinusOneUnitLowerSum intervals =
      64 * ArctanGeometry.intervalSquareSum intervals := by
  induction intervals with
  | nil =>
      simp [reciprocalQuarticMinusOneUnitLowerSum,
        reciprocalQuarticMinusOneUnitUpperSum,
        ArctanGeometry.intervalSquareSum]
      native_decide
  | cons interval rest ih =>
      rcases interval with ⟨p, r⟩
      have hcell := reciprocalQuarticMinusOneUnit_cell_width p r
      simp [reciprocalQuarticMinusOneUnitLowerSum,
        reciprocalQuarticMinusOneUnitUpperSum,
        ArctanGeometry.intervalSquareSum]
      calc
        reciprocalQuarticMinusOneUnitUpperCell p r +
              reciprocalQuarticMinusOneUnitUpperSum rest -
            (reciprocalQuarticMinusOneUnitLowerCell p r +
              reciprocalQuarticMinusOneUnitLowerSum rest) =
            (reciprocalQuarticMinusOneUnitUpperCell p r -
              reciprocalQuarticMinusOneUnitLowerCell p r) +
              (reciprocalQuarticMinusOneUnitUpperSum rest -
                reciprocalQuarticMinusOneUnitLowerSum rest) := by
              grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]
        _ = 64 * ((r - p) * (r - p)) +
              64 * ArctanGeometry.intervalSquareSum rest := by
              rw [hcell, ih]
        _ = 64 * ((r - p) * (r - p) +
              ArctanGeometry.intervalSquareSum rest) := by
              grind [Rat.mul_add, Rat.add_assoc, Rat.add_comm]

theorem reciprocalQuarticMinusOneUnitDyadicCompute_ordered (stage : Nat) :
    0 <= (reciprocalQuarticMinusOneUnitDyadicCompute stage).width := by
  unfold reciprocalQuarticMinusOneUnitDyadicCompute QInterval.width
  dsimp
  let cells := (ArctanGeometry.arctanAreaLoopState 1 stage).intervals
  have hunit : ArctanGeometry.UnitIntervals cells :=
    ArctanGeometry.arctanAreaLoopState_intervals_unit
      (x := 1) (by native_decide) (by native_decide) stage
  have hsum := reciprocalQuarticMinusOneUnit_lowerSum_le_upperSum cells hunit
  grind [Rat.sub_eq_add_neg]

theorem reciprocalQuarticMinusOneUnitDyadicCompute_width (stage : Nat) :
    (reciprocalQuarticMinusOneUnitDyadicCompute stage).width =
      64 * (1 / (((2 ^ stage : Nat) : Rat))) := by
  unfold reciprocalQuarticMinusOneUnitDyadicCompute QInterval.width
  dsimp
  rw [reciprocalQuarticMinusOneUnit_sum_width,
    ArctanGeometry.arctanAreaLoopState_one_squareSum]

theorem reciprocalQuarticMinusOneUnitDyadicCompute_nested
    (n m : Nat) (hnm : n <= m) :
    (reciprocalQuarticMinusOneUnitDyadicCompute n).lo <=
        (reciprocalQuarticMinusOneUnitDyadicCompute m).lo /\
      (reciprocalQuarticMinusOneUnitDyadicCompute m).lo <=
        (reciprocalQuarticMinusOneUnitDyadicCompute m).hi /\
      (reciprocalQuarticMinusOneUnitDyadicCompute m).hi <=
        (reciprocalQuarticMinusOneUnitDyadicCompute n).hi := by
  induction hnm with
  | refl =>
      have hordered := reciprocalQuarticMinusOneUnitDyadicCompute_ordered n
      unfold QInterval.width at hordered
      have hmid :
          (reciprocalQuarticMinusOneUnitDyadicCompute n).lo <=
            (reciprocalQuarticMinusOneUnitDyadicCompute n).hi := by
        grind [Rat.sub_eq_add_neg]
      exact ⟨Rat.le_refl, hmid, Rat.le_refl⟩
  | step hnm ih =>
      rename_i k
      have hstep := reciprocalQuarticMinusOneUnitDyadicCompute_step_refines k
      have hordered :=
        reciprocalQuarticMinusOneUnitDyadicCompute_ordered (k + 1)
      unfold QInterval.width at hordered
      have hmid :
          (reciprocalQuarticMinusOneUnitDyadicCompute (k + 1)).lo <=
            (reciprocalQuarticMinusOneUnitDyadicCompute (k + 1)).hi := by
        grind [Rat.sub_eq_add_neg]
      exact ⟨Rat.le_trans ih.1 hstep.1, hmid,
        Rat.le_trans hstep.2 ih.2.2⟩

private theorem reciprocalQuarticMinusOneUnit_succ_le_two_pow (n : Nat) :
    n + 1 <= 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        n + 1 + 1 <= 2 * (n + 1) := by omega
        _ <= 2 * 2 ^ n := Nat.mul_le_mul_left 2 ih
        _ = 2 ^ (n + 1) := by
          rw [Nat.pow_succ]
          omega

theorem reciprocalQuarticMinusOneUnitDyadicCompute_width_le_nat_over_succ
    (stage : Nat) :
    (reciprocalQuarticMinusOneUnitDyadicCompute stage).width <=
      (64 : Rat) / (((stage + 1 : Nat) : Rat)) := by
  rw [reciprocalQuarticMinusOneUnitDyadicCompute_width]
  have hpow : stage + 1 <= 2 ^ stage :=
    reciprocalQuarticMinusOneUnit_succ_le_two_pow stage
  have hinv :
      1 / (((2 ^ stage : Nat) : Rat)) <=
        1 / (((stage + 1 : Nat) : Rat)) :=
    FTC.one_div_nat_antitone (Nat.succ_pos stage)
      (Nat.pow_pos (by omega : 0 < 2)) hpow
  calc
    64 * (1 / (((2 ^ stage : Nat) : Rat))) <=
      64 * (1 / (((stage + 1 : Nat) : Rat))) :=
      Rat.mul_le_mul_of_nonneg_left hinv (by native_decide)
    _ = (64 : Rat) / (((stage + 1 : Nat) : Rat)) := by
      rw [Rat.div_def]
      grind [Rat.mul_assoc]

private theorem reciprocalQuarticMinusOneUnit_widthsShrink_of_natOverSuccBound
    {compute : Nat -> QInterval} {C : Nat}
    (hbound : forall n,
      (compute n).width <= (C : Rat) / (((n + 1 : Nat) : Rat))) :
    RealRaw.WidthsShrinkToZero compute := by
  intro eps
  refine ⟨C * (eps.val.den + 1), ?_⟩
  intro n hn
  have hmain :
      (C : Rat) / (((n + 1 : Nat) : Rat)) <=
        1 / (((eps.val.den + 1 : Nat) : Rat)) := by
    let A : Rat := ((n + 1 : Nat) : Rat)
    let B : Rat := ((eps.val.den + 1 : Nat) : Rat)
    let K : Rat := (C : Rat)
    have hApos : 0 < A := by
      dsimp [A]
      exact (Rat.natCast_pos).2 (Nat.succ_pos n)
    have hBpos : 0 < B := by
      dsimp [B]
      exact (Rat.natCast_pos).2 (Nat.succ_pos eps.val.den)
    have hAne : A ≠ 0 := Rat.ne_of_gt hApos
    have hBne : B ≠ 0 := Rat.ne_of_gt hBpos
    have hABpos : 0 < A * B := Rat.mul_pos hApos hBpos
    have hscaledRat : K * B <= A := by
      dsimp [A, B, K]
      exact_mod_cast (by omega :
        C * (eps.val.den + 1) <= n + 1)
    apply Rat.le_of_mul_le_mul_right (c := A * B)
    · calc
        (K / A) * (A * B) = K * B := by
          rw [Rat.div_def]
          grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
        _ <= A := hscaledRat
        _ = (1 / B) * (A * B) := by
          rw [Rat.div_def]
          grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
    · exact hABpos
  exact Rat.le_trans (hbound n)
    (Rat.le_trans hmain
      (FTC.one_div_den_succ_le_of_pos eps.property))

theorem reciprocalQuarticMinusOneUnitDyadicCompute_widthsShrink :
    RealRaw.WidthsShrinkToZero reciprocalQuarticMinusOneUnitDyadicCompute :=
  reciprocalQuarticMinusOneUnit_widthsShrink_of_natOverSuccBound
    reciprocalQuarticMinusOneUnitDyadicCompute_width_le_nat_over_succ

/-- The completed raw interval algorithm obtained from the dyadic Lipschitz
brackets.  At stage n its width is exactly 64 divided by 2^n; its nestedness
comes from the finite midpoint-refinement inequalities above. -/
def reciprocalQuarticMinusOneUnitDyadicRaw : RealRaw where
  compute := reciprocalQuarticMinusOneUnitDyadicCompute

theorem reciprocalQuarticMinusOneUnitDyadicRaw_valid :
    reciprocalQuarticMinusOneUnitDyadicRaw.Valid := by
  change RealRaw.ValidCompute reciprocalQuarticMinusOneUnitDyadicCompute
  exact ⟨reciprocalQuarticMinusOneUnitDyadicCompute_ordered,
    reciprocalQuarticMinusOneUnitDyadicCompute_nested,
    reciprocalQuarticMinusOneUnitDyadicCompute_widthsShrink⟩

/-- The exact rational-name evaluator for the affine compact density. -/
def reciprocalQuarticMinusOneUnitRaw : PartialRealFunRaw where
  definedAt := fun _ => True
  compute := fun t _ _ =>
    let y := reciprocalQuarticMinusOneUnitDensity t
    { lo := y, hi := y }

/-- The affine compact quartic density as a total interval function on
[0,1]. -/
def reciprocalQuarticMinusOneUnitOnInterval : FunctionOnInterval where
  raw := reciprocalQuarticMinusOneUnitRaw
  lower := 0
  upper := 1
  defined_on := fun _ _ => trivial
  valid_on := by
    intro t _ht
    simpa [reciprocalQuarticMinusOneUnitRaw] using
      RealRaw.ofRat_valid (reciprocalQuarticMinusOneUnitDensity t)

/-- The concrete domain-aware integral construction for the affine compact
quartic density.  Unlike the earlier unconstrained placeholder interface, its
computation is visibly the finite left-cell Lipschitz bracket defined above. -/
def reciprocalQuarticMinusOneUnitDyadicConstruction :
    Integral.ConstructionFor reciprocalQuarticMinusOneUnitOnInterval where
  compute := reciprocalQuarticMinusOneUnitDyadicCompute
  certificate := reciprocalQuarticMinusOneUnitDyadicRaw_valid

def reciprocalQuarticMinusOneUnitDyadicIntegral : RealRaw :=
  Integral.integralFor reciprocalQuarticMinusOneUnitOnInterval
    reciprocalQuarticMinusOneUnitDyadicConstruction

theorem reciprocalQuarticMinusOneUnitDyadicIntegral_valid :
    reciprocalQuarticMinusOneUnitDyadicIntegral.Valid :=
  Integral.integralFor_valid reciprocalQuarticMinusOneUnitOnInterval
    reciprocalQuarticMinusOneUnitDyadicConstruction

theorem reciprocalQuarticMinusOneUnitDyadicIntegral_compute_eq (stage : Nat) :
    reciprocalQuarticMinusOneUnitDyadicIntegral.compute stage =
      reciprocalQuarticMinusOneUnitDyadicCompute stage :=
  rfl

/-- The affine unit density is the compact density composed with
x = 2t - 1, multiplied by its rational Jacobian. -/
theorem reciprocalQuarticMinusOneUnitDensity_eq_affineCompact (t : Rat) :
    reciprocalQuarticMinusOneUnitDensity t =
      2 * reciprocalQuarticSymmetricDensity (-1) (2 * t - 1) :=
  rfl

/-- The same dyadic bracket, now packaged for the actual compact density on
[-1,1].  Its finite cell expression is the affine unit construction above,
with the exact rational Jacobian already included in the integrand. -/
def reciprocalQuarticMinusOneCompactDyadicConstruction :
    Integral.ConstructionFor
      (reciprocalQuarticMinusOneCompactOnInterval (-1) 1) where
  compute := reciprocalQuarticMinusOneUnitDyadicCompute
  certificate := reciprocalQuarticMinusOneUnitDyadicRaw_valid

def reciprocalQuarticMinusOneCompactDyadicIntegral : RealRaw :=
  Integral.integralFor
    (reciprocalQuarticMinusOneCompactOnInterval (-1) 1)
    reciprocalQuarticMinusOneCompactDyadicConstruction

theorem reciprocalQuarticMinusOneCompactDyadicIntegral_valid :
    reciprocalQuarticMinusOneCompactDyadicIntegral.Valid :=
  Integral.integralFor_valid
    (reciprocalQuarticMinusOneCompactOnInterval (-1) 1)
    reciprocalQuarticMinusOneCompactDyadicConstruction

theorem reciprocalQuarticMinusOneCompactDyadicIntegral_compute_eq
    (stage : Nat) :
    reciprocalQuarticMinusOneCompactDyadicIntegral.compute stage =
      reciprocalQuarticMinusOneUnitDyadicCompute stage :=
  rfl

theorem reciprocalQuarticMinusOneCompact_existsConstruction :
    Integral.ExistsConstructionFor
      (reciprocalQuarticMinusOneCompactOnInterval (-1) 1) :=
  ⟨reciprocalQuarticMinusOneCompactDyadicConstruction⟩

/-- The finite compact interval integral that represents the clean
projective-line quartic route.  Its integrand is the explicit density obtained
after the rational compactification of the line; a future route must therefore
provide an integral construction for this particular function, rather than an
unconstrained raw real. -/
def reciprocalQuarticMinusOneCompactIntegral
    (construction : Integral.ConstructionFor
      (reciprocalQuarticMinusOneCompactOnInterval (-1) 1)) : RealRaw :=
  Integral.integralFor (reciprocalQuarticMinusOneCompactOnInterval (-1) 1)
    construction

theorem reciprocalQuarticMinusOneCompactIntegral_valid
    (construction : Integral.ConstructionFor
      (reciprocalQuarticMinusOneCompactOnInterval (-1) 1)) :
    (reciprocalQuarticMinusOneCompactIntegral construction).Valid :=
  Integral.integralFor_valid _ construction

/-- The theorem-facing obligation for the compactified clean reciprocal
quartic integral.  The required equality is now tied to a construction for
the actual compact density on `[-1,1]`. -/
def ReciprocalQuarticMinusOneProjectiveAgreement
    (construction : Integral.ConstructionFor
      (reciprocalQuarticMinusOneCompactOnInterval (-1) 1)) : Prop :=
  (reciprocalQuarticMinusOneCompactIntegral construction).Equiv
    reciprocalQuarticMinusOneExpectedPi

/-- Data for the clean reciprocal quartic pi route.  The finite algebraic
pullback and compact interval integrand are formalized above.  What remains is
an analytic certificate that a concrete integral construction for that density
computes the expected pi value. -/
structure ReciprocalQuarticMinusOneProjectiveRoute where
  compactConstruction : Integral.ConstructionFor
    (reciprocalQuarticMinusOneCompactOnInterval (-1) 1)
  computes_expected :
    ReciprocalQuarticMinusOneProjectiveAgreement compactConstruction

namespace ReciprocalQuarticMinusOneProjectiveRoute

/-- The projective-line integral is definitionally the finite integral of the
compactified rational density. -/
def projectiveIntegral (R : ReciprocalQuarticMinusOneProjectiveRoute) : RealRaw :=
  reciprocalQuarticMinusOneCompactIntegral R.compactConstruction

theorem projectiveIntegral_valid (R : ReciprocalQuarticMinusOneProjectiveRoute) :
    R.projectiveIntegral.Valid :=
  reciprocalQuarticMinusOneCompactIntegral_valid R.compactConstruction

end ReciprocalQuarticMinusOneProjectiveRoute

/-- Folding the positive half-line by the reciprocal map produces the symmetric
density \((1+x^2)/(x^4+a x^2+1)\) on the unit interval. -/
theorem reciprocalQuarticUnitFoldDensity_eq_symmetric
    (a x : Rat) (hx : x ≠ 0)
    (hQ : reciprocalQuarticDenominator a x ≠ 0)
    (hQrec : reciprocalQuarticDenominator a (1 / x) ≠ 0) :
    reciprocalQuarticUnitFoldDensity a x =
      reciprocalQuarticSymmetricDensity a x := by
  apply rat_eq_of_mul_eq_mul_ne (c := reciprocalQuarticDenominator a x) hQ
  have hrec := reciprocalQuarticDenominator_reciprocal_cleared a x hx
  have hx2 : x * x ≠ 0 := Rat.ne_of_gt (rat_square_pos_of_ne_zero hx)
  calc
    reciprocalQuarticUnitFoldDensity a x *
        reciprocalQuarticDenominator a x
        = 1 + x * x := by
          unfold reciprocalQuarticUnitFoldDensity reciprocalQuarticKernel
          rw [Rat.add_mul, Rat.div_def, Rat.div_def, Rat.div_def]
          rw [← hrec]
          grind [Rat.mul_add, Rat.add_mul, Rat.add_assoc, Rat.add_comm,
            Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
    _ = reciprocalQuarticSymmetricDensity a x *
        reciprocalQuarticDenominator a x := by
          unfold reciprocalQuarticSymmetricDensity reciprocalQuarticKernel
          rw [Rat.div_def]
          grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

/-- The exact pullback-density identity for the reciprocal quartic test
integral.  The positivity hypotheses needed in analysis will imply the two
nonzero denominator assumptions here. -/
theorem reciprocalQuarticSymmetricDensity_eq_pullback_shiftedCauchy
    (a x : Rat) (hx : x ≠ 0)
    (hQ : reciprocalQuarticDenominator a x ≠ 0)
    (hE : shiftedCauchyDenominator a (reciprocalDifference x) ≠ 0) :
    reciprocalQuarticSymmetricDensity a x =
      reciprocalDifferenceJacobian x *
        shiftedCauchyKernel a (reciprocalDifference x) := by
  apply rat_eq_of_mul_eq_mul_ne (c := reciprocalQuarticDenominator a x) hQ
  calc
    reciprocalQuarticSymmetricDensity a x *
        reciprocalQuarticDenominator a x
        = 1 + x * x := by
          unfold reciprocalQuarticSymmetricDensity reciprocalQuarticKernel
          rw [Rat.div_def]
          grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
    _ = (reciprocalDifferenceJacobian x *
          shiftedCauchyKernel a (reciprocalDifference x)) *
          reciprocalQuarticDenominator a x := by
          have hden :=
            reciprocalDifference_quartic_denominator a x hx
          have hjac :=
            reciprocalDifferenceJacobian_square_cleared x hx
          unfold shiftedCauchyKernel
          rw [Rat.div_def]
          rw [← hden]
          grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

/-- The whole finite algebra chain used by the reciprocal quartic test:
fold the positive half-line by \(x\leftrightarrow1/x\), then substitute
`u = x - 1/x`. -/
theorem reciprocalQuarticUnitFoldDensity_eq_pullback_shiftedCauchy
    (a x : Rat) (hx : x ≠ 0)
    (hQ : reciprocalQuarticDenominator a x ≠ 0)
    (hQrec : reciprocalQuarticDenominator a (1 / x) ≠ 0)
    (hE : shiftedCauchyDenominator a (reciprocalDifference x) ≠ 0) :
    reciprocalQuarticUnitFoldDensity a x =
      reciprocalDifferenceJacobian x *
        shiftedCauchyKernel a (reciprocalDifference x) := by
  rw [reciprocalQuarticUnitFoldDensity_eq_symmetric a x hx hQ hQrec]
  exact reciprocalQuarticSymmetricDensity_eq_pullback_shiftedCauchy
    a x hx hQ hE

/-- The denominator-free specialization of the full finite algebra chain for
the pi-producing quartic \(x^4-x^2+1\). -/
theorem reciprocalQuarticUnitFoldDensity_minus_one_eq_pullback_shiftedCauchy
    (x : Rat) (hx : x ≠ 0) :
    reciprocalQuarticUnitFoldDensity (-1) x =
      reciprocalDifferenceJacobian x *
        shiftedCauchyKernel (-1) (reciprocalDifference x) := by
  exact reciprocalQuarticUnitFoldDensity_eq_pullback_shiftedCauchy
    (-1) x hx
    (Rat.ne_of_gt (reciprocalQuarticDenominator_minus_one_pos x))
    (Rat.ne_of_gt (reciprocalQuarticDenominator_minus_one_pos (1 / x)))
    (Rat.ne_of_gt
      (shiftedCauchyDenominator_minus_one_pos (reciprocalDifference x)))

/-- The denominator-free pi-case pullback, stated directly with the arctangent
kernel used by the rectangle construction. -/
theorem reciprocalQuarticUnitFoldDensity_minus_one_eq_pullback_integralKernel
    (x : Rat) (hx : x ≠ 0) :
    reciprocalQuarticUnitFoldDensity (-1) x =
      reciprocalDifferenceJacobian x *
        ArctanGeometry.integralKernel (reciprocalDifference x) := by
  rw [reciprocalQuarticUnitFoldDensity_minus_one_eq_pullback_shiftedCauchy x hx]
  rw [shiftedCauchyKernel_minus_one_eq_integralKernel]

/-- The geometric cosine algorithm, restricted to a rational interval where it
is defined. -/
def geometricCosOnInterval
    (C : RationalCircle.GeometricTrig.FunctionRawConstruction)
    (a b : Rat)
    (hdefined :
      forall x, inDomainInterval a b x -> C.cosFunctionRaw.definedAt x) :
    FunctionOnInterval where
  raw := {
    definedAt := inDomainInterval a b
    compute := fun x hx => C.cosFunctionRaw.compute x (hdefined x hx)
  }
  lower := a
  upper := b
  defined_on := fun _ hx => hx
  valid_on := by
    intro x hx
    exact C.cosFunctionRaw_valid x (hdefined x hx)

/-- The geometric sine algorithm, restricted to a rational interval where it
is defined. -/
def geometricSinOnInterval
    (C : RationalCircle.GeometricTrig.FunctionRawConstruction)
    (a b : Rat)
    (hdefined :
      forall x, inDomainInterval a b x -> C.sinFunctionRaw.definedAt x) :
    FunctionOnInterval where
  raw := {
    definedAt := inDomainInterval a b
    compute := fun x hx => C.sinFunctionRaw.compute x (hdefined x hx)
  }
  lower := a
  upper := b
  defined_on := fun _ hx => hx
  valid_on := by
    intro x hx
    exact C.sinFunctionRaw_valid x (hdefined x hx)

theorem geometricCosOnInterval_valid
    (C : RationalCircle.GeometricTrig.FunctionRawConstruction)
    (a b : Rat)
    (hdefined :
      forall x, inDomainInterval a b x -> C.cosFunctionRaw.definedAt x) :
    forall x hx,
      RealRaw.ValidCompute
        ((geometricCosOnInterval C a b hdefined).compute x hx) := by
  intro x hx
  exact (geometricCosOnInterval C a b hdefined).valid_on
    x ((geometricCosOnInterval C a b hdefined).defined_on x hx)

theorem geometricSinOnInterval_valid
    (C : RationalCircle.GeometricTrig.FunctionRawConstruction)
    (a b : Rat)
    (hdefined :
      forall x, inDomainInterval a b x -> C.sinFunctionRaw.definedAt x) :
    forall x hx,
      RealRaw.ValidCompute
        ((geometricSinOnInterval C a b hdefined).compute x hx) := by
  intro x hx
  exact (geometricSinOnInterval C a b hdefined).valid_on
    x ((geometricSinOnInterval C a b hdefined).defined_on x hx)

/-- The target package saying that geometric sine and cosine satisfy their
definite-integral identities on a chosen rational interval.  The derivative
proofs and the integral constructions are supplied as data. -/
structure GeometricTrigIntegralIdentities
    (C : RationalCircle.GeometricTrig.FunctionRawConstruction)
    (a b : Rat) where
  cos_defined :
    forall x, inDomainInterval a b x -> C.cosFunctionRaw.definedAt x
  sin_defined :
    forall x, inDomainInterval a b x -> C.sinFunctionRaw.definedAt x
  negCos : FunctionOnInterval
  integral_cos_eq_sin :
    Integral.DefiniteIdentityOnInterval
      (geometricCosOnInterval C a b cos_defined)
      (geometricSinOnInterval C a b sin_defined)
  integral_sin_eq_negCos :
    Integral.DefiniteIdentityOnInterval
      (geometricSinOnInterval C a b sin_defined)
      negCos

namespace GeometricTrigIntegralIdentities

def cosOnInterval
    {C : RationalCircle.GeometricTrig.FunctionRawConstruction}
    {a b : Rat}
    (H : GeometricTrigIntegralIdentities C a b) :
    FunctionOnInterval :=
  geometricCosOnInterval C a b H.cos_defined

def sinOnInterval
    {C : RationalCircle.GeometricTrig.FunctionRawConstruction}
    {a b : Rat}
    (H : GeometricTrigIntegralIdentities C a b) :
    FunctionOnInterval :=
  geometricSinOnInterval C a b H.sin_defined

theorem cos_integral_valid
    {C : RationalCircle.GeometricTrig.FunctionRawConstruction}
    {a b : Rat}
    (H : GeometricTrigIntegralIdentities C a b) :
    (Integral.integral
      (H.cosOnInterval).toRealFunRaw
      (H.cosOnInterval).lower
      (H.cosOnInterval).upper
      H.integral_cos_eq_sin.construction).Valid :=
  H.integral_cos_eq_sin.integral_valid

theorem sin_integral_valid
    {C : RationalCircle.GeometricTrig.FunctionRawConstruction}
    {a b : Rat}
    (H : GeometricTrigIntegralIdentities C a b) :
    (Integral.integral
      (H.sinOnInterval).toRealFunRaw
      (H.sinOnInterval).lower
      (H.sinOnInterval).upper
      H.integral_sin_eq_negCos.construction).Valid :=
  H.integral_sin_eq_negCos.integral_valid

end GeometricTrigIntegralIdentities

/-- Inverse elementary functions represented by the kernels that a calculus
student would recognize.  These identities are deliberately interval-local:
the branch and endpoint choices are part of the data. -/
structure InverseElementaryIntegralIdentities where
  arctan : FunctionOnInterval
  arctanKernel : FunctionOnInterval
  integral_invOnePlusSquare_eq_arctan :
    Integral.DefiniteIdentityOnInterval arctanKernel arctan
  arcsin : FunctionOnInterval
  arcsinKernel : FunctionOnInterval
  integral_invSqrtOneMinusSquare_eq_arcsin :
    Integral.DefiniteIdentityOnInterval arcsinKernel arcsin
  log : FunctionOnInterval
  logKernel : FunctionOnInterval
  integral_invX_eq_log :
    Integral.DefiniteIdentityOnInterval logKernel log

/-- Abelian-integral forms related to trigonometric and inverse-trigonometric
functions.  The first two are inverse representations; elliptic integrals are
included as the next natural Abelian family beyond circular trigonometry. -/
structure AbelianTrigIntegralRepresentations where
  arcsinInverse : AbelianIntegral.InverseRepresentation
  arctanInverse : AbelianIntegral.InverseRepresentation
  sine_agrees_with_arcsinInverse :
    ComputableAnalysis.sin.agreesWithAbelianInverseRep arcsinInverse
  cosine_agrees_with_arctanInverse :
    ComputableAnalysis.cos.agreesWithAbelianInverseRep arctanInverse
  ellipticDifferential : AbelianIntegral.DifferentialRaw
  ellipticIntegral : AbelianIntegral.Raw

end IntegralIdentities

end ComputableAnalysis
