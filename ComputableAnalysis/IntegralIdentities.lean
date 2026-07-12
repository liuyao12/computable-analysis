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

/-- Machin's pi computation assembled directly from the certified
midpoint-rectangle integrals of `1 / (1 + t^2)` at its two rational inputs.

This is a separate calculus computation from the power-series `piMachin`:
each occurrence of arctangent is an `Integral.ConstructionFor` evaluator. -/
def piMachinIntegralRectangle : RealRaw :=
  (4 : Nat) *
    ((4 : Nat) *
      arctanIntegralRectangleFor ((1 : Rat) / 5)
        (by native_decide) (by native_decide) -
      arctanIntegralRectangleFor ((1 : Rat) / 239)
        (by native_decide) (by native_decide))

theorem piMachinIntegralRectangle_valid :
    piMachinIntegralRectangle.Valid := by
  unfold piMachinIntegralRectangle
  exact RealRaw.natScale_valid 4
    (RealRaw.sub_valid
      (RealRaw.natScale_valid 4
        (arctanIntegralRectangleFor_valid ((1 : Rat) / 5)
          (by native_decide) (by native_decide)))
      (arctanIntegralRectangleFor_valid ((1 : Rat) / 239)
        (by native_decide) (by native_decide)))

/-- A transparent precision budget for the certified Machin rectangle
integral.  Each integral contributes at most `4/(n+1)`; interval subtraction
and the two natural scalings give the displayed `80/(n+1)` bound. -/
theorem piMachinIntegralRectangle_compute_width_le_eighty_div_succ
    (n : Nat) :
    (piMachinIntegralRectangle.compute n).width <=
      (80 : Rat) / (((n + 1 : Nat) : Rat)) := by
  let A : RealRaw := arctanIntegralRectangleFor ((1 : Rat) / 5)
    (by native_decide) (by native_decide)
  let B : RealRaw := arctanIntegralRectangleFor ((1 : Rat) / 239)
    (by native_decide) (by native_decide)
  let d : Rat := ((n + 1 : Nat) : Rat)
  have hA : (A.compute n).width <= (4 : Rat) / d := by
    dsimp [A, d]
    rw [arctanIntegralRectangleFor_compute_eq]
    exact ArctanGeometry.arctanIntegralRectangleCompute_width_le_four_div_succ
      (x := (1 : Rat) / 5) (by native_decide) (by native_decide) n
  have hB : (B.compute n).width <= (4 : Rat) / d := by
    dsimp [B, d]
    rw [arctanIntegralRectangleFor_compute_eq]
    exact ArctanGeometry.arctanIntegralRectangleCompute_width_le_four_div_succ
      (x := (1 : Rat) / 239) (by native_decide) (by native_decide) n
  have hscaled : (4 : Rat) * (A.compute n).width <=
      (4 : Rat) * ((4 : Rat) / d) :=
    Rat.mul_le_mul_of_nonneg_left hA (by native_decide)
  have hinner :
      (4 : Rat) * (A.compute n).width + (B.compute n).width <=
        (4 : Rat) * ((4 : Rat) / d) + (4 : Rat) / d := by
    calc
      (4 : Rat) * (A.compute n).width + (B.compute n).width <=
          (4 : Rat) * ((4 : Rat) / d) + (B.compute n).width :=
        (Rat.add_le_add_right).2 hscaled
      _ <= (4 : Rat) * ((4 : Rat) / d) + (4 : Rat) / d :=
        (Rat.add_le_add_left).2 hB
  change
    (((4 : Nat) * ((4 : Nat) * A - B) : RealRaw).compute n).width <=
      (80 : Rat) / d
  rw [RealRaw.natScale_width, RealRaw.sub_width, RealRaw.natScale_width]
  calc
    (4 : Rat) * ((4 : Rat) * (A.compute n).width + (B.compute n).width) <=
      (4 : Rat) * ((4 : Rat) * ((4 : Rat) / d) + (4 : Rat) / d) :=
        Rat.mul_le_mul_of_nonneg_left hinner (by native_decide)
    _ = (80 : Rat) / d := by
      grind [Rat.div_def, Rat.mul_add, Rat.mul_assoc, Rat.mul_comm]

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

/-- The global Farey-prefix construction for
`∫_a^b dt / (1 + t^2)`, packaged as a domain-aware integral construction.
The construction uses one shared Farey mesh and subtracts global prefixes, so
additivity over adjacent intervals is inherited from the raw Farey theorem. -/
def oneOverOnePlusSquareFareyConstruction
    (a b : Rat) :
    Integral.ConstructionFor (oneOverOnePlusSquareOnInterval a b) where
  compute := (ArctanGeometry.fareyIntegralBetweenRaw a b).compute
  certificate := ArctanGeometry.fareyIntegralBetweenRaw_valid a b

def oneOverOnePlusSquareFareyIntegral (a b : Rat) : RealRaw :=
  Integral.integralFor (oneOverOnePlusSquareOnInterval a b)
    (oneOverOnePlusSquareFareyConstruction a b)

theorem oneOverOnePlusSquareFareyIntegral_valid (a b : Rat) :
    (oneOverOnePlusSquareFareyIntegral a b).Valid :=
  Integral.integralFor_valid (oneOverOnePlusSquareOnInterval a b)
    (oneOverOnePlusSquareFareyConstruction a b)

theorem oneOverOnePlusSquareFareyIntegral_compute_eq
    (a b : Rat) (n : Nat) :
    (oneOverOnePlusSquareFareyIntegral a b).compute n =
      (ArctanGeometry.fareyIntegralBetweenRaw a b).compute n := rfl

theorem oneOverOnePlusSquareFareyIntegral_width_le_six_div_succ
    (a b : Rat) (n : Nat) :
    ((oneOverOnePlusSquareFareyIntegral a b).compute n).width <=
      (6 : Rat) / (((n + 1 : Nat) : Rat)) := by
  rw [oneOverOnePlusSquareFareyIntegral_compute_eq]
  exact ArctanGeometry.fareyIntegralBetweenRaw_width_le_six_div_succ a b n

theorem oneOverOnePlusSquareFareyIntegral_equiv_betweenRaw
    (a b : Rat) :
    (oneOverOnePlusSquareFareyIntegral a b).Equiv
      (ArctanGeometry.fareyIntegralBetweenRaw a b) := by
  intro n
  apply (RealRaw.compareAt_overlap_iff
    (oneOverOnePlusSquareFareyIntegral a b)
    (ArctanGeometry.fareyIntegralBetweenRaw a b) n n).2
  rw [oneOverOnePlusSquareFareyIntegral_compute_eq]
  have hordered :=
    (ArctanGeometry.fareyIntegralBetweenRaw_valid a b).1 n
  have hle :
      ((ArctanGeometry.fareyIntegralBetweenRaw a b).compute n).lo <=
        ((ArctanGeometry.fareyIntegralBetweenRaw a b).compute n).hi := by
    unfold QInterval.width at hordered
    grind [Rat.sub_eq_add_neg]
  exact ⟨hle, hle⟩

theorem oneOverOnePlusSquareFareyIntegral_additive
    (a b c : Rat) :
    (oneOverOnePlusSquareFareyIntegral a b +
      oneOverOnePlusSquareFareyIntegral b c).Equiv
        (oneOverOnePlusSquareFareyIntegral a c) := by
  have hleftValid :
      (oneOverOnePlusSquareFareyIntegral a b +
        oneOverOnePlusSquareFareyIntegral b c).Valid :=
    RealRaw.add_valid
      (oneOverOnePlusSquareFareyIntegral_valid a b)
      (oneOverOnePlusSquareFareyIntegral_valid b c)
  have hrawLeftValid :
      (ArctanGeometry.fareyIntegralBetweenRaw a b +
        ArctanGeometry.fareyIntegralBetweenRaw b c).Valid :=
    RealRaw.add_valid
      (ArctanGeometry.fareyIntegralBetweenRaw_valid a b)
      (ArctanGeometry.fareyIntegralBetweenRaw_valid b c)
  have hrawRightValid :
      (ArctanGeometry.fareyIntegralBetweenRaw a c).Valid :=
    ArctanGeometry.fareyIntegralBetweenRaw_valid a c
  have hrightValid :
      (oneOverOnePlusSquareFareyIntegral a c).Valid :=
    oneOverOnePlusSquareFareyIntegral_valid a c
  have hleftRaw :
      (oneOverOnePlusSquareFareyIntegral a b +
        oneOverOnePlusSquareFareyIntegral b c).Equiv
          (ArctanGeometry.fareyIntegralBetweenRaw a b +
            ArctanGeometry.fareyIntegralBetweenRaw b c) :=
    RealRaw.add_equiv
      (oneOverOnePlusSquareFareyIntegral_valid a b)
      (ArctanGeometry.fareyIntegralBetweenRaw_valid a b)
      (oneOverOnePlusSquareFareyIntegral_valid b c)
      (ArctanGeometry.fareyIntegralBetweenRaw_valid b c)
      (oneOverOnePlusSquareFareyIntegral_equiv_betweenRaw a b)
      (oneOverOnePlusSquareFareyIntegral_equiv_betweenRaw b c)
  have hrawToRight :
      (ArctanGeometry.fareyIntegralBetweenRaw a b +
        ArctanGeometry.fareyIntegralBetweenRaw b c).Equiv
          (oneOverOnePlusSquareFareyIntegral a c) :=
    RealRaw.equiv_trans hrawLeftValid hrawRightValid hrightValid
      (ArctanGeometry.fareyIntegralBetweenRaw_additive a b c)
      (RealRaw.equiv_symm
        (oneOverOnePlusSquareFareyIntegral_equiv_betweenRaw a c))
  exact RealRaw.equiv_trans hleftValid hrawLeftValid hrightValid
    hleftRaw hrawToRight

theorem oneOverOnePlusSquareFareyIntegral_self_equiv_zero
    (a : Rat) :
    (oneOverOnePlusSquareFareyIntegral a a).Equiv (RealRaw.ofRat 0) := by
  exact RealRaw.equiv_trans
    (oneOverOnePlusSquareFareyIntegral_valid a a)
    (ArctanGeometry.fareyIntegralBetweenRaw_valid a a)
    (RealRaw.ofRat_valid 0)
    (oneOverOnePlusSquareFareyIntegral_equiv_betweenRaw a a)
    (ArctanGeometry.fareyIntegralBetweenRaw_self_equiv_zero a)

theorem oneOverOnePlusSquareFareyIntegral_reverse_equiv_neg
    (a b : Rat) :
    (oneOverOnePlusSquareFareyIntegral a b).Equiv
      (-(oneOverOnePlusSquareFareyIntegral b a)) := by
  have hleftValid :
      (oneOverOnePlusSquareFareyIntegral a b).Valid :=
    oneOverOnePlusSquareFareyIntegral_valid a b
  have hrawLeftValid :
      (ArctanGeometry.fareyIntegralBetweenRaw a b).Valid :=
    ArctanGeometry.fareyIntegralBetweenRaw_valid a b
  have hnegRawValid :
      (-(ArctanGeometry.fareyIntegralBetweenRaw b a)).Valid :=
    RealRaw.neg_valid
      (ArctanGeometry.fareyIntegralBetweenRaw_valid b a)
  have hnegRightValid :
      (-(oneOverOnePlusSquareFareyIntegral b a)).Valid :=
    RealRaw.neg_valid (oneOverOnePlusSquareFareyIntegral_valid b a)
  have hrawToNegIntegral :
      (ArctanGeometry.fareyIntegralBetweenRaw a b).Equiv
        (-(oneOverOnePlusSquareFareyIntegral b a)) :=
    RealRaw.equiv_trans hrawLeftValid hnegRawValid hnegRightValid
      (ArctanGeometry.fareyIntegralBetweenRaw_reverse_equiv_neg a b)
      (RealRaw.neg_equiv
        (RealRaw.equiv_symm
          (oneOverOnePlusSquareFareyIntegral_equiv_betweenRaw b a)))
  exact RealRaw.equiv_trans hleftValid hrawLeftValid hnegRightValid
    (oneOverOnePlusSquareFareyIntegral_equiv_betweenRaw a b)
    hrawToNegIntegral

theorem oneOverOnePlusSquareFareyIntegral_add_reverse_equiv_zero
    (a b : Rat) :
    (oneOverOnePlusSquareFareyIntegral a b +
      oneOverOnePlusSquareFareyIntegral b a).Equiv (RealRaw.ofRat 0) := by
  have hleftValid :
      (oneOverOnePlusSquareFareyIntegral a b +
        oneOverOnePlusSquareFareyIntegral b a).Valid :=
    RealRaw.add_valid
      (oneOverOnePlusSquareFareyIntegral_valid a b)
      (oneOverOnePlusSquareFareyIntegral_valid b a)
  have hselfValid :
      (oneOverOnePlusSquareFareyIntegral a a).Valid :=
    oneOverOnePlusSquareFareyIntegral_valid a a
  exact RealRaw.equiv_trans hleftValid hselfValid (RealRaw.ofRat_valid 0)
    (oneOverOnePlusSquareFareyIntegral_additive a b a)
    (oneOverOnePlusSquareFareyIntegral_self_equiv_zero a)

theorem oneOverOnePlusSquareFareyIntegral_zero_left_equiv_prefix
    (x : Rat) :
    (oneOverOnePlusSquareFareyIntegral 0 x).Equiv
      (ArctanGeometry.fareyIntegralPrefixRaw x) := by
  exact RealRaw.equiv_trans
    (oneOverOnePlusSquareFareyIntegral_valid 0 x)
    (ArctanGeometry.fareyIntegralBetweenRaw_valid 0 x)
    (ArctanGeometry.fareyIntegralPrefixRaw_valid x)
    (oneOverOnePlusSquareFareyIntegral_equiv_betweenRaw 0 x)
    (ArctanGeometry.fareyIntegralBetweenRaw_zero_left_equiv_prefix x)

theorem oneOverOnePlusSquareFareyIntegral_zero_right_equiv_neg_prefix
    (x : Rat) :
    (oneOverOnePlusSquareFareyIntegral x 0).Equiv
      (-(ArctanGeometry.fareyIntegralPrefixRaw x)) := by
  have hleftValid :
      (oneOverOnePlusSquareFareyIntegral x 0).Valid :=
    oneOverOnePlusSquareFareyIntegral_valid x 0
  have hrawValid :
      (ArctanGeometry.fareyIntegralBetweenRaw x 0).Valid :=
    ArctanGeometry.fareyIntegralBetweenRaw_valid x 0
  have hnegPrefixValid :
      (-(ArctanGeometry.fareyIntegralPrefixRaw x)).Valid :=
    RealRaw.neg_valid (ArctanGeometry.fareyIntegralPrefixRaw_valid x)
  exact RealRaw.equiv_trans hleftValid hrawValid hnegPrefixValid
    (oneOverOnePlusSquareFareyIntegral_equiv_betweenRaw x 0)
    (ArctanGeometry.fareyIntegralBetweenRaw_zero_right_equiv_neg_prefix x)

/-- The global Farey-prefix construction for
`∫_0^x dt / (1 + t^2)`, packaged as a domain-aware integral construction.
Unlike the rectangle route, this uses one shared Farey mesh for all endpoints
and then subtracts prefixes. -/
def arctanIntegralFareyConstruction
    (x : Rat) : Integral.ConstructionFor (arctanKernelInterval x) where
  compute := (oneOverOnePlusSquareFareyIntegral 0 x).compute
  certificate := oneOverOnePlusSquareFareyIntegral_valid 0 x

def arctanIntegralFareyFor (x : Rat) : RealRaw :=
  Integral.integralFor (arctanKernelInterval x)
    (arctanIntegralFareyConstruction x)

theorem arctanIntegralFareyFor_valid (x : Rat) :
    (arctanIntegralFareyFor x).Valid :=
  Integral.integralFor_valid (arctanKernelInterval x)
    (arctanIntegralFareyConstruction x)

theorem arctanIntegralFareyFor_compute_eq (x : Rat) (n : Nat) :
    (arctanIntegralFareyFor x).compute n =
      (oneOverOnePlusSquareFareyIntegral 0 x).compute n := rfl

theorem arctanIntegralFareyFor_equiv_fareyIntegral (x : Rat) :
    (arctanIntegralFareyFor x).Equiv
      (oneOverOnePlusSquareFareyIntegral 0 x) := by
  intro n
  apply (RealRaw.compareAt_overlap_iff
    (arctanIntegralFareyFor x)
    (oneOverOnePlusSquareFareyIntegral 0 x) n n).2
  rw [arctanIntegralFareyFor_compute_eq]
  have hordered :=
    (oneOverOnePlusSquareFareyIntegral_valid 0 x).1 n
  have hle :
      ((oneOverOnePlusSquareFareyIntegral 0 x).compute n).lo <=
        ((oneOverOnePlusSquareFareyIntegral 0 x).compute n).hi := by
    unfold QInterval.width at hordered
    grind [Rat.sub_eq_add_neg]
  exact ⟨hle, hle⟩

theorem arctanIntegralFareyFor_equiv_betweenRaw (x : Rat) :
    (arctanIntegralFareyFor x).Equiv
      (ArctanGeometry.fareyIntegralBetweenRaw 0 x) := by
  exact RealRaw.equiv_trans
    (arctanIntegralFareyFor_valid x)
    (oneOverOnePlusSquareFareyIntegral_valid 0 x)
    (ArctanGeometry.fareyIntegralBetweenRaw_valid 0 x)
    (arctanIntegralFareyFor_equiv_fareyIntegral x)
    (oneOverOnePlusSquareFareyIntegral_equiv_betweenRaw 0 x)

theorem arctanIntegralFareyFor_equiv_prefix (x : Rat) :
    (arctanIntegralFareyFor x).Equiv
      (ArctanGeometry.fareyIntegralPrefixRaw x) := by
  exact RealRaw.equiv_trans
    (arctanIntegralFareyFor_valid x)
    (ArctanGeometry.fareyIntegralBetweenRaw_valid 0 x)
    (ArctanGeometry.fareyIntegralPrefixRaw_valid x)
    (arctanIntegralFareyFor_equiv_betweenRaw x)
    (ArctanGeometry.fareyIntegralBetweenRaw_zero_left_equiv_prefix x)

theorem arctanIntegralFareyFor_equiv_arctanGeom
    (x : Rat) (hx0 : 0 <= x) (hx1 : x <= 1) :
    (arctanIntegralFareyFor x).Equiv
      (ArctanGeometry.arctanGeom x) :=
  RealRaw.equiv_trans
    (arctanIntegralFareyFor_valid x)
    (ArctanGeometry.fareyIntegralPrefixRaw_valid x)
    (ArctanGeometry.arctanGeom_valid_on_unit hx0 hx1)
    (arctanIntegralFareyFor_equiv_prefix x)
    (ArctanGeometry.fareyIntegralPrefixRaw_equiv_arctanGeom_on_unit
      hx0 hx1)

/-- A two-term rational arctangent pi computation, evaluated using the shared
Farey integral construction.  The rational tangent identity
`atan(1/2) + atan(1/3) = atan(1)` is proved in the companion proof layer by
finite chart transport. -/
def piTwoThreeIntegralFarey : RealRaw :=
  (4 : Nat) *
    (arctanIntegralFareyFor ((1 : Rat) / 2) +
      arctanIntegralFareyFor ((1 : Rat) / 3))

theorem piTwoThreeIntegralFarey_valid :
    piTwoThreeIntegralFarey.Valid := by
  unfold piTwoThreeIntegralFarey
  exact RealRaw.natScale_valid 4
    (RealRaw.add_valid
      (arctanIntegralFareyFor_valid ((1 : Rat) / 2))
      (arctanIntegralFareyFor_valid ((1 : Rat) / 3)))

/-- The shared Farey mesh gives a direct public precision budget for the
two-three arctangent formula.  Each bounded integral has width at most
`6/(n+1)`, and the outer factor four yields `48/(n+1)`. -/
theorem piTwoThreeIntegralFarey_compute_width_le_fortyEight_div_succ
    (n : Nat) :
    (piTwoThreeIntegralFarey.compute n).width <=
      (48 : Rat) / (((n + 1 : Nat) : Rat)) := by
  let A : RealRaw := arctanIntegralFareyFor ((1 : Rat) / 2)
  let B : RealRaw := arctanIntegralFareyFor ((1 : Rat) / 3)
  let d : Rat := ((n + 1 : Nat) : Rat)
  have hA : (A.compute n).width <= (6 : Rat) / d := by
    dsimp [A, d]
    rw [arctanIntegralFareyFor_compute_eq]
    exact oneOverOnePlusSquareFareyIntegral_width_le_six_div_succ 0
      ((1 : Rat) / 2) n
  have hB : (B.compute n).width <= (6 : Rat) / d := by
    dsimp [B, d]
    rw [arctanIntegralFareyFor_compute_eq]
    exact oneOverOnePlusSquareFareyIntegral_width_le_six_div_succ 0
      ((1 : Rat) / 3) n
  have hsum :
      (A.compute n).width + (B.compute n).width <=
        (6 : Rat) / d + (6 : Rat) / d :=
    calc
      (A.compute n).width + (B.compute n).width <=
          (6 : Rat) / d + (B.compute n).width :=
        (Rat.add_le_add_right).2 hA
      _ <= (6 : Rat) / d + (6 : Rat) / d :=
        (Rat.add_le_add_left).2 hB
  change (((4 : Nat) * (A + B) : RealRaw).compute n).width <=
    (48 : Rat) / d
  rw [RealRaw.natScale_width, RealRaw.add_width]
  calc
    (4 : Rat) * ((A.compute n).width + (B.compute n).width) <=
        (4 : Rat) * ((6 : Rat) / d + (6 : Rat) / d) :=
      Rat.mul_le_mul_of_nonneg_left hsum (by native_decide)
    _ = (48 : Rat) / d := by
      grind [Rat.div_def, Rat.mul_add, Rat.mul_assoc, Rat.mul_comm]

theorem arctanIntegralFareyFor_zero_equiv_zero :
    (arctanIntegralFareyFor 0).Equiv (RealRaw.ofRat 0) := by
  exact RealRaw.equiv_trans
    (arctanIntegralFareyFor_valid 0)
    (ArctanGeometry.fareyIntegralPrefixRaw_valid 0)
    (RealRaw.ofRat_valid 0)
    (arctanIntegralFareyFor_equiv_prefix 0)
    ArctanGeometry.fareyIntegralPrefixRaw_zero_equiv_zero

theorem arctanIntegralFareyFor_add_interval
    (a b : Rat) :
    (arctanIntegralFareyFor a +
      oneOverOnePlusSquareFareyIntegral a b).Equiv
        (arctanIntegralFareyFor b) := by
  have hleftValid :
      (arctanIntegralFareyFor a +
        oneOverOnePlusSquareFareyIntegral a b).Valid :=
    RealRaw.add_valid
      (arctanIntegralFareyFor_valid a)
      (oneOverOnePlusSquareFareyIntegral_valid a b)
  have hkernelLeftValid :
      (oneOverOnePlusSquareFareyIntegral 0 a +
        oneOverOnePlusSquareFareyIntegral a b).Valid :=
    RealRaw.add_valid
      (oneOverOnePlusSquareFareyIntegral_valid 0 a)
      (oneOverOnePlusSquareFareyIntegral_valid a b)
  have hkernelRightValid :
      (oneOverOnePlusSquareFareyIntegral 0 b).Valid :=
    oneOverOnePlusSquareFareyIntegral_valid 0 b
  have hrightValid :
      (arctanIntegralFareyFor b).Valid :=
    arctanIntegralFareyFor_valid b
  have hleftToKernel :
      (arctanIntegralFareyFor a +
        oneOverOnePlusSquareFareyIntegral a b).Equiv
          (oneOverOnePlusSquareFareyIntegral 0 a +
            oneOverOnePlusSquareFareyIntegral a b) :=
    RealRaw.add_equiv
      (arctanIntegralFareyFor_valid a)
      (oneOverOnePlusSquareFareyIntegral_valid 0 a)
      (oneOverOnePlusSquareFareyIntegral_valid a b)
      (oneOverOnePlusSquareFareyIntegral_valid a b)
      (arctanIntegralFareyFor_equiv_fareyIntegral a)
      (RealRaw.equiv_refl
        (oneOverOnePlusSquareFareyIntegral a b)
        (oneOverOnePlusSquareFareyIntegral_valid a b))
  have hkernelToRight :
      (oneOverOnePlusSquareFareyIntegral 0 a +
        oneOverOnePlusSquareFareyIntegral a b).Equiv
          (arctanIntegralFareyFor b) :=
    RealRaw.equiv_trans hkernelLeftValid hkernelRightValid hrightValid
      (oneOverOnePlusSquareFareyIntegral_additive 0 a b)
      (RealRaw.equiv_symm
        (arctanIntegralFareyFor_equiv_fareyIntegral b))
  exact RealRaw.equiv_trans hleftValid hkernelLeftValid hrightValid
    hleftToKernel hkernelToRight

theorem arctanIntegralFareyFor_equiv_add_interval
    (a b : Rat) :
    (arctanIntegralFareyFor b).Equiv
      (arctanIntegralFareyFor a +
        oneOverOnePlusSquareFareyIntegral a b) :=
  RealRaw.equiv_symm (arctanIntegralFareyFor_add_interval a b)

theorem arctanIntegralFareyFor_sub_interval
    (a b : Rat) :
    (arctanIntegralFareyFor b - arctanIntegralFareyFor a).Equiv
      (oneOverOnePlusSquareFareyIntegral a b) := by
  let A := arctanIntegralFareyFor a
  let B := arctanIntegralFareyFor b
  let J := oneOverOnePlusSquareFareyIntegral a b
  have hA : A.Valid := by
    dsimp [A]
    exact arctanIntegralFareyFor_valid a
  have hB : B.Valid := by
    dsimp [B]
    exact arctanIntegralFareyFor_valid b
  have hJ : J.Valid := by
    dsimp [J]
    exact oneOverOnePlusSquareFareyIntegral_valid a b
  have hsum : (A + J).Valid :=
    RealRaw.add_valid hA hJ
  have hsub : (B - A).Valid :=
    RealRaw.sub_valid hB hA
  have hcancelValid : ((A + J) - A).Valid :=
    RealRaw.sub_valid hsum hA
  have hBsum : B.Equiv (A + J) := by
    dsimp [A, B, J]
    exact arctanIntegralFareyFor_equiv_add_interval a b
  have hsubToCancel : (B - A).Equiv ((A + J) - A) :=
    RealRaw.sub_equiv hB hsum hA hA hBsum
      (RealRaw.equiv_refl A hA)
  have hcancel : ((A + J) - A).Equiv J :=
    RealRaw.add_sub_cancel_left_equiv hA hJ
  exact RealRaw.equiv_trans hsub hcancelValid hJ hsubToCancel hcancel

theorem oneOverOnePlusSquareFareyIntegral_equiv_arctanIntegralFareyFor_sub
    (a b : Rat) :
    (oneOverOnePlusSquareFareyIntegral a b).Equiv
      (arctanIntegralFareyFor b - arctanIntegralFareyFor a) :=
  RealRaw.equiv_symm (arctanIntegralFareyFor_sub_interval a b)

theorem arctanIntegralFareyFor_sub_interval_equiv_betweenRaw
    (a b : Rat) :
    (arctanIntegralFareyFor b - arctanIntegralFareyFor a).Equiv
      (ArctanGeometry.fareyIntegralBetweenRaw a b) := by
  exact RealRaw.equiv_trans
    (RealRaw.sub_valid
      (arctanIntegralFareyFor_valid b)
      (arctanIntegralFareyFor_valid a))
    (oneOverOnePlusSquareFareyIntegral_valid a b)
    (ArctanGeometry.fareyIntegralBetweenRaw_valid a b)
    (arctanIntegralFareyFor_sub_interval a b)
    (oneOverOnePlusSquareFareyIntegral_equiv_betweenRaw a b)

theorem fareyIntegralBetweenRaw_equiv_arctanIntegralFareyFor_sub
    (a b : Rat) :
    (ArctanGeometry.fareyIntegralBetweenRaw a b).Equiv
      (arctanIntegralFareyFor b - arctanIntegralFareyFor a) :=
  RealRaw.equiv_symm
    (arctanIntegralFareyFor_sub_interval_equiv_betweenRaw a b)

/-- The Farey arctangent primitive is additive by finite interval
subtraction:

`(F(b)-F(a)) + (F(c)-F(b)) = F(c)-F(a)`.

This is the primitive-difference form of additivity that later FTC-style pi
routes need.  The proof reduces both differences to the shared-Farey integral
on the corresponding interval and then uses the raw Farey additivity theorem. -/
theorem arctanIntegralFareyFor_sub_interval_additive
    (a b c : Rat) :
    ((arctanIntegralFareyFor b - arctanIntegralFareyFor a) +
      (arctanIntegralFareyFor c - arctanIntegralFareyFor b)).Equiv
        (arctanIntegralFareyFor c - arctanIntegralFareyFor a) := by
  let Fab := arctanIntegralFareyFor b - arctanIntegralFareyFor a
  let Fbc := arctanIntegralFareyFor c - arctanIntegralFareyFor b
  let Fac := arctanIntegralFareyFor c - arctanIntegralFareyFor a
  let Jab := oneOverOnePlusSquareFareyIntegral a b
  let Jbc := oneOverOnePlusSquareFareyIntegral b c
  let Jac := oneOverOnePlusSquareFareyIntegral a c
  have hFab : Fab.Valid := by
    dsimp [Fab]
    exact RealRaw.sub_valid
      (arctanIntegralFareyFor_valid b)
      (arctanIntegralFareyFor_valid a)
  have hFbc : Fbc.Valid := by
    dsimp [Fbc]
    exact RealRaw.sub_valid
      (arctanIntegralFareyFor_valid c)
      (arctanIntegralFareyFor_valid b)
  have hFac : Fac.Valid := by
    dsimp [Fac]
    exact RealRaw.sub_valid
      (arctanIntegralFareyFor_valid c)
      (arctanIntegralFareyFor_valid a)
  have hJab : Jab.Valid := by
    dsimp [Jab]
    exact oneOverOnePlusSquareFareyIntegral_valid a b
  have hJbc : Jbc.Valid := by
    dsimp [Jbc]
    exact oneOverOnePlusSquareFareyIntegral_valid b c
  have hJac : Jac.Valid := by
    dsimp [Jac]
    exact oneOverOnePlusSquareFareyIntegral_valid a c
  have hleftValid : (Fab + Fbc).Valid :=
    RealRaw.add_valid hFab hFbc
  have hkernelValid : (Jab + Jbc).Valid :=
    RealRaw.add_valid hJab hJbc
  have hleftToKernel : (Fab + Fbc).Equiv (Jab + Jbc) :=
    RealRaw.add_equiv hFab hJab hFbc hJbc
      (by
        dsimp [Fab, Jab]
        exact arctanIntegralFareyFor_sub_interval a b)
      (by
        dsimp [Fbc, Jbc]
        exact arctanIntegralFareyFor_sub_interval b c)
  have hkernelToRight : (Jab + Jbc).Equiv Fac :=
    RealRaw.equiv_trans hkernelValid hJac hFac
      (by
        dsimp [Jab, Jbc, Jac]
        exact oneOverOnePlusSquareFareyIntegral_additive a b c)
      (by
        dsimp [Jac, Fac]
        exact RealRaw.equiv_symm
          (arctanIntegralFareyFor_sub_interval a c))
  simpa [Fab, Fbc, Fac] using
    RealRaw.equiv_trans hleftValid hkernelValid hFac
      hleftToKernel hkernelToRight

/-- On the rational unit branch, the shared-Farey integral over `[a,b]`
computes the endpoint difference of geometric arctangent. -/
theorem arctanGeom_sub_equiv_fareyIntegralBetweenRaw_on_unit
    (a b : Rat) (ha0 : 0 <= a) (ha1 : a <= 1)
    (hb0 : 0 <= b) (hb1 : b <= 1) :
    (ArctanGeometry.arctanGeom b -
      ArctanGeometry.arctanGeom a).Equiv
        (ArctanGeometry.fareyIntegralBetweenRaw a b) := by
  have hgB : (ArctanGeometry.arctanGeom b).Valid :=
    ArctanGeometry.arctanGeom_valid_on_unit hb0 hb1
  have hgA : (ArctanGeometry.arctanGeom a).Valid :=
    ArctanGeometry.arctanGeom_valid_on_unit ha0 ha1
  have hFB : (arctanIntegralFareyFor b).Valid :=
    arctanIntegralFareyFor_valid b
  have hFA : (arctanIntegralFareyFor a).Valid :=
    arctanIntegralFareyFor_valid a
  have hsubGeomValid :
      (ArctanGeometry.arctanGeom b -
        ArctanGeometry.arctanGeom a).Valid :=
    RealRaw.sub_valid hgB hgA
  have hsubFareyValid :
      (arctanIntegralFareyFor b - arctanIntegralFareyFor a).Valid :=
    RealRaw.sub_valid hFB hFA
  have htoFareySub :
      (ArctanGeometry.arctanGeom b -
        ArctanGeometry.arctanGeom a).Equiv
          (arctanIntegralFareyFor b - arctanIntegralFareyFor a) :=
    RealRaw.sub_equiv hgB hFB hgA hFA
      (RealRaw.equiv_symm
        (arctanIntegralFareyFor_equiv_arctanGeom b hb0 hb1))
      (RealRaw.equiv_symm
        (arctanIntegralFareyFor_equiv_arctanGeom a ha0 ha1))
  exact RealRaw.equiv_trans
    hsubGeomValid hsubFareyValid
    (ArctanGeometry.fareyIntegralBetweenRaw_valid a b)
    htoFareySub
    (arctanIntegralFareyFor_sub_interval_equiv_betweenRaw a b)

theorem fareyIntegralBetweenRaw_equiv_arctanGeom_sub_on_unit
    (a b : Rat) (ha0 : 0 <= a) (ha1 : a <= 1)
    (hb0 : 0 <= b) (hb1 : b <= 1) :
    (ArctanGeometry.fareyIntegralBetweenRaw a b).Equiv
      (ArctanGeometry.arctanGeom b -
        ArctanGeometry.arctanGeom a) :=
  RealRaw.equiv_symm
    (arctanGeom_sub_equiv_fareyIntegralBetweenRaw_on_unit
      a b ha0 ha1 hb0 hb1)

/-- Domain-aware wrapper version of the same endpoint-difference theorem:
the packaged Farey integral of `1/(1+x^2)` over `[a,b]` computes
`arctanGeom(b)-arctanGeom(a)` on the rational unit branch. -/
theorem arctanGeom_sub_equiv_oneOverOnePlusSquareFareyIntegral_on_unit
    (a b : Rat) (ha0 : 0 <= a) (ha1 : a <= 1)
    (hb0 : 0 <= b) (hb1 : b <= 1) :
    (ArctanGeometry.arctanGeom b -
      ArctanGeometry.arctanGeom a).Equiv
        (oneOverOnePlusSquareFareyIntegral a b) := by
  have hgeomSubValid :
      (ArctanGeometry.arctanGeom b -
        ArctanGeometry.arctanGeom a).Valid :=
    RealRaw.sub_valid
      (ArctanGeometry.arctanGeom_valid_on_unit hb0 hb1)
      (ArctanGeometry.arctanGeom_valid_on_unit ha0 ha1)
  exact RealRaw.equiv_trans
    hgeomSubValid
    (ArctanGeometry.fareyIntegralBetweenRaw_valid a b)
    (oneOverOnePlusSquareFareyIntegral_valid a b)
    (arctanGeom_sub_equiv_fareyIntegralBetweenRaw_on_unit
      a b ha0 ha1 hb0 hb1)
    (RealRaw.equiv_symm
      (oneOverOnePlusSquareFareyIntegral_equiv_betweenRaw a b))

theorem oneOverOnePlusSquareFareyIntegral_equiv_arctanGeom_sub_on_unit
    (a b : Rat) (ha0 : 0 <= a) (ha1 : a <= 1)
    (hb0 : 0 <= b) (hb1 : b <= 1) :
    (oneOverOnePlusSquareFareyIntegral a b).Equiv
      (ArctanGeometry.arctanGeom b -
        ArctanGeometry.arctanGeom a) :=
  RealRaw.equiv_symm
    (arctanGeom_sub_equiv_oneOverOnePlusSquareFareyIntegral_on_unit
      a b ha0 ha1 hb0 hb1)

/-- Additivity of geometric arctangent endpoint differences on the rational
unit branch.  The proof goes through the shared-Farey integral, so the
calculus identity is certified by finite rational interval sums. -/
theorem arctanGeom_sub_additive_on_unit
    (a b c : Rat)
    (ha0 : 0 <= a) (ha1 : a <= 1)
    (hb0 : 0 <= b) (hb1 : b <= 1)
    (hc0 : 0 <= c) (hc1 : c <= 1) :
    ((ArctanGeometry.arctanGeom b - ArctanGeometry.arctanGeom a) +
      (ArctanGeometry.arctanGeom c - ArctanGeometry.arctanGeom b)).Equiv
        (ArctanGeometry.arctanGeom c -
          ArctanGeometry.arctanGeom a) := by
  let Gab := ArctanGeometry.arctanGeom b - ArctanGeometry.arctanGeom a
  let Gbc := ArctanGeometry.arctanGeom c - ArctanGeometry.arctanGeom b
  let Gac := ArctanGeometry.arctanGeom c - ArctanGeometry.arctanGeom a
  let Jab := oneOverOnePlusSquareFareyIntegral a b
  let Jbc := oneOverOnePlusSquareFareyIntegral b c
  let Jac := oneOverOnePlusSquareFareyIntegral a c
  have hgA : (ArctanGeometry.arctanGeom a).Valid :=
    ArctanGeometry.arctanGeom_valid_on_unit ha0 ha1
  have hgB : (ArctanGeometry.arctanGeom b).Valid :=
    ArctanGeometry.arctanGeom_valid_on_unit hb0 hb1
  have hgC : (ArctanGeometry.arctanGeom c).Valid :=
    ArctanGeometry.arctanGeom_valid_on_unit hc0 hc1
  have hGab : Gab.Valid := by
    dsimp [Gab]
    exact RealRaw.sub_valid hgB hgA
  have hGbc : Gbc.Valid := by
    dsimp [Gbc]
    exact RealRaw.sub_valid hgC hgB
  have hGac : Gac.Valid := by
    dsimp [Gac]
    exact RealRaw.sub_valid hgC hgA
  have hJab : Jab.Valid := by
    dsimp [Jab]
    exact oneOverOnePlusSquareFareyIntegral_valid a b
  have hJbc : Jbc.Valid := by
    dsimp [Jbc]
    exact oneOverOnePlusSquareFareyIntegral_valid b c
  have hJac : Jac.Valid := by
    dsimp [Jac]
    exact oneOverOnePlusSquareFareyIntegral_valid a c
  have hleftValid : (Gab + Gbc).Valid :=
    RealRaw.add_valid hGab hGbc
  have hkernelValid : (Jab + Jbc).Valid :=
    RealRaw.add_valid hJab hJbc
  have hleftToKernel : (Gab + Gbc).Equiv (Jab + Jbc) :=
    RealRaw.add_equiv hGab hJab hGbc hJbc
      (by
        dsimp [Gab, Jab]
        exact arctanGeom_sub_equiv_oneOverOnePlusSquareFareyIntegral_on_unit
          a b ha0 ha1 hb0 hb1)
      (by
        dsimp [Gbc, Jbc]
        exact arctanGeom_sub_equiv_oneOverOnePlusSquareFareyIntegral_on_unit
          b c hb0 hb1 hc0 hc1)
  have hkernelToRight : (Jab + Jbc).Equiv Gac :=
    RealRaw.equiv_trans hkernelValid hJac hGac
      (by
        dsimp [Jab, Jbc, Jac]
        exact oneOverOnePlusSquareFareyIntegral_additive a b c)
      (by
        dsimp [Jac, Gac]
        exact RealRaw.equiv_symm
          (arctanGeom_sub_equiv_oneOverOnePlusSquareFareyIntegral_on_unit
            a c ha0 ha1 hc0 hc1))
  simpa [Gab, Gbc, Gac] using
    RealRaw.equiv_trans hleftValid hkernelValid hGac
      hleftToKernel hkernelToRight

/-- The geometric arctangent algorithm, restricted to the rational unit
interval as a `FunctionOnInterval`. -/
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

/-- Farey unit arctangent as a definite-integral identity: the verified
shared-Farey construction of `∫_0^1 dx/(1+x^2)` computes the endpoint
difference of the geometric arctangent primitive. -/
def arctanGeomUnitFareyDefiniteIdentity :
    Integral.DefiniteIdentityFor
      (oneOverOnePlusSquareOnInterval 0 1) arctanGeomOnUnit where
  same_lower := rfl
  same_upper := rfl
  construction := oneOverOnePlusSquareFareyConstruction 0 1
  endpoint_valid := arctanGeomOnUnit_endpointDifference_valid
  equivalent := by
    have hintegral :
        (oneOverOnePlusSquareFareyIntegral 0 1).Equiv
          (ArctanGeometry.arctanGeom (1 : Rat) -
            ArctanGeometry.arctanGeom (0 : Rat)) :=
      oneOverOnePlusSquareFareyIntegral_equiv_arctanGeom_sub_on_unit
        (0 : Rat) (1 : Rat)
        (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)
    have hleft :
        (oneOverOnePlusSquareFareyIntegral 0 1).Valid :=
      oneOverOnePlusSquareFareyIntegral_valid 0 1
    have hmid :
        (ArctanGeometry.arctanGeom (1 : Rat) -
          ArctanGeometry.arctanGeom (0 : Rat)).Valid :=
      RealRaw.sub_valid
        (ArctanGeometry.arctanGeom_valid_on_unit
          (x := (1 : Rat)) (by native_decide) (by native_decide))
        (ArctanGeometry.arctanGeom_valid_on_unit
          (x := (0 : Rat)) (by native_decide) (by native_decide))
    have hright :
        (endpointDifferenceRaw arctanGeomOnUnit.toRealFunRaw 0 1
          arctanGeomOnUnit_endpointDifference_valid).Valid := by
      simpa [endpointDifferenceRaw, RealRaw.Valid] using
        arctanGeomOnUnit_endpointDifference_valid
    simpa [oneOverOnePlusSquareFareyIntegral] using
      RealRaw.equiv_trans hleft hmid hright hintegral
        (RealRaw.equiv_symm arctanGeomOnUnit_endpointDifference_equiv_sub)

def arctanIntegralFareyUnitData : ArctanIntegralUnitData where
  constructionAt := fun x _hx0 _hx1 => arctanIntegralFareyConstruction x

theorem arctanIntegralFareyUnit_equiv_prefix
    (x : Rat) (hx0 : 0 <= x) (hx1 : x <= 1) :
    (arctanIntegralUnit x
      (arctanIntegralFareyUnitData.constructionAt x hx0 hx1)).Equiv
        (ArctanGeometry.fareyIntegralPrefixRaw x) := by
  simpa [arctanIntegralUnit, arctanIntegralFareyUnitData,
    arctanIntegralFareyFor] using
    arctanIntegralFareyFor_equiv_prefix x

theorem arctanIntegralFareyUnit_equiv_arctanGeom
    (x : Rat) (hx0 : 0 <= x) (hx1 : x <= 1) :
    (arctanIntegralUnit x
      (arctanIntegralFareyUnitData.constructionAt x hx0 hx1)).Equiv
        (ArctanGeometry.arctanGeom x) := by
  have hleft :
      (arctanIntegralUnit x
        (arctanIntegralFareyUnitData.constructionAt x hx0 hx1)).Valid := by
    simpa [arctanIntegralUnit, arctanIntegralFareyUnitData,
      arctanIntegralFareyFor] using
      arctanIntegralFareyFor_valid x
  exact RealRaw.equiv_trans
    hleft
    (ArctanGeometry.fareyIntegralPrefixRaw_valid x)
    (ArctanGeometry.arctanGeom_valid_on_unit hx0 hx1)
    (arctanIntegralFareyUnit_equiv_prefix x hx0 hx1)
    (ArctanGeometry.fareyIntegralPrefixRaw_equiv_arctanGeom_on_unit
      hx0 hx1)

theorem arctanIntegralFareyUnitComputes_prefix
    (x : Rat) (hx0 : 0 <= x) (hx1 : x <= 1) :
    ArctanIntegralUnitComputes x hx0 hx1
      (ArctanGeometry.fareyIntegralPrefixRaw x) :=
  ⟨arctanIntegralFareyUnitData.constructionAt x hx0 hx1,
    arctanIntegralFareyUnit_equiv_prefix x hx0 hx1⟩

theorem arctanIntegralFareyUnitComputes_arctanGeom
    (x : Rat) (hx0 : 0 <= x) (hx1 : x <= 1) :
    ArctanIntegralUnitComputes x hx0 hx1
      (ArctanGeometry.arctanGeom x) :=
  ⟨arctanIntegralFareyUnitData.constructionAt x hx0 hx1,
    arctanIntegralFareyUnit_equiv_arctanGeom x hx0 hx1⟩

theorem arctanIntegralFareyUnitFunctionAgreement :
    ArctanIntegralUnitGeomFunctionAgreement
      arctanIntegralFareyUnitData := by
  intro x hx _hgeom
  simpa [ArctanIntegralUnitGeomFunctionAgreement,
    arctanIntegralUnitRepresentation, arctanIntegralUnitFunctionRaw,
    arctanIntegralUnit, arctanIntegralFareyUnitData,
    arctanIntegralFareyFor, ArctanGeometry.representation,
    ArctanGeometry.functionRaw, PartialRealFunRaw.evalRaw] using
    arctanIntegralFareyUnit_equiv_arctanGeom x hx.1 hx.2

theorem arctanIntegralFareyUnitComputes_one :
    ArctanIntegralUnitComputes (1 : Rat)
      (by native_decide) (by native_decide)
      (ArctanGeometry.fareyIntegralPrefixRaw (1 : Rat)) :=
  arctanIntegralFareyUnitComputes_prefix
    (1 : Rat) (by native_decide) (by native_decide)

theorem arctanIntegralFareyUnitComputes_arctanGeom_one :
    ArctanIntegralUnitComputes (1 : Rat)
      (by native_decide) (by native_decide)
      (ArctanGeometry.arctanGeom (1 : Rat)) :=
  arctanIntegralFareyUnitComputes_arctanGeom
    (1 : Rat) (by native_decide) (by native_decide)

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
the projective/Farey construction still has to be supplied separately. -/
def reciprocalQuarticMinusOneExpectedPi : RealRaw :=
  reciprocalQuarticExpectedPiMultiple 1

/-- The theorem-facing obligation for a future projective-line/Farey
construction of the clean reciprocal quartic integral: its produced raw real
must agree with the expected pi value. -/
def ReciprocalQuarticMinusOneProjectiveAgreement
    (projectiveIntegral : RealRaw) : Prop :=
  projectiveIntegral.Equiv reciprocalQuarticMinusOneExpectedPi

/-- Data for the clean reciprocal quartic pi route.  The finite algebraic
pullback is already formalized above; this structure isolates the remaining
analytic/improper-integral construction as a verified raw real equivalent to the
expected value. -/
structure ReciprocalQuarticMinusOneProjectiveRoute where
  projectiveIntegral : RealRaw
  projectiveIntegral_valid : projectiveIntegral.Valid
  computes_expected :
    ReciprocalQuarticMinusOneProjectiveAgreement projectiveIntegral

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
will supply the Farey/improper-integral bookkeeping. -/
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
kernel used by the existing Farey and rectangle constructions. -/
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
