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
interface.  This is the version used by hand-built interval constructions such
as the Farey arctangent integral, where the raw computation is already a valid
integral on the whole `FunctionOnInterval` but is not necessarily presented as
the generic left-Riemann `Integral.Construction` plan. -/
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

end DefiniteIdentityFor

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
