import ComputableAnalysis.IntegralIdentities

/-!
# The half-interval integral of `sin (pi * x)`

This file is the proof-facing entry point for the first nontrivial
trigonometric integral.  The circle layer uses normalized quarter-turns: its
input `t` denotes the angle `t * pi / 2`.  Consequently the requested
function `sin (pi * x)` is obtained at a rational input by evaluating the
circle sine at `2 * x`; no real-valued argument and no primitive real `pi` are
used by the evaluator.

The final equality is intentionally expressed through an effective FTC
certificate.  The certificate is where the finite interval bounds,
monotonicity/turning-point analysis, and endpoint calculation belong.  This
keeps the theorem constructive: the dyadic integral algorithm is a raw
algorithm, while the FTC certificate identifies its value.
-/

namespace ComputableAnalysis

namespace RationalCircle

namespace GeometricTrig

/-- The normalized circle sine reparameterized as `sin (pi * x)`.

The input is rational and is only interpreted through the quarter-turn
parameter `2*x`.  In particular, this definition does not ask for a real
number named `pi` at a rational input.
-/
def sinPiRawOfConstruction
    (C : FunctionRawConstruction)
    (hdefined : forall x, 0 <= x -> x <= (1 : Rat) / 2 ->
      C.sinFunctionRaw.definedAt (2 * x)) :
    PartialRealFunRaw where
  definedAt := fun x => 0 <= x /\ x <= (1 : Rat) / 2
  compute := fun x hx n =>
    C.sinFunctionRaw.compute (2 * x) (hdefined x hx.1 hx.2) n

theorem sinPiRawOfConstruction_valid
    (C : FunctionRawConstruction)
    (hdefined : forall x, 0 <= x -> x <= (1 : Rat) / 2 ->
      C.sinFunctionRaw.definedAt (2 * x)) :
    forall x hx,
      RealRaw.ValidCompute
        ((sinPiRawOfConstruction C hdefined).compute x hx) := by
  intro x hx
  exact C.sinFunctionRaw_valid (2 * x) (hdefined x hx.1 hx.2)

end GeometricTrig

end RationalCircle

namespace SinPiIntegral

open RationalCircle.GeometricTrig

/-- `sin (pi*x)` as a function on the rational interval `[0,1/2]`. -/
def sinPiOnHalf
    (C : FunctionRawConstruction)
    (hdefined : forall x, 0 <= x -> x <= (1 : Rat) / 2 ->
      C.sinFunctionRaw.definedAt (2 * x)) :
    FunctionOnInterval where
  raw := sinPiRawOfConstruction C hdefined
  lower := 0
  upper := (1 : Rat) / 2
  defined_on := by
    intro x hx
    exact hx
  valid_on := by
    intro x hx
    exact sinPiRawOfConstruction_valid C hdefined x hx

/-- The equal-dyadic-subdivision integral of `sin (pi*x)` on `[0,1/2]`.

The caller supplies the usual interval-sum certificate.  This is the
computable value before any identification with a closed expression.
-/
def halfIntegral
    (C : FunctionRawConstruction)
    (hdefined : forall x, 0 <= x -> x <= (1 : Rat) / 2 ->
      C.sinFunctionRaw.definedAt (2 * x))
    (c : Integral.Construction
      (sinPiOnHalf C hdefined).toRealFunRaw 0 ((1 : Rat) / 2)) : RealRaw :=
  Integral.integral
    (sinPiOnHalf C hdefined).toRealFunRaw 0 ((1 : Rat) / 2) c

theorem halfIntegral_valid
    (C : FunctionRawConstruction)
    (hdefined : forall x, 0 <= x -> x <= (1 : Rat) / 2 ->
      C.sinFunctionRaw.definedAt (2 * x))
    (c : Integral.Construction
      (sinPiOnHalf C hdefined).toRealFunRaw 0 ((1 : Rat) / 2)) :
    (halfIntegral C hdefined c).Valid := by
  exact FTC.integral_valid_of_construction c

/--
The exact reusable conclusion of the elementary sine-integral argument.

`F` is the computable primitive (normally the represented function
`-cos(pi*x)/pi`) and `hftc` is an effective, static-dyadic FTC certificate
for its derivative, which is the `sinPiOnHalf` evaluator.  The theorem does
not invoke Mathlib's real numbers: equality is `RealRaw.Equiv`, and the
certificate is made from finite rational interval computations.

The endpoint raw is deliberately returned by the theorem.  Once the
project's reciprocal-`pi` representation is connected to the endpoint, the
same theorem immediately yields the familiar notation
`integral = 1/pi`; the scaled form `pi * integral = 1` is obtained from the
corresponding endpoint identity without changing the integral algorithm.
-/
structure HalfIntegralFTCCertificate
    (C : FunctionRawConstruction)
    (hdefined : forall x, 0 <= x -> x <= (1 : Rat) / 2 ->
      C.sinFunctionRaw.definedAt (2 * x)) where
  primitive : RealFunRaw
  primitive_valid : primitive.Valid
  endpoint_valid :
    RealRaw.ValidCompute
      (endpointDifferenceCompute primitive 0 ((1 : Rat) / 2))
  integral : Integral.Construction
    (sinPiOnHalf C hdefined).toRealFunRaw 0 ((1 : Rat) / 2)
  /-- The integral is computed by the project's fixed equal-dyadic plan. -/
  integral_plan : integral.plan = Integral.staticDyadicPlan
  ftc : DefiniteIntegralEqualsEndpointDifference
    primitive (sinPiOnHalf C hdefined).toRealFunRaw 0 ((1 : Rat) / 2)
    integral endpoint_valid

theorem halfIntegral_equiv_endpoint
    {C : FunctionRawConstruction}
    {hdefined : forall x, 0 <= x -> x <= (1 : Rat) / 2 ->
      C.sinFunctionRaw.definedAt (2 * x)}
    (h : HalfIntegralFTCCertificate C hdefined) :
    (halfIntegral C hdefined h.integral).Equiv
      (endpointDifferenceRaw h.primitive 0 ((1 : Rat) / 2) h.endpoint_valid) :=
  h.ftc

end SinPiIntegral

end ComputableAnalysis
