import ComputableAnalysis.RiemannHilbert.ContourPowerContours
import ComputableAnalysis.RiemannHilbert.ContourScaledEffectiveLimit

/-! Constructed local Cauchy moment values of every order for a supplied
holomorphic map and any represented point in its domain. All quantitative
data are computed locally. The first two values are proved to recover the
function and its supplied derivative; higher Taylor reconstruction is separate. -/
namespace ComputableAnalysis.RiemannHilbert.RectangularContour
open ComplexRaw FunctionTheory DomainFunctions
set_option autoImplicit false

def effectiveLocalPowerBound (f : DomainFunctions.Map) (hf : Holomorphic f) (b : Scalar) (hb : f.domain b) (m : Nat) : QPos :=
  powerKernelDerivativeBound (localHolomorphicValueBound f b hb) (localHolomorphicDerivativeBound f hf b hb)
    (centeredBoundaryReciprocalBound (effectiveLocalRadius f hf b hb)) m

theorem effectiveLocalPower_boundary_bound (f : DomainFunctions.Map) (hf : Holomorphic f) (b : Scalar) (hb : f.domain b)
    (m : Nat) :
    RectangleBoundaryDerivativeBound (ribbonCauchyPowerKernel f b m) (ribbonCauchyPowerKernel_holomorphic f hf b m)
      (effectiveLocalRectangle f hf b hb)
      (ribbonCauchyPowerBoundaryDomains f _ (effectiveLocalRectangle_domain f hf b hb) b
        (effectiveLocalRectangle_pole_inside f hf b hb) m) (effectiveLocalPowerBound f hf b hb m) := by
  let J := effectiveLocalRectangle f hf b hb
  let hp := effectiveLocalRectangle_pole_inside f hf b hb
  have hord := rectanglePoleInterior_ordered J b hp
  let hdF := rectangleBoundaryDomains_of_rectangle f J hord.1 hord.2 (effectiveLocalRectangle_domain f hf b hb)
  let hdR := rectanglePoleReciprocalBoundaryDomains J b hp
  exact ribbonCauchyPowerBoundary_derivative_bound f hf J (effectiveLocalRectangle_domain f hf b hb) b hp hdF hdR
    (localHolomorphicValueBound f b hb) (localHolomorphicDerivativeBound f hf b hb)
    (centeredBoundaryReciprocalBound (effectiveLocalRadius f hf b hb))
    (effectiveLocalRectangle_value_bound f hf b hb hdF) (effectiveLocalRectangle_derivative_bound f hf b hb hdF)
    (effectiveLocalRectangle_reciprocal_bound f hf b hb hdR) m

def effectiveLocalPowerValue (f : DomainFunctions.Map) (hf : Holomorphic f) (b : Scalar) (hb : f.domain b) (m : Nat) : Scalar :=
  let J := effectiveLocalRectangle f hf b hb
  let hp := effectiveLocalRectangle_pole_inside f hf b hb
  let hord := rectanglePoleInterior_ordered J b hp
  scaledEffectiveBoundaryValue (ribbonCauchyPowerKernel f b m) (ribbonCauchyPowerKernel_holomorphic f hf b m) J
    hord.1 hord.2 (ribbonCauchyPowerBoundaryDomains f J (effectiveLocalRectangle_domain f hf b hb) b hp m)
    (effectiveLocalPowerBound f hf b hb m) (effectiveLocalPower_boundary_bound f hf b hb m)

theorem effectiveLocalPowerValue_prefix_error (f : DomainFunctions.Map) (hf : Holomorphic f) (b : Scalar)
    (hb : f.domain b) (m n : Nat) :
    Small (sub (fixedRectanglePowerContour f (effectiveLocalRectangle f hf b hb)
      (effectiveLocalRectangle_domain f hf b hb) b (effectiveLocalRectangle_pole_inside f hf b hb) m n).val
      (effectiveLocalPowerValue f hf b hb m).val)
      (effectiveBoundaryTail (effectiveLocalRectangle f hf b hb) (effectiveLocalPowerBound f hf b hb m) n) :=
  let hord := rectanglePoleInterior_ordered _ b (effectiveLocalRectangle_pole_inside f hf b hb)
  scaledEffectiveBoundaryValue_prefix_error _ (ribbonCauchyPowerKernel_holomorphic f hf b m) _ hord.1 hord.2 _ _
    (effectiveLocalPower_boundary_bound f hf b hb m) n

theorem effectiveLocalPowerValue_converges (f : DomainFunctions.Map) (hf : Holomorphic f) (b : Scalar)
    (hb : f.domain b) (m : Nat) :
    Converges (fixedRectanglePowerContour f (effectiveLocalRectangle f hf b hb) (effectiveLocalRectangle_domain f hf b hb)
      b (effectiveLocalRectangle_pole_inside f hf b hb) m) (effectiveLocalPowerValue f hf b hb m) :=
  let hord := rectanglePoleInterior_ordered _ b (effectiveLocalRectangle_pole_inside f hf b hb)
  scaledEffectiveBoundaryValue_converges _ (ribbonCauchyPowerKernel_holomorphic f hf b m) _ hord.1 hord.2 _ _
    (effectiveLocalPower_boundary_bound f hf b hb m)

def localCauchyMoment (f : DomainFunctions.Map) (hf : Holomorphic f) (b : Scalar) (hb : f.domain b) (k : Nat) : Scalar :=
  scalarProduct inverseGeometricPeriod (effectiveLocalPowerValue f hf b hb (k+1))

def localCauchyMomentContour (f : DomainFunctions.Map) (hf : Holomorphic f) (b : Scalar) (hb : f.domain b)
    (k n : Nat) : Scalar :=
  scalarProduct inverseGeometricPeriod (fixedRectanglePowerContour f (effectiveLocalRectangle f hf b hb)
    (effectiveLocalRectangle_domain f hf b hb) b (effectiveLocalRectangle_pole_inside f hf b hb) (k+1) n)

theorem localCauchyMoment_converges (f : DomainFunctions.Map) (hf : Holomorphic f) (b : Scalar) (hb : f.domain b) (k : Nat) :
    Converges (localCauchyMomentContour f hf b hb k) (localCauchyMoment f hf b hb k) :=
  converge_product_left inverseGeometricPeriod _ _ (effectiveLocalPowerValue_converges f hf b hb (k+1))

theorem localCauchyMoment_zero (f : DomainFunctions.Map) (hf : Holomorphic f) (b : Scalar) (hb : f.domain b) :
    localCauchyMoment f hf b hb 0≈f.eval b hb := by
  let J := effectiveLocalRectangle f hf b hb
  let hd := effectiveLocalRectangle_domain f hf b hb
  let hp := effectiveLocalRectangle_pole_inside f hf b hb
  apply converge_unique (localCauchyMomentContour f hf b hb 0) _ _ (localCauchyMoment_converges f hf b hb 0)
  exact converge_congr (normalizedFixedRectangleCauchyContour f J hd b hp) _ _
    (normalizedFixedRectangleCauchyContour_converges f hf J hd b hp)
    (fun n => mul_equiv inverseGeometricPeriod.property inverseGeometricPeriod.property
      (fixedRectangleCauchyContour f J hd b hp n).property (fixedRectanglePowerContour f J hd b hp 1 n).property
      (equiv_refl _ inverseGeometricPeriod.property) (equiv_symm (fixedRectanglePowerContour_one f J hd b hp n)))

theorem localCauchyMoment_one (f : DomainFunctions.Map) (hf : Holomorphic f) (b : Scalar) (hb : f.domain b) :
    localCauchyMoment f hf b hb 1≈hf.derivative b hb := by
  let J := effectiveLocalRectangle f hf b hb
  let hd := effectiveLocalRectangle_domain f hf b hb
  let hp := effectiveLocalRectangle_pole_inside f hf b hb
  apply converge_unique (localCauchyMomentContour f hf b hb 1) _ _ (localCauchyMoment_converges f hf b hb 1)
  exact converge_congr (normalizedFixedRectangleDerivativeContour f J hd b hp) _ _
    (normalizedFixedRectangleDerivativeContour_converges f hf J hd b hp)
    (fun n => mul_equiv inverseGeometricPeriod.property inverseGeometricPeriod.property
      (fixedRectangleDerivativeContour f J hd b hp n).property (fixedRectanglePowerContour f J hd b hp 2 n).property
      (equiv_refl _ inverseGeometricPeriod.property) (equiv_symm (fixedRectanglePowerContour_two f J hd b hp n)))

theorem localCauchyMoment_zero_congr (f : DomainFunctions.Map) (hf hg : Holomorphic f) (b c : Scalar)
    (hb : f.domain b) (hc : f.domain c) (he : b≈c) : localCauchyMoment f hf b hb 0≈localCauchyMoment f hg c hc 0 :=
  Setoid.trans (localCauchyMoment_zero f hf b hb)
    (Setoid.trans (f.eval_congr b c hb hc he) (equiv_symm (localCauchyMoment_zero f hg c hc)))

theorem localCauchyMoment_one_congr (f : DomainFunctions.Map) (hf : Holomorphic f) (b c : Scalar)
    (hb : f.domain b) (hc : f.domain c) (he : b≈c) : localCauchyMoment f hf b hb 1≈localCauchyMoment f hf c hc 1 :=
  Setoid.trans (localCauchyMoment_one f hf b hb)
    (Setoid.trans (hf.derivative_congr b c hb hc he) (equiv_symm (localCauchyMoment_one f hf c hc)))

end ComputableAnalysis.RiemannHilbert.RectangularContour
