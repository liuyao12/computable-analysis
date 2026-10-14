import ComputableAnalysis.RiemannHilbert.ContourTaylorRemainder
import ComputableAnalysis.RiemannHilbert.ContourScaledEffectiveLimit

/-! Constructed Cauchy moments from actual boundary data alone. The source
may have a hole or poles inside the rectangle, and the represented center may
be outside its domain. Full edge domains and actual value, derivative and
reciprocal bounds construct every moment by a rational quadrature limit. -/
namespace ComputableAnalysis.RiemannHilbert.BoundaryCauchyPowers
open ComplexRaw FunctionTheory DomainFunctions RectangularContour
set_option autoImplicit false

structure Data where
  source : DomainFunctions.Map
  holomorphic : Holomorphic source
  rectangle : QInterval × QInterval
  xOrder : rectangle.1.lo≤rectangle.1.hi
  yOrder : rectangle.2.lo≤rectangle.2.hi
  center : Scalar
  sourceDomains : RectangleBoundaryDomains source rectangle
  reciprocalDomains : RectangleBoundaryDomains (ribbonPoleReciprocal center) rectangle
  valueBound : QPos
  derivativeBound : QPos
  reciprocalBound : QPos
  values : RectangleBoundaryValueBound source rectangle sourceDomains valueBound
  derivatives : RectangleBoundaryDerivativeBound source holomorphic rectangle sourceDomains derivativeBound
  reciprocals : RectangleBoundaryValueBound (ribbonPoleReciprocal center) rectangle reciprocalDomains reciprocalBound

variable (d : Data)

theorem powerDomains (k : Nat) : RectangleBoundaryDomains (ribbonCauchyPowerKernel d.source d.center k) d.rectangle :=
  ⟨fun z hz => ⟨d.sourceDomains.bottom z hz,d.reciprocalDomains.bottom z hz⟩,
    fun z hz => ⟨d.sourceDomains.top z hz,d.reciprocalDomains.top z hz⟩,
    fun z hz => ⟨d.sourceDomains.left z hz,d.reciprocalDomains.left z hz⟩,
    fun z hz => ⟨d.sourceDomains.right z hz,d.reciprocalDomains.right z hz⟩⟩

theorem power_values (k : Nat) : RectangleBoundaryValueBound (ribbonCauchyPowerKernel d.source d.center k)
    d.rectangle (powerDomains d k) (powerKernelValueBound d.valueBound d.reciprocalBound k) :=
  ⟨fun z hz => ribbonCauchyPowerKernel_value_bound d.source d.center z _ _ _ (d.values.bottom z hz) (d.reciprocals.bottom z hz) k,
    fun z hz => ribbonCauchyPowerKernel_value_bound d.source d.center z _ _ _ (d.values.top z hz) (d.reciprocals.top z hz) k,
    fun z hz => ribbonCauchyPowerKernel_value_bound d.source d.center z _ _ _ (d.values.left z hz) (d.reciprocals.left z hz) k,
    fun z hz => ribbonCauchyPowerKernel_value_bound d.source d.center z _ _ _ (d.values.right z hz) (d.reciprocals.right z hz) k⟩

theorem power_derivatives (k : Nat) : RectangleBoundaryDerivativeBound (ribbonCauchyPowerKernel d.source d.center k)
    (ribbonCauchyPowerKernel_holomorphic d.source d.holomorphic d.center k) d.rectangle (powerDomains d k)
    (powerKernelDerivativeBound d.valueBound d.derivativeBound d.reciprocalBound k) :=
  ⟨fun z hz => ribbonCauchyPowerKernel_derivative_bound d.source d.holomorphic d.center z _ _ _ _
      (d.values.bottom z hz) (d.derivatives.bottom z hz) (d.reciprocals.bottom z hz) k,
    fun z hz => ribbonCauchyPowerKernel_derivative_bound d.source d.holomorphic d.center z _ _ _ _
      (d.values.top z hz) (d.derivatives.top z hz) (d.reciprocals.top z hz) k,
    fun z hz => ribbonCauchyPowerKernel_derivative_bound d.source d.holomorphic d.center z _ _ _ _
      (d.values.left z hz) (d.derivatives.left z hz) (d.reciprocals.left z hz) k,
    fun z hz => ribbonCauchyPowerKernel_derivative_bound d.source d.holomorphic d.center z _ _ _ _
      (d.values.right z hz) (d.derivatives.right z hz) (d.reciprocals.right z hz) k⟩

def quadrature (k n : Nat) : Scalar :=
  continuousRectangleBoundary (ribbonCauchyPowerKernel d.source d.center k) d.rectangle (powerDomains d k) n

def value (k : Nat) : Scalar := scaledEffectiveBoundaryValue (ribbonCauchyPowerKernel d.source d.center k)
  (ribbonCauchyPowerKernel_holomorphic d.source d.holomorphic d.center k) d.rectangle d.xOrder d.yOrder
  (powerDomains d k) (powerKernelDerivativeBound d.valueBound d.derivativeBound d.reciprocalBound k) (power_derivatives d k)

theorem prefix_error (k n : Nat) : Small (sub (quadrature d k n).val (value d k).val)
    (effectiveBoundaryTail d.rectangle (powerKernelDerivativeBound d.valueBound d.derivativeBound d.reciprocalBound k) n) :=
  scaledEffectiveBoundaryValue_prefix_error _ _ _ _ _ _ _ (power_derivatives d k) n

theorem converges (k : Nat) : Converges (quadrature d k) (value d k) :=
  scaledEffectiveBoundaryValue_converges _ _ _ _ _ _ _ (power_derivatives d k)

theorem value_bound (k : Nat) : Small (value d k).val
    (4*(d.rectangle.1.width+d.rectangle.2.width)*d.valueBound.val*(2*d.reciprocalBound.val)^k) := by
  apply converge_bounded _ _ (converges d k)
  intro n
  have hb := continuousRectangleBoundary_value_bound _ d.rectangle d.xOrder d.yOrder (powerDomains d k)
    (powerKernelValueBound d.valueBound d.reciprocalBound k) (power_values d k) n
  rw [powerKernelValueBound_formula] at hb
  simpa only [quadrature,Rat.mul_assoc] using hb

def moment (k : Nat) : Scalar := scalarProduct inverseGeometricPeriod (value d (k+1))
def momentPrefix (k n : Nat) : Scalar := scalarProduct inverseGeometricPeriod (quadrature d (k+1) n)

theorem moment_converges (k : Nat) : Converges (momentPrefix d k) (moment d k) :=
  converge_product_left inverseGeometricPeriod _ _ (converges d (k+1))

def rate : QPos := ⟨2*d.reciprocalBound.val,Rat.mul_pos (by decide +kernel) d.reciprocalBound.property⟩

def bound : QPos :=
  ⟨1+16*scalarBound inverseGeometricPeriod*(d.rectangle.1.width+d.rectangle.2.width)*d.valueBound.val*d.reciprocalBound.val,by
    have hx : 0≤d.rectangle.1.width := by unfold QInterval.width; have h := d.xOrder; grind only
    have hy : 0≤d.rectangle.2.width := by unfold QInterval.width; have h := d.yOrder; grind only
    have hp : 0≤16*scalarBound inverseGeometricPeriod*(d.rectangle.1.width+d.rectangle.2.width)*d.valueBound.val*d.reciprocalBound.val := Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg
      (Rat.le_of_lt (Rat.mul_pos (show (0:Rat)<16 by decide +kernel) (scalarBound_pos inverseGeometricPeriod)))
      (Rat.add_nonneg hx hy)) (Rat.le_of_lt d.valueBound.property)) (Rat.le_of_lt d.reciprocalBound.property)
    grind only⟩

theorem moment_bound (k : Nat) : Small (moment d k).val ((bound d).val*((rate d).val)^k) := by
  have hx : 0≤d.rectangle.1.width := by unfold QInterval.width; have h := d.xOrder; grind only
  have hy : 0≤d.rectangle.2.width := by unfold QInterval.width; have h := d.yOrder; grind only
  have hs := Small.mul inverseGeometricPeriod.property (value d (k+1)).property
    (Rat.le_of_lt (scalarBound_pos inverseGeometricPeriod))
    (Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) (Rat.add_nonneg hx hy))
      (Rat.le_of_lt d.valueBound.property)) (Rat.pow_nonneg (Rat.le_of_lt (rate d).property)))
    (scalar_small inverseGeometricPeriod) (value_bound d (k+1))
  have hp := Rat.pow_nonneg (Rat.le_of_lt (rate d).property) (n := k)
  change 0≤(2*d.reciprocalBound.val)^k at hp
  apply hs.mono
  dsimp [bound,rate]
  rw [Rat.pow_succ]
  grind only

end ComputableAnalysis.RiemannHilbert.BoundaryCauchyPowers
