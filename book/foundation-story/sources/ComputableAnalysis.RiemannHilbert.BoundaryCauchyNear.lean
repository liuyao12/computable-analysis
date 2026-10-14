import ComputableAnalysis.RiemannHilbert.BoundaryCauchyPowers

/-! A boundary reciprocal bound computes a full pole-parameter neighborhood.
Inverse stability derives all new edge domains and bounds. The source is never
evaluated at the pole parameter or required to extend through the contour. -/
namespace ComputableAnalysis.RiemannHilbert.BoundaryCauchyNear
open ComplexRaw FunctionTheory DomainFunctions RectangularContour BoundaryCauchyPowers
set_option autoImplicit false
variable (d : Data)

def radius : QPos := divideRadius unitError
  ⟨16*(rate d).val,Rat.mul_pos (by decide +kernel) (rate d).property⟩

theorem radius_rate : (rate d).val*(radius d).val=(1:Rat)/16 := by
  have h := divideRadius_identity unitError
    (⟨16*(rate d).val,Rat.mul_pos (by decide +kernel) (rate d).property⟩ : QPos)
  change (16*(rate d).val)*(radius d).val=1 at h
  grind only

theorem radius_budget : 16*d.reciprocalBound.val*(radius d).val≤1 := by
  have h := radius_rate d
  change (2*d.reciprocalBound.val)*(radius d).val=(1:Rat)/16 at h
  calc
    16*d.reciprocalBound.val*(radius d).val=8*((2*d.reciprocalBound.val)*(radius d).val) := by grind only
    _=8*((1:Rat)/16) := by rw [h]
    _≤1 := by decide +kernel

theorem near_domain (z w : Scalar) (hz : Centered.domain d.center (radius d).val z)
    (hw : (ribbonPoleReciprocal d.center).domain w)
    (hu : Small ((ribbonPoleReciprocal d.center).eval w hw).val d.reciprocalBound.val) :
    (ribbonPoleReciprocal z).domain w := by
  have hh := LocalODE.interior_bound _ _ hz
  have hdiff : Small (sub ((ribbonPoleOffset z).eval w trivial).val
      ((ribbonPoleOffset d.center).eval w trivial).val) (radius d).val :=
    Small.congr (scalarNeg (Centered.offset d.center z)).property
      (sub_valid ((ribbonPoleOffset z).eval w trivial).property ((ribbonPoleOffset d.center).eval w trivial).property)
      (equiv_symm (ribbonPoleOffset_pole_difference d.center z w)) (SeriesLimitLaws.small_neg hh)
  obtain ⟨hn,_⟩ := inverse_near_exists_bound ((ribbonPoleOffset d.center).eval w trivial)
    ((ribbonPoleOffset z).eval w trivial) (compose_outer_mem hw) d.reciprocalBound.val (radius d).val
    (Rat.le_of_lt d.reciprocalBound.property) (Rat.le_of_lt (radius d).property) hu hdiff (radius_budget d)
  exact ⟨trivial,hn⟩

theorem near_bound (z w : Scalar) (hz : Centered.domain d.center (radius d).val z)
    (hw : (ribbonPoleReciprocal d.center).domain w)
    (hu : Small ((ribbonPoleReciprocal d.center).eval w hw).val d.reciprocalBound.val) :
    Small ((ribbonPoleReciprocal z).eval w (near_domain d z w hz hw hu)).val (8*d.reciprocalBound.val) :=
  ribbonPoleReciprocal_near_bound d.center z w hw (near_domain d z w hz hw hu)
    d.reciprocalBound.val (radius d).val (Rat.le_of_lt d.reciprocalBound.property)
    (Rat.le_of_lt (radius d).property) hu (LocalODE.interior_bound _ _ hz) (radius_budget d)

theorem nearDomains (z : Scalar) (hz : Centered.domain d.center (radius d).val z) :
    RectangleBoundaryDomains (ribbonPoleReciprocal z) d.rectangle :=
  ⟨fun w hw => near_domain d z w hz (d.reciprocalDomains.bottom w hw) (d.reciprocals.bottom w hw),
    fun w hw => near_domain d z w hz (d.reciprocalDomains.top w hw) (d.reciprocals.top w hw),
    fun w hw => near_domain d z w hz (d.reciprocalDomains.left w hw) (d.reciprocals.left w hw),
    fun w hw => near_domain d z w hz (d.reciprocalDomains.right w hw) (d.reciprocals.right w hw)⟩

def nearReciprocalBound : QPos := ⟨8*d.reciprocalBound.val,Rat.mul_pos (by decide +kernel) d.reciprocalBound.property⟩

theorem nearValues (z : Scalar) (hz : Centered.domain d.center (radius d).val z) :
    RectangleBoundaryValueBound (ribbonPoleReciprocal z) d.rectangle (nearDomains d z hz) (nearReciprocalBound d) :=
  ⟨fun w hw => near_bound d z w hz (d.reciprocalDomains.bottom w hw) (d.reciprocals.bottom w hw),
    fun w hw => near_bound d z w hz (d.reciprocalDomains.top w hw) (d.reciprocals.top w hw),
    fun w hw => near_bound d z w hz (d.reciprocalDomains.left w hw) (d.reciprocals.left w hw),
    fun w hw => near_bound d z w hz (d.reciprocalDomains.right w hw) (d.reciprocals.right w hw)⟩

def data (z : Scalar) (hz : Centered.domain d.center (radius d).val z) : Data where
  source := d.source
  holomorphic := d.holomorphic
  rectangle := d.rectangle
  xOrder := d.xOrder
  yOrder := d.yOrder
  center := z
  sourceDomains := d.sourceDomains
  reciprocalDomains := nearDomains d z hz
  valueBound := d.valueBound
  derivativeBound := d.derivativeBound
  reciprocalBound := nearReciprocalBound d
  values := d.values
  derivatives := d.derivatives
  reciprocals := nearValues d z hz

end ComputableAnalysis.RiemannHilbert.BoundaryCauchyNear
