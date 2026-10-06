import ComputableAnalysis.RiemannHilbert.CenteredSystemChart

/-! Normalized holomorphic solutions and actual transport on translated
coefficient charts, with effective neighborhoods at every interior point. -/
namespace ComputableAnalysis.RiemannHilbert.SystemChart
open ComplexRaw FunctionTheory LocalODE LocalSystem
variable {n : Nat}

def seed (c : SystemChart n) (p : Scalar) (hp : c.domain p) (v : Fiber n) : Fiber n :=
  (c.valueIso p hp).toValueIso.backward.eval v

def through (c : SystemChart n) (p : Scalar) (hp : c.domain p) (v : Fiber n)
    (z : Scalar) (hz : c.domain z) : Fiber n := c.value (c.seed p hp v) z hz

theorem through_normalized (c : SystemChart n) (p : Scalar) (hp : c.domain p) (v : Fiber n) :
    c.through p hp v p hp ≈ v :=
  (c.valueIso p hp).toValueIso.forward_backward v

def through_holomorphic (c : SystemChart n) (p : Scalar) (hp : c.domain p) (v : Fiber n) (i : Fin n) :
    CertifiedFunctions.Holomorphic (c.coordinate (c.seed p hp v) i) :=
  c.coordinate_holomorphic (c.seed p hp v) i

theorem through_bound (c : SystemChart n) (p : Scalar) (hp : c.domain p) (v : Fiber n)
    (z : Scalar) (hz : c.domain z) :
    CoordinateBound (c.through p hp v z hz) (4*initialBound (c.seed p hp v)) :=
  c.value_bound (c.seed p hp v) z hz

theorem through_congr (c : SystemChart n) (p : Scalar) (hp : c.domain p) (v u : Fiber n)
    (hvu : v ≈ u) (z w : Scalar) (hzw : z.val.Equiv w.val) (hz : c.domain z) (hw : c.domain w) :
    c.through p hp v z hz ≈ c.through p hp u w hw :=
  c.value_congr c (c.seed p hp v) (c.seed p hp u) (equiv_refl _ c.center.property)
    (fun _ => ValueMap.equiv_refl _) ((c.valueIso p hp).toValueIso.backward.congr hvu) z w hzw hz hw

def transport (c : SystemChart n) (p q : Scalar) (hp : c.domain p) (hq : c.domain q) : LinearIso n n :=
  LocalSystem.transport c.coefficients c.linear c.M c.K c.nonnegM c.nonnegK c.compatible c.majorant
    (Centered.offset c.center p) (Centered.offset c.center q) hp hq

theorem transport_value (c : SystemChart n) (p q : Scalar) (hp : c.domain p) (hq : c.domain q) (v : Fiber n) :
    (c.transport p q hp hq).toValueIso.forward.eval v = c.through p hp v q hq := rfl

theorem transport_self (c : SystemChart n) (p : Scalar) (hp : c.domain p) :
    (c.transport p p hp hp).toValueIso.forward.Equiv ValueMap.identity :=
  LocalSystem.transport_self c.coefficients c.linear c.M c.K c.nonnegM c.nonnegK c.compatible c.majorant
    (Centered.offset c.center p) hp

theorem transport_compose (c : SystemChart n) (p q r : Scalar)
    (hp : c.domain p) (hq : c.domain q) (hr : c.domain r) :
    ((c.transport p q hp hq).toValueIso.forward.followedBy (c.transport q r hq hr).toValueIso.forward).Equiv
      (c.transport p r hp hr).toValueIso.forward :=
  LocalSystem.transport_compose c.coefficients c.linear c.M c.K c.nonnegM c.nonnegK c.compatible c.majorant
    (Centered.offset c.center p) (Centered.offset c.center q) (Centered.offset c.center r) hp hq hr

theorem transport_reverse (c : SystemChart n) (p q : Scalar) (hp : c.domain p) (hq : c.domain q) :
    (c.transport q p hq hp).toValueIso.forward.Equiv (c.transport p q hp hq).toValueIso.backward :=
  LocalSystem.transport_reverse c.coefficients c.linear c.M c.K c.nonnegM c.nonnegK c.compatible c.majorant
    (Centered.offset c.center p) (Centered.offset c.center q) hp hq

def neighborhoodRadius (c : SystemChart n) (p : Scalar) (hp : c.domain p) : QPos :=
  germRadius c.K c.nonnegK (Centered.offset c.center p) hp

theorem neighborhood_inside (c : SystemChart n) (p : Scalar) (hp : c.domain p) (z : Scalar)
    (hz : Centered.domain p (c.neighborhoodRadius p hp).val z) : c.domain z := by
  apply germRadius_inside c.K c.nonnegK (Centered.offset c.center p) hp (Centered.offset c.center z)
  exact Centered.interior_congr (c.neighborhoodRadius p hp).val (Centered.offset p z)
    (Centered.offset (Centered.offset c.center p) (Centered.offset c.center z))
    (equiv_symm (Centered.offset_difference c.center p z)) hz

theorem neighborhood_le (c : SystemChart n) (p : Scalar) (hp : c.domain p) :
    (c.neighborhoodRadius p hp).val ≤ c.radius.val :=
  smallerRadius_le_right _ _

theorem neighborhood_small (c : SystemChart n) (p : Scalar) (hp : c.domain p) :
    2*(c.neighborhoodRadius p hp).val*(8*c.M) ≤ (1 : Rat)/2 := by
  have hr := c.neighborhood_le p hp
  have hs : 2*c.radius.val*(8*c.M) ≤ (1 : Rat)/2 :=
    local_operator_small c.M c.K c.nonnegM c.nonnegK c.compatible
  have hM : 0 ≤ 16*c.M := Rat.mul_nonneg (by decide) c.nonnegM
  have hh := Rat.mul_le_mul_of_nonneg_left hr hM
  grind

end ComputableAnalysis.RiemannHilbert.SystemChart
