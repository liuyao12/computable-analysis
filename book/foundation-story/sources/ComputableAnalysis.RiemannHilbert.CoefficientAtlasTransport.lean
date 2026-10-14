import ComputableAnalysis.RiemannHilbert.AtlasFiberAlgebra
import ComputableAnalysis.RiemannHilbert.FrameAtlas
import ComputableAnalysis.RiemannHilbert.ChartDataInvariance

/-! Atlas fibers for actual bounded coefficient charts, and the actual local
analytic transport between them. The input cocycle glues fiber coordinates;
transport identities and coordinate formulas are proved from chart solutions. -/
namespace ComputableAnalysis.RiemannHilbert
universe u

structure CoefficientAtlas (I : Type u) (n : Nat) where
  chart : I → SystemChart n
  transition : (p : Scalar) → (i j : I) → (chart i).domain p → (chart j).domain p → LinearIso n n
  cocycle : ∀ p i j k hi hj hk,
    ((transition p i j hi hj).toValueIso.forward.followedBy
      (transition p j k hj hk).toValueIso.forward).Equiv
      (transition p i k hi hk).toValueIso.forward
  transition_congr : ∀ p q i j hip hjp hiq hjq, p.val.Equiv q.val →
    (transition p i j hip hjp).toValueIso.forward.Equiv
      (transition q i j hiq hjq).toValueIso.forward

namespace CoefficientAtlas
variable {I : Type u} {n : Nat}

def toTransitionAtlas (a : CoefficientAtlas I n) : TransitionAtlas Scalar I n where
  domain i := (a.chart i).domain
  transition := a.transition
  cocycle := a.cocycle

abbrev PointFiber (a : CoefficientAtlas I n) (p : Scalar) := AtlasFiber a.toTransitionAtlas p

def ofFrames (c : I → SystemChart n)
    (F : (i : I) → (p : Scalar) → (c i).domain p → LinearIso n n)
    (hF : ∀ i p q hp hq, p.val.Equiv q.val →
      (F i p hp).toValueIso.forward.Equiv (F i q hq).toValueIso.forward) : CoefficientAtlas I n where
  chart := c
  transition p i j hi hj := (F i p hi).inverse.followedBy (F j p hj)
  cocycle := (TransitionAtlas.ofFrames (fun i => (c i).domain) F).cocycle
  transition_congr p q i j hip hjp hiq hjq hpq :=
    ValueMap.followedBy_congr (ValueIso.inverse_congr _ _ (hF i p q hip hiq hpq))
      (hF j p q hjp hjq hpq)

def localTransport (a : CoefficientAtlas I n) (i : I) (p q : Scalar)
    (hp : (a.chart i).domain p) (hq : (a.chart i).domain q) :
    ValueIso (a.PointFiber p) (a.PointFiber q) :=
  ((AtlasFiber.chartIso i hp).followedBy ((a.chart i).transport p q hp hq).toValueIso).followedBy
    (AtlasFiber.chartIso i hq).inverse

theorem localTransport_coordinates (a : CoefficientAtlas I n) (i : I) (p q : Scalar)
    (hp : (a.chart i).domain p) (hq : (a.chart i).domain q) (x : a.PointFiber p) :
    AtlasFiber.coordinatesIn i hq ((a.localTransport i p q hp hq).forward.eval x) ≈
      ((a.chart i).transport p q hp hq).toValueIso.forward.eval (AtlasFiber.coordinatesIn i hp x) :=
  AtlasFiber.coordinatesIn_inChart i hq _

theorem localTransport_self (a : CoefficientAtlas I n) (i : I) (p : Scalar)
    (hp : (a.chart i).domain p) :
    (a.localTransport i p p hp hp).forward.Equiv ValueMap.identity := by
  intro x
  exact Setoid.trans (AtlasFiber.inChart_congr i hp ((a.chart i).transport_self p hp _))
    (AtlasFiber.inChart_coordinatesIn i hp x)

theorem localTransport_compose (a : CoefficientAtlas I n) (i : I) (p q r : Scalar)
    (hp : (a.chart i).domain p) (hq : (a.chart i).domain q) (hr : (a.chart i).domain r) :
    ((a.localTransport i p q hp hq).forward.followedBy (a.localTransport i q r hq hr).forward).Equiv
      (a.localTransport i p r hp hr).forward := by
  intro x
  apply AtlasFiber.inChart_congr i hr
  exact Setoid.trans
    (((a.chart i).transport q r hq hr).toValueIso.forward.congr (a.localTransport_coordinates i p q hp hq x))
    ((a.chart i).transport_compose p q r hp hq hr (AtlasFiber.coordinatesIn i hp x))

theorem localTransport_reverse (a : CoefficientAtlas I n) (i : I) (p q : Scalar)
    (hp : (a.chart i).domain p) (hq : (a.chart i).domain q) :
    (a.localTransport i q p hq hp).forward.Equiv (a.localTransport i p q hp hq).backward := by
  intro x
  exact AtlasFiber.inChart_congr i hp
    ((a.chart i).transport_reverse p q hp hq (AtlasFiber.coordinatesIn i hq x))

theorem localTransport_add (a : CoefficientAtlas I n) (i : I) (p q : Scalar)
    (hp : (a.chart i).domain p) (hq : (a.chart i).domain q) (x y : a.PointFiber p) :
    (a.localTransport i p q hp hq).forward.eval (AtlasFiber.add x y) ≈
      AtlasFiber.add ((a.localTransport i p q hp hq).forward.eval x)
        ((a.localTransport i p q hp hq).forward.eval y) := by
  apply AtlasFiber.coordinatesIn_reflects i hq
  exact Setoid.trans (a.localTransport_coordinates i p q hp hq (AtlasFiber.add x y))
    (Setoid.trans (((a.chart i).transport p q hp hq).toValueIso.forward.congr (AtlasFiber.coordinatesIn_add i hp x y))
      (Setoid.trans (((a.chart i).transport p q hp hq).linear.1 _ _)
        (Setoid.trans (Fiber.add_congr (Setoid.symm (a.localTransport_coordinates i p q hp hq x))
          (Setoid.symm (a.localTransport_coordinates i p q hp hq y)))
          (Setoid.symm (AtlasFiber.coordinatesIn_add i hq _ _)))))

theorem localTransport_scale (a : CoefficientAtlas I n) (i : I) (p q : Scalar)
    (hp : (a.chart i).domain p) (hq : (a.chart i).domain q) (s : Scalar) (x : a.PointFiber p) :
    (a.localTransport i p q hp hq).forward.eval (AtlasFiber.scale s x) ≈
      AtlasFiber.scale s ((a.localTransport i p q hp hq).forward.eval x) := by
  apply AtlasFiber.coordinatesIn_reflects i hq
  exact Setoid.trans (a.localTransport_coordinates i p q hp hq (AtlasFiber.scale s x))
    (Setoid.trans (((a.chart i).transport p q hp hq).toValueIso.forward.congr (AtlasFiber.coordinatesIn_scale i hp s x))
      (Setoid.trans (((a.chart i).transport p q hp hq).linear.2 s _)
        (Setoid.trans (Fiber.scale_congr (ComplexRaw.equiv_refl _ s.property)
          (Setoid.symm (a.localTransport_coordinates i p q hp hq x)))
          (Setoid.symm (AtlasFiber.coordinatesIn_scale i hq s _)))))

theorem localTransport_agreement_of_natural (a : CoefficientAtlas I n) (i j : I) (p q : Scalar)
    (hip : (a.chart i).domain p) (hjp : (a.chart j).domain p)
    (hiq : (a.chart i).domain q) (hjq : (a.chart j).domain q)
    (h : ((a.transition p i j hip hjp).toValueIso.forward.followedBy
      ((a.chart j).transport p q hjp hjq).toValueIso.forward).Equiv
      (((a.chart i).transport p q hip hiq).toValueIso.forward.followedBy
        (a.transition q i j hiq hjq).toValueIso.forward)) :
    (a.localTransport i p q hip hiq).forward.Equiv (a.localTransport j p q hjp hjq).forward := by
  intro x
  change (a.transition q i j hiq hjq).toValueIso.forward.eval
      (((a.chart i).transport p q hip hiq).toValueIso.forward.eval (AtlasFiber.coordinatesIn i hip x)) ≈
    ((a.chart j).transport p q hjp hjq).toValueIso.forward.eval (AtlasFiber.coordinatesIn j hjp x)
  exact Setoid.trans (Setoid.symm (h (AtlasFiber.coordinatesIn i hip x)))
    (((a.chart j).transport p q hjp hjq).toValueIso.forward.congr
      (AtlasFiber.change_coordinates i j hip hjp x))

end CoefficientAtlas
end ComputableAnalysis.RiemannHilbert
