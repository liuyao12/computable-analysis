import ComputableAnalysis.RiemannHilbert.CoordinateConnectionPullback
import ComputableAnalysis.RiemannHilbert.CenteredChartTransport
import ComputableAnalysis.RiemannHilbert.ChartDataInvariance

/-! Applying analytic coordinate change to every constructed finite-rank
coefficient chart. The pulled-back field is an actual holomorphic solution
of its transformed operator, with normalized sections and reversible
transport inherited from the original chart's evaluation isomorphisms. -/
namespace ComputableAnalysis.RiemannHilbert.CoordinatePullbackChart
open ComplexRaw FunctionTheory DomainVectorFunctions
variable {n : Nat}

def solution (c : SystemChart n) (initial : Fiber n) : DomainVectorFunctions.Map n where
  domain := c.domain
  eval := c.value initial
  domain_congr := c.domain_congr
  eval_congr z w hz hw hzw := c.value_congr c initial initial (equiv_refl _ c.center.property)
    (fun _ => ValueMap.equiv_refl _) (Setoid.refl _) z w hzw hz hw

def solution_holomorphic (c : SystemChart n) (initial : Fiber n) : Holomorphic (solution c initial) where
  openDomain := {
    radius := fun a ha => LocalODE.interiorRadius c.radius.val (Centered.offset c.center a) ha
    inside := fun a ha z hza => LocalODE.interiorRadius_inside c.radius.val (Centered.offset c.center a) ha
      (Centered.offset c.center z) (Small.congr (sub_valid z.property a.property)
        (sub_valid (Centered.offset c.center z).property (Centered.offset c.center a).property)
        (equiv_symm (Centered.offset_difference c.center a z)) hza) }
  coordinates i := DomainFunctions.ofCertifiedHolomorphic (c.coordinate_holomorphic initial i)

theorem solution_derivative (c : SystemChart n) (initial : Fiber n) (z : Scalar) (hz : c.domain z) :
    derivative (solution c initial) (solution_holomorphic c initial) z hz ≈ c.derivative initial z hz :=
  fun i => equiv_refl _ ((c.derivative initial z hz).property i)

theorem solution_horizontal (c : SystemChart n) (initial : Fiber n) :
    CoordinateConnection.Horizontal (solution c initial) (solution_holomorphic c initial) c.operator :=
  fun z hz => Setoid.trans (solution_derivative c initial z hz) (c.value_ode initial z hz)

def domain (c : SystemChart n) (g : DomainFunctions.Map) (z : Scalar) : Prop :=
  ∃ hg : g.domain z, c.domain (g.eval z hg)

theorem inner_mem {c : SystemChart n} {g : DomainFunctions.Map} {z : Scalar} (hz : domain c g z) :
    g.domain z := by obtain ⟨hg,_⟩ := hz; exact hg

theorem image_mem {c : SystemChart n} {g : DomainFunctions.Map} {z : Scalar} (hz : domain c g z) :
    c.domain (g.eval z (inner_mem hz)) := by obtain ⟨hg,hc⟩ := hz; exact hc

def pulledSolution (c : SystemChart n) (initial : Fiber n) (g : DomainFunctions.Map) :
    DomainVectorFunctions.Map n := DomainVectorFunctions.pullback (solution c initial) g

def pulledSolution_holomorphic (c : SystemChart n) (initial : Fiber n) (g : DomainFunctions.Map)
    (hg : DomainFunctions.Holomorphic g) : Holomorphic (pulledSolution c initial g) :=
  pullback_holomorphic (solution c initial) (solution_holomorphic c initial) g hg

def coefficient (c : SystemChart n) (g : DomainFunctions.Map) (hg : DomainFunctions.Holomorphic g) :
    CoordinateConnection.Field (n := n) (domain c g) :=
  fun z hz => (c.operator (g.eval z (inner_mem hz)) (image_mem hz)).followedBy
    (Fiber.scaleMap (hg.derivative z (inner_mem hz)))

theorem coefficient_linear (c : SystemChart n) (g : DomainFunctions.Map) (hg : DomainFunctions.Holomorphic g)
    (z : Scalar) (hz : domain c g z) : IsLinear (coefficient c g hg z hz) :=
  IsLinear.followedBy (c.operator_linear _ _) (Fiber.scaleMap_linear _)

theorem coefficient_point_congr (c : SystemChart n) (g : DomainFunctions.Map)
    (hg : DomainFunctions.Holomorphic g) (z w : Scalar) (hz : domain c g z) (hw : domain c g w)
    (hzw : z.val.Equiv w.val) : (coefficient c g hg z hz).Equiv (coefficient c g hg w hw) := by
  intro x
  exact Fiber.scale_congr (hg.derivative_congr z w _ _ hzw)
    (c.operator_congr c (equiv_refl _ c.center.property) (fun _ => ValueMap.equiv_refl _)
      _ _ (g.eval_congr z w _ _ hzw) _ _ x x (Setoid.refl _))

theorem pulledSolution_ode (c : SystemChart n) (initial : Fiber n) (g : DomainFunctions.Map)
    (hg : DomainFunctions.Holomorphic g) (z : Scalar) (hz : domain c g z) :
    derivative (pulledSolution c initial g) (pulledSolution_holomorphic c initial g hg) z hz ≈
      (coefficient c g hg z hz).eval ((pulledSolution c initial g).eval z hz) :=
  CoordinateConnection.horizontal_pullback (solution c initial) (solution_holomorphic c initial)
    g hg c.operator (solution_horizontal c initial) z hz

def seed (c : SystemChart n) (g : DomainFunctions.Map) (p : Scalar) (hp : domain c g p) (v : Fiber n) : Fiber n :=
  c.seed (g.eval p (inner_mem hp)) (image_mem hp) v

def normalizedSection (c : SystemChart n) (g : DomainFunctions.Map) (p : Scalar) (hp : domain c g p) (v : Fiber n) :
    DomainVectorFunctions.Map n := pulledSolution c (seed c g p hp v) g

def section_holomorphic (c : SystemChart n) (g : DomainFunctions.Map) (hg : DomainFunctions.Holomorphic g)
    (p : Scalar) (hp : domain c g p) (v : Fiber n) : Holomorphic (normalizedSection c g p hp v) :=
  pulledSolution_holomorphic c (seed c g p hp v) g hg

theorem section_normalized (c : SystemChart n) (g : DomainFunctions.Map)
    (p : Scalar) (hp : domain c g p) (v : Fiber n) : (normalizedSection c g p hp v).eval p hp ≈ v :=
  c.through_normalized (g.eval p (inner_mem hp)) (image_mem hp) v

theorem section_ode (c : SystemChart n) (g : DomainFunctions.Map) (hg : DomainFunctions.Holomorphic g)
    (p : Scalar) (hp : domain c g p) (v : Fiber n) (z : Scalar) (hz : domain c g z) :
    derivative (normalizedSection c g p hp v) (section_holomorphic c g hg p hp v) z hz ≈
      (coefficient c g hg z hz).eval ((normalizedSection c g p hp v).eval z hz) :=
  pulledSolution_ode c (seed c g p hp v) g hg z hz

def transport (c : SystemChart n) (g : DomainFunctions.Map) (p q : Scalar)
    (hp : domain c g p) (hq : domain c g q) : LinearIso n n :=
  c.transport (g.eval p (inner_mem hp)) (g.eval q (inner_mem hq)) (image_mem hp) (image_mem hq)

theorem transport_section (c : SystemChart n) (g : DomainFunctions.Map) (p q : Scalar)
    (hp : domain c g p) (hq : domain c g q) (v : Fiber n) :
    (transport c g p q hp hq).toValueIso.forward.eval v = (normalizedSection c g p hp v).eval q hq := rfl

theorem transport_self (c : SystemChart n) (g : DomainFunctions.Map) (p : Scalar) (hp : domain c g p) :
    (transport c g p p hp hp).toValueIso.forward.Equiv ValueMap.identity :=
  c.transport_self _ (image_mem hp)

theorem transport_compose (c : SystemChart n) (g : DomainFunctions.Map) (p q r : Scalar)
    (hp : domain c g p) (hq : domain c g q) (hr : domain c g r) :
    ((transport c g p q hp hq).toValueIso.forward.followedBy
      (transport c g q r hq hr).toValueIso.forward).Equiv (transport c g p r hp hr).toValueIso.forward :=
  c.transport_compose _ _ _ (image_mem hp) (image_mem hq) (image_mem hr)

theorem transport_reverse (c : SystemChart n) (g : DomainFunctions.Map) (p q : Scalar)
    (hp : domain c g p) (hq : domain c g q) :
    (transport c g q p hq hp).toValueIso.forward.Equiv (transport c g p q hp hq).toValueIso.backward :=
  c.transport_reverse _ _ (image_mem hp) (image_mem hq)

end ComputableAnalysis.RiemannHilbert.CoordinatePullbackChart
