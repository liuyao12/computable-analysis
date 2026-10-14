import ComputableAnalysis.RiemannHilbert.CoefficientAtlasTransport
import ComputableAnalysis.RiemannHilbert.FrameChartComparison

/-! Analytic independence of the chart used for intrinsic atlas transport.
The result is derived from the actual varying-horizontal-map theorem, with
explicit derivative estimates. The same proof glues actual local horizontal
sections on their entire intersection. -/
namespace ComputableAnalysis.RiemannHilbert.CoefficientAtlas
universe u
open ComplexRaw FunctionTheory LocalSystem
variable {I : Type u} {n : Nat}

def overlapField (a : CoefficientAtlas I n) (i j : I) :
    LinearField.Field (n := n) (m := n) (FrameComparison.domain (a.chart i) (a.chart j)) :=
  fun z hz => (a.transition z i j hz.1 hz.2).toValueIso.forward

section Comparison
variable (a : CoefficientAtlas I n) (i j : I)
variable (DG : LinearField.Field (n := n) (m := n) (FrameComparison.domain (a.chart i) (a.chart j)))
variable (hcompat : LinearField.Compatible (a.overlapField i j) DG
  (fun z hz => (a.chart i).operator z hz.1) (fun z hz => (a.chart j).operator z hz.2))
variable (P Q : Rat) (hP : 0 ≤ P) (hQ : 0 ≤ Q)
variable (hGbound : ∀ z hz E, 0 ≤ E → ∀ x, CoordinateBound x E →
  CoordinateBound ((a.overlapField i j z hz).eval x) (P*E))
variable (hDGbound : ∀ z hz E, 0 ≤ E → ∀ x, CoordinateBound x E →
  CoordinateBound ((DG z hz).eval x) (Q*E))
variable (deltaG : QPos → QPos)
variable (hGrem : ∀ (eps H : QPos) w z hw hz, H.val ≤ (deltaG eps).val →
  Small (sub z.val w.val) H.val → ∀ E, 0 ≤ E → ∀ x, CoordinateBound x E →
    CoordinateBound (LinearField.operatorRemainder (a.overlapField i j) DG w z hw hz x) ((eps.val*H.val)*E))

include hcompat hP hQ hGbound hDGbound hGrem
theorem localTransport_chart_independent (p q : Scalar)
    (hip : (a.chart i).domain p) (hjp : (a.chart j).domain p)
    (hiq : (a.chart i).domain q) (hjq : (a.chart j).domain q) :
    (a.localTransport i p q hip hiq).forward.Equiv (a.localTransport j p q hjp hjq).forward :=
  a.localTransport_agreement_of_natural i j p q hip hjp hiq hjq
    (FrameComparison.transport_natural (a.chart i) (a.chart j) (a.overlapField i j) DG
      (fun z hz => (a.transition z i j hz.1 hz.2).linear)
      (fun z w hz hw hzw => a.transition_congr z w i j hz.1 hz.2 hw.1 hw.2 hzw)
      hcompat P Q hP hQ hGbound hDGbound deltaG hGrem p q hip hjp hiq hjq)

theorem localTransport_inverse_chart_independent (p q : Scalar)
    (hip : (a.chart i).domain p) (hjp : (a.chart j).domain p)
    (hiq : (a.chart i).domain q) (hjq : (a.chart j).domain q) :
    (a.localTransport i p q hip hiq).backward.Equiv (a.localTransport j p q hjp hjq).backward :=
  ValueIso.inverse_congr _ _
    (a.localTransport_chart_independent i j DG hcompat P Q hP hQ hGbound hDGbound deltaG hGrem p q hip hjp hiq hjq)
end Comparison

def localSection (a : CoefficientAtlas I n) (i : I) (p : Scalar) (hp : (a.chart i).domain p)
    (v : a.PointFiber p) (z : Scalar) (hz : (a.chart i).domain z) : a.PointFiber z :=
  AtlasFiber.inChart i hz ((a.chart i).through p hp (AtlasFiber.coordinatesIn i hp v) z hz)

theorem localSection_transport (a : CoefficientAtlas I n) (i : I) (p : Scalar)
    (hp : (a.chart i).domain p) (v : a.PointFiber p) (z : Scalar) (hz : (a.chart i).domain z) :
    a.localSection i p hp v z hz = (a.localTransport i p z hp hz).forward.eval v := rfl

def localSectionCoordinate (a : CoefficientAtlas I n) (i : I) (p : Scalar)
    (hp : (a.chart i).domain p) (v : a.PointFiber p) (d : Fin n) : CertifiedFunctions.Map :=
  (a.chart i).coordinate ((a.chart i).seed p hp (AtlasFiber.coordinatesIn i hp v)) d

theorem localSectionCoordinate_value (a : CoefficientAtlas I n) (i : I) (p : Scalar)
    (hp : (a.chart i).domain p) (v : a.PointFiber p) (d : Fin n) (z : Scalar) (hz : (a.chart i).domain z) :
    (a.localSectionCoordinate i p hp v d).eval z = (a.localSection i p hp v z hz).coordinates.val d := rfl

def localSectionCoordinate_holomorphic (a : CoefficientAtlas I n) (i : I) (p : Scalar)
    (hp : (a.chart i).domain p) (v : a.PointFiber p) (d : Fin n) :
    CertifiedFunctions.Holomorphic (a.localSectionCoordinate i p hp v d) :=
  (a.chart i).through_holomorphic p hp (AtlasFiber.coordinatesIn i hp v) d

theorem localSection_normalized (a : CoefficientAtlas I n) (i : I) (p : Scalar)
    (hp : (a.chart i).domain p) (v : a.PointFiber p) :
    a.localSection i p hp v p hp ≈ v :=
  a.localTransport_self i p hp v

theorem localSection_agreement_of_transport (a : CoefficientAtlas I n) (i j : I) (p z : Scalar)
    (hip : (a.chart i).domain p) (hjp : (a.chart j).domain p)
    (hiz : (a.chart i).domain z) (hjz : (a.chart j).domain z) (v : a.PointFiber p)
    (h : (a.localTransport i p z hip hiz).forward.Equiv (a.localTransport j p z hjp hjz).forward) :
    a.localSection i p hip v z hiz ≈ a.localSection j p hjp v z hjz := h v

end ComputableAnalysis.RiemannHilbert.CoefficientAtlas
