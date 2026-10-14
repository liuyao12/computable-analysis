import ComputableAnalysis.RiemannHilbert.GlobalBoundaryCauchy
import ComputableAnalysis.RiemannHilbert.ContourBoundaryBounds

/-! Genuine holomorphic edge domains imply existence of finite positive
value and derivative bounds and actual Cauchy boundary data. Existential
compactness witnesses stay in Prop; executable constructions accept their
rational bounds explicitly, without extracting data by choice. -/
namespace ComputableAnalysis.RiemannHilbert.HolomorphicBoundaryDataExistence
open ComplexRaw FunctionTheory DomainFunctions RectangularContour
set_option autoImplicit false

def derivativeMap (f : DomainFunctions.Map) (hf : Holomorphic f) : DomainFunctions.Map where
  domain := f.domain
  eval := hf.derivative
  domain_congr := f.domain_congr
  eval_congr := hf.derivative_congr

theorem derivativeDomains (f : DomainFunctions.Map) (hf : Holomorphic f)
    (J : QInterval × QInterval) (hd : RectangleBoundaryDomains f J) :
    RectangleBoundaryDomains (derivativeMap f hf) J := ⟨hd.bottom,hd.top,hd.left,hd.right⟩

theorem value_bound_exists (f : DomainFunctions.Map) (hc : ContinuousOn f.domain f.eval)
    (J : QInterval × QInterval) (hx : J.1.lo≤J.1.hi) (hy : J.2.lo≤J.2.hi)
    (hd : RectangleBoundaryDomains f J) : ∃ B : QPos, RectangleBoundaryValueBound f J hd B := by
  obtain ⟨b,hb,hval⟩ := continuousRectangleBoundary_rational_bound f hc J hx hy hd
  let B : QPos := ⟨b+1,by grind only⟩
  refine ⟨B,rectangleBoundaryValueBound_of_rational f hc J hx hy hd B ?_⟩
  intro q hq hz
  exact (hval q hq hz).mono (by change b≤b+1; grind only)

theorem derivative_bound_exists (f : DomainFunctions.Map) (hf : Holomorphic f)
    (J : QInterval × QInterval) (hx : J.1.lo≤J.1.hi) (hy : J.2.lo≤J.2.hi)
    (hd : RectangleBoundaryDomains f J) : ∃ B : QPos, RectangleBoundaryDerivativeBound f hf J hd B := by
  obtain ⟨B,hB⟩ := value_bound_exists (derivativeMap f hf) hf.continuousDerivative J hx hy (derivativeDomains f hf J hd)
  exact ⟨B,⟨hB.bottom,hB.top,hB.left,hB.right⟩⟩

def ofBounds (f : DomainFunctions.Map) (hf : Holomorphic f)
    (J : QInterval × QInterval) (hx : J.1.lo≤J.1.hi) (hy : J.2.lo≤J.2.hi)
    (hd : RectangleBoundaryDomains f J) (B D : QPos)
    (hb : RectangleBoundaryValueBound f J hd B) (hD : RectangleBoundaryDerivativeBound f hf J hd D) :
    GlobalBoundaryCauchy.BoundaryData where
  source := f
  holomorphic := hf
  rectangle := J
  xOrder := hx
  yOrder := hy
  sourceDomains := hd
  valueBound := B
  derivativeBound := D
  values := hb
  derivatives := hD

/-- Supplied actual holomorphicity and edge domains give genuine numerical
data for the Cauchy algorithms. No reconstruction identity is assumed. -/
theorem boundary_data_exists (f : DomainFunctions.Map) (hf : Holomorphic f)
    (J : QInterval × QInterval) (hx : J.1.lo≤J.1.hi) (hy : J.2.lo≤J.2.hi)
    (hd : RectangleBoundaryDomains f J) :
    ∃ d : GlobalBoundaryCauchy.BoundaryData, d.source=f ∧ d.rectangle=J := by
  obtain ⟨B,hB⟩ := value_bound_exists f hf.continuous J hx hy hd
  obtain ⟨D,hD⟩ := derivative_bound_exists f hf J hx hy hd
  exact ⟨ofBounds f hf J hx hy hd B D hB hD,rfl,rfl⟩

end ComputableAnalysis.RiemannHilbert.HolomorphicBoundaryDataExistence
