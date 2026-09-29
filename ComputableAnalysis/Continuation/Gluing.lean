import ComputableAnalysis.Continuation.Derivative

/-!
# Effective local gluing of holomorphic maps

A supplied represented map locally agrees with supplied holomorphic charts.
The theorem constructs its derivative, derivative modulus, and derivative
continuity; these global conclusions are not assumed as fields. Choosing the
local charts is runtime data, not an application of classical choice.
-/
namespace ComputableAnalysis.Continuation
open ComplexRaw FunctionTheory

structure Chart where
  map : FunctionTheory.Map
  holomorphic : Holomorphic map

structure LocalModels (f : FunctionTheory.Map) where
  chart : ComplexRaw → Chart
  radius : ∀ a, a.Valid → f.domain a → QPos
  agreement : ∀ a ha hfa z, z.Valid → Small (sub z a) (radius a ha hfa).val →
    f.domain z ∧ (chart a).map.domain z ∧
      (f.eval z).Equiv ((chart a).map.eval z)

private def halfPos (r : QPos) : QPos := ⟨r.val/2, by have := r.property; grind⟩
private def minPos (r s : QPos) : QPos := ⟨min r.val s.val, by
  have := r.property; have := s.property; grind⟩
private theorem minPos_left (r s : QPos) : (minPos r s).val ≤ r.val := by
  dsimp [minPos]; grind
private theorem minPos_right (r s : QPos) : (minPos r s).val ≤ s.val := by
  dsimp [minPos]; grind
private theorem half_le (r : QPos) : r.val/2 ≤ r.val := by
  have := r.property; grind

namespace LocalModels
variable {f : FunctionTheory.Map} (L : LocalModels f)

def openDomain : OpenDomain f where
  radius := L.radius
  inside := fun a ha hfa z hz hza => (L.agreement a ha hfa z hz hza).1

def derivative (a : ComplexRaw) : ComplexRaw := (L.chart a).holomorphic.derivative a

theorem chart_mem (a : ComplexRaw) (ha : a.Valid) (hfa : f.domain a) :
    (L.chart a).map.domain a :=
  (L.agreement a ha hfa a ha
    (Small.sub_self a ha (Rat.le_of_lt (L.radius a ha hfa).property))).2.1

def atPoint (a : ComplexRaw) (ha : a.Valid) (hfa : f.domain a) :
    HasDerivativeAt f a (L.derivative a) :=
  ((L.chart a).holomorphic.atPoint a ha (L.chart_mem a ha hfa)).congrMap
    (L.radius a ha hfa) (fun z hz hza => by
      obtain ⟨hf,hg,he⟩ := L.agreement a ha hfa z hz hza
      exact ⟨hg,hf,equiv_symm he⟩)

def continuityRadius (a : ComplexRaw) (ha : a.Valid) (hfa : f.domain a) (eps : QPos) : QPos :=
  minPos (halfPos (L.radius a ha hfa))
    ((L.chart a).holomorphic.continuousDerivative.delta a ha (L.chart_mem a ha hfa) eps)

set_option maxHeartbeats 800000 in
theorem continuity_estimate (a : ComplexRaw) (ha : a.Valid) (hfa : f.domain a)
    (eps : QPos) (z : ComplexRaw) (hz : z.Valid) (hfz : f.domain z)
    (hza : Small (sub z a) (L.continuityRadius a ha hfa eps).val) :
    Small (sub (L.derivative z) (L.derivative a)) eps.val := by
  let r := L.radius a ha hfa
  have hhalf : Small (sub z a) (r.val/2) := hza.mono (minPos_left _ _)
  have hr : Small (sub z a) r.val := hhalf.mono (half_le r)
  have hlocalz := (L.agreement a ha hfa z hz hr).2.1
  have hgerm : AgreeAt ⟨z,hz⟩ f (L.chart a).map :=
    agreeAt_nearby (a := ⟨a,ha⟩) (b := ⟨z,hz⟩) r (L.agreement a ha hfa) hhalf
  have hder : (L.derivative z).Equiv ((L.chart a).holomorphic.derivative z) :=
    derivative_eq_of_agreeAt (a := ⟨z,hz⟩) (L.chart a).holomorphic.openDomain
      (L.atPoint z hz hfz) ((L.chart a).holomorphic.atPoint z hz hlocalz) hgerm
  have hc := (L.chart a).holomorphic.continuousDerivative.estimate
    a ha (L.chart_mem a ha hfa) eps z hz hlocalz (hza.mono (minPos_right _ _))
  apply Small.congr
    (sub_valid ((L.chart a).holomorphic.atPoint z hz hlocalz).derivative_valid
      (L.atPoint a ha hfa).derivative_valid)
    (sub_valid (L.atPoint z hz hfz).derivative_valid (L.atPoint a ha hfa).derivative_valid)
    _ hc
  exact FunctionTheory.sub_congr (equiv_symm hder)
    (equiv_refl _ (L.atPoint a ha hfa).derivative_valid)

/-- A locally glued map is holomorphic at arbitrary represented inputs.
Derivative continuity is transported from one fixed chart near each point. -/
def holomorphic : Holomorphic f where
  openDomain := L.openDomain
  derivative := L.derivative
  atPoint := L.atPoint
  derivative_congr := by
    intro a b ha hb hfa hfb hab
    exact ((L.atPoint a ha hfa).congrPoint hb hab).unique L.openDomain (L.atPoint b hb hfb)
  continuousDerivative := {
    delta := L.continuityRadius
    estimate := L.continuity_estimate }

end LocalModels
end ComputableAnalysis.Continuation
