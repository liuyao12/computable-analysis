import ComputableAnalysis.Continuation.Gluing

/-!
# Differential equations respect holomorphic germs

The represented derivative is a map on the same domain. Equality of germs
implies equality of derivative germs, not merely equality at the base point.
Iterating this comparison transfers a second-order differential equation.
Holomorphicity of the derivative is supplied: deriving it from arbitrary
holomorphicity is still part of the missing Cauchy/Taylor bridge.
-/
namespace ComputableAnalysis.FunctionTheory
open ComplexRaw

def Holomorphic.derivativeMap {f : Map} (h : Holomorphic f) : Map where
  domain := f.domain
  eval := h.derivative
  valid := fun z hz hfz => (h.atPoint z hz hfz).derivative_valid
  domain_congr := f.domain_congr
  eval_congr := h.derivative_congr

end ComputableAnalysis.FunctionTheory

namespace ComputableAnalysis.Continuation
open ComplexRaw FunctionTheory

/-- Different computational derivative representatives agree throughout a
smaller neighborhood. The witness radius is half the original radius. -/
theorem AgreeAt.derivative {a : Point} {f g : FunctionTheory.Map}
    (h : AgreeAt a f g) (hf : Holomorphic f) (hg : Holomorphic g) :
    AgreeAt a hf.derivativeMap hg.derivativeMap := by
  obtain ⟨r,hr⟩ := h
  refine ⟨⟨r.val/2, by have := r.property; grind⟩, fun z hz hza => ?_⟩
  have hnear := agreeAt_nearby (a := a) (b := ⟨z,hz⟩) r hr hza
  have hfull := hr z hz (hza.mono (by have := r.property; grind))
  exact ⟨hfull.1,hfull.2.1,derivative_eq_of_agreeAt hg.openDomain
    (hf.atPoint z hz hfull.1) (hg.atPoint z hz hfull.2.1) hnear⟩

/-- The actual second-order expression, with arbitrary represented complex
coefficient values. Neither a formal jet nor a vanishing residual is assumed. -/
def secondOrderResidual {f : FunctionTheory.Map} (hf : Holomorphic f)
    (hdf : Holomorphic hf.derivativeMap) (a A B C : ComplexRaw) : ComplexRaw :=
  add (add (mul A (hdf.derivative a)) (mul B (hf.derivative a))) (mul C (f.eval a))

theorem secondOrderResidual_valid {f : FunctionTheory.Map} (hf : Holomorphic f)
    (hdf : Holomorphic hf.derivativeMap) {a A B C : ComplexRaw}
    (ha : a.Valid) (hfa : f.domain a) (hA : A.Valid) (hB : B.Valid) (hC : C.Valid) :
    (secondOrderResidual hf hdf a A B C).Valid :=
  add_valid (add_valid (mul_valid hA (hdf.atPoint a ha hfa).derivative_valid)
    (mul_valid hB (hf.atPoint a ha hfa).derivative_valid)) (mul_valid hC (f.valid a ha hfa))

/-- A second-order ODE is invariant under replacing a solution by the same
germ. This compares values and two actual analytic derivatives. -/
theorem secondOrderResidual_congr {a : Point} {f g : FunctionTheory.Map}
    (hf : Holomorphic f) (hg : Holomorphic g)
    (hdf : Holomorphic hf.derivativeMap) (hdg : Holomorphic hg.derivativeMap)
    (h : AgreeAt a f g) (A B C : ComplexRaw)
    (hA : A.Valid) (hB : B.Valid) (hC : C.Valid) :
    (secondOrderResidual hf hdf a.val A B C).Equiv
      (secondOrderResidual hg hdg a.val A B C) := by
  have h1 := h.derivative hf hg
  have h2 := h1.derivative hdf hdg
  obtain ⟨r,hr⟩ := h
  have hm := hr a.val a.property
    (Small.sub_self _ a.property (Rat.le_of_lt r.property))
  exact add_equiv (add_equiv
    (mul_equiv hA hA (hdf.atPoint a.val a.property hm.1).derivative_valid
      (hdg.atPoint a.val a.property hm.2.1).derivative_valid (equiv_refl _ hA) h2.value)
    (mul_equiv hB hB (hf.atPoint a.val a.property hm.1).derivative_valid
      (hg.atPoint a.val a.property hm.2.1).derivative_valid (equiv_refl _ hB) h1.value))
    (mul_equiv hC hC (f.valid a.val a.property hm.1) (g.valid a.val a.property hm.2.1)
      (equiv_refl _ hC) hm.2.2)

end ComputableAnalysis.Continuation
