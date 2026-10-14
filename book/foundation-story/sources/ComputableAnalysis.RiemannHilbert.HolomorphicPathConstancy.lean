import ComputableAnalysis.RiemannHilbert.UnitIntervalLocalEquality
import ComputableAnalysis.RiemannHilbert.ConstructedSolutionGerms
import ComputableAnalysis.RiemannHilbert.HolomorphicMatrixComposition
import ComputableAnalysis.RiemannHilbert.DomainVectorSuperposition
import ComputableAnalysis.RiemannHilbert.ScalarPaths

/-! An actual holomorphic vector function with zero derivative is constant
along every continuous path in its domain. Local ODE uniqueness constructs
positive equality neighborhoods. A proved finite rational open cover then
propagates equality; no completed scalar or global connectedness is used. -/
namespace ComputableAnalysis.RiemannHilbert.DomainVectorFunctions
open ComplexRaw FunctionTheory LinearField
set_option autoImplicit false
variable {n : Nat} (f : Map n) (hf : Holomorphic f)
    (hzero : ∀ z hz, derivative f hf z hz≈Fiber.zero n)
include hf hzero

/-- A positive equality neighborhood follows from actual zero derivative.
The neighborhood and its domain inclusion are conclusions. -/
theorem zero_derivative_local_constant (b : Scalar) (hb : f.domain b) :
    ∃ R : QPos, (∀ z, Centered.domain b R.val z → f.domain z) ∧
      ∀ z, Centered.domain b R.val z → ∀ hz, f.eval z hz≈f.eval b hb := by
  let G := LinearField.constant (fun _ : Scalar => True) (ValueMap.zeroBetween n n)
  let O := ScalarTopology.wholeData
  let hG := fun (z w : Scalar) (_ _ : True) (_ : z≈w) => ValueMap.equiv_refl (ValueMap.zeroBetween n n)
  let hM := constantMatrixHolomorphic O (ValueMap.zeroBetween n n)
  let x : AnalyticSolutionGerm.Name G b := ⟨f,hf,hb,fun _ _ => trivial,hzero⟩
  let c := constantOn (fun _ : Scalar => True) O.invariant (f.eval b hb)
  let hc := constantOn_holomorphic O (f.eval b hb)
  let y : AnalyticSolutionGerm.Name G b := ⟨c,hc,trivial,fun _ _ => trivial,fun _ _ => Setoid.refl _⟩
  have he : x≈y := (AnalyticSolutionGerm.agreement_iff_evaluation G O hG hM
    (fun _ _ => ValueMap.zeroBetween_linear n n) b trivial x y).2 (Setoid.refl _)
  obtain ⟨R,hx,hy,hxy⟩ := he
  exact ⟨R,hx,fun z hz hzf => hxy z hz hzf (hy z hz)⟩

/-- Exact constancy along an arbitrary represented continuous route.
Pointwise holomorphic data suffice; the finite cover is internal. -/
theorem zero_derivative_path_constant {p q : Scalar} (a : ScalarPaths.Path p q)
    (inside : ∀ t, f.domain (a.eval t))
    (hp : f.domain p) (hq : f.domain q) : f.eval p hp≈f.eval q hq := by
  let Index := {b : Scalar // f.domain b} × QPos
  let U : Index → UnitInterval.Point → Prop := fun k t =>
    Centered.domain k.1.val k.2.val (a.eval t) ∧
      ∀ z, Centered.domain k.1.val k.2.val z → ∀ hz, f.eval z hz≈f.eval k.1.val k.1.property
  have hU : ∀ k, UnitInterval.IsOpen (U k) := by
    intro k
    have ho := a.continuous _ (ScalarTopology.isOpen_ball k.1.val k.2)
    exact {
      invariant s t hst := and_congr (ho.invariant s t hst) Iff.rfl
      neighborhood s hs := by
        obtain ⟨r,hr⟩ := ho.neighborhood s hs.1
        exact ⟨r,fun t ht => ⟨hr t ht,hs.2⟩⟩ }
  have cover : ∀ t, ∃ k, U k t := by
    intro t
    obtain ⟨R,_hinside,he⟩ := zero_derivative_local_constant f hf hzero (a.eval t) (inside t)
    exact ⟨⟨⟨a.eval t,inside t⟩,R⟩,Centered.center_mem (a.eval t) R,he⟩
  have he := UnitInterval.values_equal_of_local U hU cover (fun t => f.eval (a.eval t) (inside t))
    (fun _ s t hs ht => Setoid.trans (hs.2 _ hs.1 (inside s)) (Setoid.symm (ht.2 _ ht.1 (inside t))))
  exact Setoid.trans (f.eval_congr p (a.eval UnitInterval.zero) hp (inside UnitInterval.zero) (Setoid.symm a.source))
    (Setoid.trans he (f.eval_congr (a.eval UnitInterval.one) q (inside UnitInterval.one) hq a.target))

end ComputableAnalysis.RiemannHilbert.DomainVectorFunctions
