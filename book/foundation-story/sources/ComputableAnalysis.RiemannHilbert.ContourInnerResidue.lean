import ComputableAnalysis.RiemannHilbert.ContourLimitComparison

/-! The shrinking inner Cauchy boundary has the center-times-period value
whenever the actual reciprocal boundary sequence has its supplied limit.
All local frame radii and numerator estimates are constructed here. -/
namespace ComputableAnalysis.RiemannHilbert.RectangularContour
open ComplexRaw FunctionTheory DomainFunctions
set_option autoImplicit false

def innerResidueError (f : DomainFunctions.Map) (hf : Holomorphic f)
    (a : Scalar) (ha : f.domain a) (mesh : Nat → Nat) (n : Nat) : Scalar :=
  gridScalarSub (shrinkingCauchyPrefix f hf a ha n (mesh n))
    (scalarProduct (f.eval a ha) (shrinkingReciprocalPrefix f hf a ha n (mesh n)))

theorem innerResidueError_eventual_bound (f : DomainFunctions.Map) (hf : Holomorphic f)
    (a : Scalar) (ha : f.domain a) (mesh : Nat → Nat) (hm : ∀ n, 0<mesh n) (eps : QPos) :
    ∃ N, ∀ n, N≤n → Small (innerResidueError f hf a ha mesh n).val eps.val := by
  let eta := divideRadius eps (⟨64,by decide +kernel⟩ : QPos)
  let N := contourErrorStage f hf a ha (hf.continuous.delta a ha eta)
  refine ⟨N, ?_⟩
  intro n hn
  have hb := shrinkingPrefix_center_estimate f hf a ha eta n (mesh n) (hm n) hn
  have he : 64*eta.val=eps.val := divideRadius_identity eps (⟨64,by decide +kernel⟩ : QPos)
  rw [he] at hb
  exact hb

theorem innerResidueError_zero (f : DomainFunctions.Map) (hf : Holomorphic f)
    (a : Scalar) (ha : f.domain a) (mesh : Nat → Nat) (hm : ∀ n, 0<mesh n) :
    Converges (innerResidueError f hf a ha mesh) ⟨zero,ofQComplex_valid _⟩ :=
  converge_zero _ (innerResidueError_eventual_bound f hf a ha mesh hm)

theorem shrinking_inner_converges (f : DomainFunctions.Map) (hf : Holomorphic f)
    (a : Scalar) (ha : f.domain a) (mesh : Nat → Nat) (hm : ∀ n, 0<mesh n) (period : Scalar)
    (hp : Converges (fun n => shrinkingReciprocalPrefix f hf a ha n (mesh n)) period) :
    Converges (fun n => shrinkingCauchyPrefix f hf a ha n (mesh n)) (scalarProduct (f.eval a ha) period) :=
  converge_perturbation _ _ _ (converge_product_left (f.eval a ha) _ period hp)
    (innerResidueError_eventual_bound f hf a ha mesh hm)

theorem shrinking_inner_limit_identity (f : DomainFunctions.Map) (hf : Holomorphic f)
    (a : Scalar) (ha : f.domain a) (mesh : Nat → Nat) (hm : ∀ n, 0<mesh n) (period u : Scalar)
    (hp : Converges (fun n => shrinkingReciprocalPrefix f hf a ha n (mesh n)) period)
    (hu : Converges (fun n => shrinkingCauchyPrefix f hf a ha n (mesh n)) u) :
    u ≈ scalarProduct (f.eval a ha) period :=
  converge_unique _ _ _ hu (shrinking_inner_converges f hf a ha mesh hm period hp)

end ComputableAnalysis.RiemannHilbert.RectangularContour
