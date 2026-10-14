import ComputableAnalysis.RiemannHilbert.ExponentialFrameHolomorphic
import ComputableAnalysis.RiemannHilbert.HolomorphicPathConstancy

/-! Global constant-coefficient uniqueness for actual holomorphic solutions.
The inverse exponential reduces the equation to zero derivative. Checked
local uniqueness and the finite rational open-cover argument in path constancy
provide domain coverage; no equality or continuation provider is assumed. -/
namespace ComputableAnalysis.RiemannHilbert.MatrixExponential
open ComplexRaw FunctionTheory DomainVectorFunctions LinearField
set_option autoImplicit false
variable {n : Nat}

theorem constant_ode_path_unique
    (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A)
    (f g : DomainVectorFunctions.Map n)
    (hf : DomainVectorFunctions.Holomorphic f) (hg : DomainVectorFunctions.Holomorphic g)
    (hfODE : CoordinateConnection.Horizontal f hf (fun _ _ => A))
    (hgODE : CoordinateConnection.Horizontal g hg (fun _ _ => A))
    {p q : Scalar} (a : ScalarPaths.Path p q)
    (insideF : ∀ t, f.domain (a.eval t)) (insideG : ∀ t, g.domain (a.eval t))
    (hfp : f.domain p) (hfq : f.domain q) (hgp : g.domain p) (hgq : g.domain q)
    (hinitial : f.eval p hfp ≈ g.eval p hgp) : f.eval q hfq ≈ g.eval q hgq := by
  let N := inverseField (frameField A hA)
  let hN := frame_inverse_holomorphic A hA
  let F := action N (frame_inverse_congr A hA) f (fun _ _ => True.intro)
  let G := action N (frame_inverse_congr A hA) g (fun _ _ => True.intro)
  let hF := action_holomorphic N (fun _ _ _ => Iff.rfl) (frame_inverse_congr A hA)
    (fun z _ => value_linear (negativeOperator A) (negativeOperator_linear A hA) z)
    hN f hf (fun _ _ => True.intro)
  let hG := action_holomorphic N (fun _ _ _ => Iff.rfl) (frame_inverse_congr A hA)
    (fun z _ => value_linear (negativeOperator A) (negativeOperator_linear A hA) z)
    hN g hg (fun _ _ => True.intro)
  have hzF : ∀ z hz, derivative F hF z hz ≈ Fiber.zero n :=
    frame_inverse_horizontal A hA hN f hf hfODE
  have hzG : ∀ z hz, derivative G hG z hz ≈ Fiber.zero n :=
    frame_inverse_horizontal A hA hN g hg hgODE
  have hpathF := zero_derivative_path_constant F hF hzF a insideF hfp hfq
  have hpathG := zero_derivative_path_constant G hG hzG a insideG hgp hgq
  have he : (N q True.intro).eval (f.eval q hfq) ≈ (N q True.intro).eval (g.eval q hgq) :=
    Setoid.trans (Setoid.symm hpathF)
      (Setoid.trans ((N p True.intro).congr hinitial) hpathG)
  exact (frame A hA q).toValueIso.inverse.forward_reflects he

/-- Entire solutions need no caller-supplied path, bounds or neighborhoods.
The constructed affine route covers every valid represented endpoint. -/
theorem constant_ode_entire_unique
    (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A)
    (f g : DomainVectorFunctions.Map n)
    (hf : DomainVectorFunctions.Holomorphic f) (hg : DomainVectorFunctions.Holomorphic g)
    (hfullF : ∀ z, f.domain z) (hfullG : ∀ z, g.domain z)
    (hfODE : CoordinateConnection.Horizontal f hf (fun _ _ => A))
    (hgODE : CoordinateConnection.Horizontal g hg (fun _ _ => A))
    (p : Scalar) (hinitial : f.eval p (hfullF p) ≈ g.eval p (hfullG p))
    (z : Scalar) : f.eval z (hfullF z) ≈ g.eval z (hfullG z) :=
  constant_ode_path_unique A hA f g hf hg hfODE hgODE (ScalarPaths.affine p z)
    (fun _t => hfullF _) (fun _t => hfullG _) (hfullF p) (hfullF z)
    (hfullG p) (hfullG z) hinitial

end ComputableAnalysis.RiemannHilbert.MatrixExponential
