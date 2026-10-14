import ComputableAnalysis.RiemannHilbert.DomainVectorFunctions
import ComputableAnalysis.RiemannHilbert.LinearFieldProduct

/-! Analytic coordinate change for a supplied justified horizontal field.
The pullback coefficient is constructed, and horizontality follows from
the actual holomorphic chain rule. This is a local coordinate law;
no bundle or global correspondence is assumed. -/
namespace ComputableAnalysis.RiemannHilbert.CoordinateConnection
open ComplexRaw FunctionTheory DomainVectorFunctions
variable {n : Nat}

abbrev Field (D : Scalar → Prop) := LinearField.Field (n := n) (m := n) D

def Horizontal (f : DomainVectorFunctions.Map n) (hf : DomainVectorFunctions.Holomorphic f)
    (A : Field (n := n) f.domain) : Prop :=
  ∀ z hz, derivative f hf z hz ≈ (A z hz).eval (f.eval z hz)

def pullback (f : DomainVectorFunctions.Map n) (g : DomainFunctions.Map)
    (hg : DomainFunctions.Holomorphic g) (A : Field (n := n) f.domain) : Field (n := n) (pullbackDomain f g) :=
  fun z hz => (A (g.eval z (pullback_inner_mem hz)) (pullback_outer_mem hz)).followedBy
    (Fiber.scaleMap (hg.derivative z (pullback_inner_mem hz)))

theorem pullback_linear (f : DomainVectorFunctions.Map n) (g : DomainFunctions.Map)
    (hg : DomainFunctions.Holomorphic g) (A : Field (n := n) f.domain) (hA : ∀ z hz, IsLinear (A z hz))
    (z : Scalar) (hz : pullbackDomain f g z) : IsLinear (pullback f g hg A z hz) :=
  IsLinear.followedBy (hA _ _) (Fiber.scaleMap_linear _)

theorem horizontal_pullback (f : DomainVectorFunctions.Map n) (hf : DomainVectorFunctions.Holomorphic f)
    (g : DomainFunctions.Map) (hg : DomainFunctions.Holomorphic g) (A : Field (n := n) f.domain)
    (hA : Horizontal f hf A) :
    Horizontal (DomainVectorFunctions.pullback f g) (pullback_holomorphic f hf g hg)
      (pullback f g hg A) := by
  intro z hz
  exact Setoid.trans (pullback_derivative f hf g hg z hz)
    (Fiber.scale_congr (equiv_refl _ (hg.derivative z (pullback_inner_mem hz)).property) (hA _ _))

theorem pullback_point_congr (f : DomainVectorFunctions.Map n) (g : DomainFunctions.Map)
    (hg : DomainFunctions.Holomorphic g) (A : Field (n := n) f.domain)
    (hA : ∀ z w hz hw, z.val.Equiv w.val → (A z hz).Equiv (A w hw))
    (z w : Scalar) (hz : pullbackDomain f g z) (hw : pullbackDomain f g w) (hzw : z.val.Equiv w.val) :
    (pullback f g hg A z hz).Equiv (pullback f g hg A w hw) := by
  intro x
  exact Fiber.scale_congr (hg.derivative_congr _ _ _ _ hzw)
    (hA _ _ _ _ (g.eval_congr _ _ _ _ hzw) x)

end ComputableAnalysis.RiemannHilbert.CoordinateConnection
