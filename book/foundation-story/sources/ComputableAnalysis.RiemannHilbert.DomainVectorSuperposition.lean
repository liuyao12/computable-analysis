import ComputableAnalysis.RiemannHilbert.DomainHolomorphicIntersectionSum
import ComputableAnalysis.RiemannHilbert.DomainVectorScaling

/-! Actual vector sums on common open domains and multiplication by an
arbitrary valid represented complex constant, with the actual derivatives.
The domain construction retains openness even for the empty vector. -/
namespace ComputableAnalysis.RiemannHilbert.DomainVectorFunctions
open ComplexRaw FunctionTheory DomainFunctions
set_option autoImplicit false
variable {n : Nat}

def openData {f : Map n} (hf : Holomorphic f) : ScalarTopology.OpenData f.domain :=
  ⟨f.domain_congr,hf.openDomain.radius,hf.openDomain.inside⟩

def intersectionSum (f g : Map n) : Map n where
  domain z := f.domain z ∧ g.domain z
  eval z hz := Fiber.add (f.eval z hz.1) (g.eval z hz.2)
  domain_congr z w he := and_congr (f.domain_congr z w he) (g.domain_congr z w he)
  eval_congr z w hz hw he := Fiber.add_congr (f.eval_congr z w hz.1 hw.1 he)
    (g.eval_congr z w hz.2 hw.2 he)

def intersectionSum_holomorphic (f g : Map n) (hf : Holomorphic f) (hg : Holomorphic g) :
    Holomorphic (intersectionSum f g) where
  openDomain := {
    radius z hz := minRadius (hf.openDomain.radius z hz.1) (hg.openDomain.radius z hz.2)
    inside a ha z hd := ⟨hf.openDomain.inside a ha.1 z (hd.mono (minRadius_left _ _)),
      hg.openDomain.inside a ha.2 z (hd.mono (minRadius_right _ _))⟩ }
  coordinates i := (hf i).intersectionSum (hg i)

theorem intersectionSum_derivative (f g : Map n) (hf : Holomorphic f) (hg : Holomorphic g)
    (z : Scalar) (hz : (intersectionSum f g).domain z) :
    derivative (intersectionSum f g) (intersectionSum_holomorphic f g hf hg) z hz≈
      Fiber.add (derivative f hf z hz.1) (derivative g hg z hz.2) :=
  fun i => equiv_refl _ (add_valid ((derivative f hf z hz.1).property i) ((derivative g hg z hz.2).property i))

def constantScaled (f : Map n) (a : Scalar) : Map n :=
  scaled f (DomainFunctions.constantOn f.domain f.domain_congr a) (fun _ hz => hz)

def constantScaled_holomorphic (f : Map n) (hf : Holomorphic f) (a : Scalar) :
    Holomorphic (constantScaled f a) :=
  scaled_holomorphic f hf _ (DomainFunctions.constantOn_holomorphic (openData hf) a) (fun _ hz => hz)

theorem constantScaled_derivative (f : Map n) (hf : Holomorphic f) (a : Scalar)
    (z : Scalar) (hz : f.domain z) :
    derivative (constantScaled f a) (constantScaled_holomorphic f hf a) z hz≈
      Fiber.scale a (derivative f hf z hz) := by
  intro i
  change (add (mul zero ((f.eval z hz).val i)) (mul a.val ((derivative f hf z hz).val i))).Equiv
    (mul a.val ((derivative f hf z hz).val i))
  exact equiv_trans (add_valid (mul_valid (ofQComplex_valid _) ((f.eval z hz).property i))
    (mul_valid a.property ((derivative f hf z hz).property i)))
    (add_valid (ofQComplex_valid _) (mul_valid a.property ((derivative f hf z hz).property i)))
    (mul_valid a.property ((derivative f hf z hz).property i))
    (add_equiv (zero_mul_equiv _ ((f.eval z hz).property i)) (equiv_refl _ (mul_valid a.property ((derivative f hf z hz).property i))))
    (zero_add_equiv _ (mul_valid a.property ((derivative f hf z hz).property i)))

end ComputableAnalysis.RiemannHilbert.DomainVectorFunctions
