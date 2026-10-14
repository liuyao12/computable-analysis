import ComputableAnalysis.RiemannHilbert.DomainAffineFunction
import ComputableAnalysis.RiemannHilbert.DomainHolomorphicValueLaws

/-! Actual entire represented monomials, with name invariance and
holomorphic witnesses built from the quantitative affine and product laws. -/
namespace ComputableAnalysis.RiemannHilbert.EntireMonomial
open ComplexRaw FunctionTheory LocalODE DomainFunctions
set_option autoImplicit false

def scalar (z : Scalar) (k : Nat) : Scalar := ⟨power z.val k,power_valid z.val z.property k⟩

theorem scalar_names (z w : Scalar) (he : z≈w) (k : Nat) : scalar z k≈scalar w k := by
  induction k with
  | zero => exact equiv_refl _ (ofQComplex_valid _)
  | succ k ih => exact mul_equiv (scalar z k).property (scalar w k).property z.property w.property ih he

def function (k : Nat) : DomainFunctions.Map where
  domain _ := True
  eval z _ := scalar z k
  domain_congr _ _ _ := Iff.rfl
  eval_congr z w _ _ he := scalar_names z w he k

def identity : DomainFunctions.Map where
  domain _ := True
  eval z _ := z
  domain_congr _ _ _ := Iff.rfl
  eval_congr _ _ _ _ he := he

def identity_holomorphic : Holomorphic identity :=
  (affine_holomorphic ⟨zero,ofQComplex_valid _⟩ oneScalar).transfer identity (fun _ _ => trivial)
    ⟨fun _ _ => unitError,fun _ _ _ _ => trivial⟩
    (fun z _ => equiv_trans (add_valid (ofQComplex_valid _) (mul_valid oneScalar.property z.property))
      (mul_valid oneScalar.property z.property) z.property (zero_add_equiv _ (mul_valid oneScalar.property z.property))
      (one_mul_equiv _ z.property))

def holomorphic (k : Nat) : Holomorphic (function k) := by
  induction k with
  | zero => exact constantOn_holomorphic ScalarTopology.wholeData oneScalar
  | succ k ih =>
    exact (ih.productOn identity_holomorphic (fun _ _ => trivial)).transfer (function (k+1))
      (fun _ _ => trivial) ⟨fun _ _ => unitError,fun _ _ _ _ => trivial⟩
      (fun z _ => equiv_refl _ (power_valid z.val z.property (k+1)))

end ComputableAnalysis.RiemannHilbert.EntireMonomial
