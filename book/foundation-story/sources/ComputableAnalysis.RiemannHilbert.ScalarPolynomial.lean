import ComputableAnalysis.RiemannHilbert.ContourTaylorRemainder
import ComputableAnalysis.RiemannHilbert.BalancedMonomialAlgebra
import ComputableAnalysis.RiemannHilbert.DomainHolomorphicSums

/-! Finite polynomials with arbitrary represented complex coefficients.
The literal finite list evaluator is entire, respects input and coefficient
names, and agrees with its finite monomial sum. No completed scalar occurs. -/
namespace ComputableAnalysis.RiemannHilbert.ScalarPolynomial
open ComplexRaw FunctionTheory DomainFunctions RectangularContour
set_option autoImplicit false

abbrev Polynomial := List Scalar
def zeroScalar : Scalar := ⟨zero,ofQComplex_valid _⟩
def coefficient (P : Polynomial) (k : Nat) : Scalar := P[k]?.getD zeroScalar
def finiteSum (c : Nat → Scalar) (N : Nat) (z : Scalar) : Scalar :=
  gridScalarSum N (fun k => scalarProduct (BalancedMonomial.scalar z k) (c k))
def value (P : Polynomial) (z : Scalar) : Scalar := finiteSum (coefficient P) P.length z
def ofCoefficients (N : Nat) (c : Nat → Scalar) : Polynomial := List.ofFn (fun i : Fin N => c i.val)

theorem ofCoefficients_length (N : Nat) (c : Nat → Scalar) : (ofCoefficients N c).length=N := List.length_ofFn

theorem ofCoefficients_coefficient (N : Nat) (c : Nat → Scalar) (k : Nat) (hk : k<N) :
    coefficient (ofCoefficients N c) k=c k := by
  simp only [coefficient,ofCoefficients,List.getElem?_ofFn,dif_pos hk,Option.getD_some]

theorem ofCoefficients_value (N : Nat) (c : Nat → Scalar) (z : Scalar) :
    value (ofCoefficients N c) z≈finiteSum c N z := by
  unfold value
  rw [ofCoefficients_length]
  apply gridScalarSum_congr_bounded N
  intro k hk
  rw [ofCoefficients_coefficient N c k hk]
  exact equiv_refl _ (scalarProduct (BalancedMonomial.scalar z k) (c k)).property

theorem prefix_names (c d : Nat → Scalar) (N : Nat) (hc : ∀ k, k<N → c k≈d k)
    (z w : Scalar) (he : z≈w) : finiteSum c N z≈finiteSum d N w :=
  gridScalarSum_congr_bounded N _ _ (fun k hk =>
    mul_equiv (BalancedMonomial.scalar z k).property (BalancedMonomial.scalar w k).property
      (c k).property (d k).property (BalancedMonomial.scalar_names z w he k) (hc k hk))

theorem value_names (P Q : Polynomial) (hl : P.length=Q.length)
    (hc : ∀ k, k<P.length → coefficient P k≈coefficient Q k)
    (z w : Scalar) (he : z≈w) : value P z≈value Q w := by
  unfold value
  rw [←hl]
  exact prefix_names _ _ _ hc z w he

def prefixFunction (c : Nat → Scalar) (N : Nat) : DomainFunctions.Map where
  domain _ := True
  eval z _ := finiteSum c N z
  domain_congr _ _ _ := Iff.rfl
  eval_congr z w _ _ he := prefix_names c c N (fun _ _ => Setoid.refl _) z w he

def prefix_holomorphic (c : Nat → Scalar) (N : Nat) : Holomorphic (prefixFunction c N) := by
  induction N with
  | zero => exact constantOn_holomorphic ScalarTopology.wholeData zeroScalar
  | succ N ih =>
    let mono := (EntireMonomial.holomorphic N).transfer
      ({domain := fun _ => True,eval := fun z _ => BalancedMonomial.scalar z N,
        domain_congr := fun _ _ _ => Iff.rfl,eval_congr := fun z w _ _ he => BalancedMonomial.scalar_names z w he N} : DomainFunctions.Map)
      (fun _ _ => trivial) ⟨fun _ _ => unitError,fun _ _ _ _ => trivial⟩
      (fun z _ => equiv_symm (BalancedMonomial.scalar_agrees z N))
    let term := mono.productOn (constantOn_holomorphic ScalarTopology.wholeData (c N)) (fun _ _ => trivial)
    exact (ih.sumOn term (fun _ _ => trivial)).transfer (prefixFunction c (N+1))
      (fun _ _ => trivial) ⟨fun _ _ => unitError,fun _ _ _ _ => trivial⟩
      (fun z _ => equiv_refl _ (finiteSum c (N+1) z).property)

def function (P : Polynomial) : DomainFunctions.Map := prefixFunction (coefficient P) P.length
def holomorphic (P : Polynomial) : Holomorphic (function P) := prefix_holomorphic (coefficient P) P.length

end ComputableAnalysis.RiemannHilbert.ScalarPolynomial
