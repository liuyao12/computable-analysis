import ComputableAnalysis.RiemannHilbert.EntireMonomial
import ComputableAnalysis.RiemannHilbert.ScalarAlgebra

/-! A balanced executable monomial expression. Its exact agreement with the
previous monomial transfers validity, name invariance and holomorphicity;
the recursion has logarithmic expression depth for every natural exponent. -/
namespace ComputableAnalysis.RiemannHilbert.BalancedMonomial
open ComplexRaw FunctionTheory LocalODE DomainFunctions
set_option autoImplicit false

def scalar (z : Scalar) (k : Nat) : Scalar :=
  if hk : k=0 then oneScalar else
    let b := scalar z (k/2)
    let square := scalarProduct b b
    if k%2=0 then square else scalarProduct square z
termination_by k
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero hk) (by decide +kernel)

private theorem power_add (z : ScalarAlgebra.Value) (j k : Nat) : z^(j+k)=z^j*z^k := by
  induction k with
  | zero => change z^j=z^j*1; exact (ComplexRawQuotient.mul_one _).symm
  | succ k ih =>
    change z^(j+k)*z=z^j*(z^k*z)
    rw [ih,ComplexRawQuotient.mul_assoc]

private theorem scalar_image (z : Scalar) (k : Nat) :
    ComplexRawQuotient.ofRaw (scalar z k).val (scalar z k).property=
      (ComplexRawQuotient.ofRaw z.val z.property)^k := by
  induction k using Nat.strongRecOn with
  | ind k ih =>
    rw [scalar]
    by_cases hk : k=0
    · subst k
      rw [dif_pos rfl]
      rfl
    · rw [dif_neg hk]
      have hb := ih (k/2) (Nat.div_lt_self (Nat.pos_of_ne_zero hk) (by decide +kernel))
      by_cases he : k%2=0
      · rw [if_pos he]
        change ComplexRawQuotient.ofRaw (scalar z (k/2)).val (scalar z (k/2)).property*
          ComplexRawQuotient.ofRaw (scalar z (k/2)).val (scalar z (k/2)).property=_
        rw [hb,← power_add]
        congr 1
        omega
      · rw [if_neg he]
        change (ComplexRawQuotient.ofRaw (scalar z (k/2)).val (scalar z (k/2)).property*
          ComplexRawQuotient.ofRaw (scalar z (k/2)).val (scalar z (k/2)).property)*
          ComplexRawQuotient.ofRaw z.val z.property=_
        rw [hb,← power_add]
        change (ComplexRawQuotient.ofRaw z.val z.property)^((k/2+k/2)+1)=_
        congr 1
        omega

theorem scalar_agrees (z : Scalar) (k : Nat) : scalar z k≈EntireMonomial.scalar z k := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq (hleft := (scalar z k).property)
    (hright := (EntireMonomial.scalar z k).property)
  exact Eq.trans (scalar_image z k) (ScalarAlgebra.ofRaw_power z.val z.property k).symm

theorem scalar_names (z w : Scalar) (he : z≈w) (k : Nat) : scalar z k≈scalar w k :=
  equiv_trans (scalar z k).property (EntireMonomial.scalar z k).property (scalar w k).property
    (scalar_agrees z k) (equiv_trans (EntireMonomial.scalar z k).property
      (EntireMonomial.scalar w k).property (scalar w k).property
      (EntireMonomial.scalar_names z w he k) (equiv_symm (scalar_agrees w k)))

theorem scalar_succ (z : Scalar) (k : Nat) :
    scalarProduct (scalar z k) z≈scalar z (k+1) :=
  equiv_trans (scalarProduct (scalar z k) z).property
    (EntireMonomial.scalar z (k+1)).property (scalar z (k+1)).property
    (mul_equiv (scalar z k).property (EntireMonomial.scalar z k).property z.property z.property
      (scalar_agrees z k) (equiv_refl _ z.property)) (equiv_symm (scalar_agrees z (k+1)))

theorem scalar_zero_succ (k : Nat) :
    (scalar ⟨zero,ofQComplex_valid _⟩ (k+1)).val.Equiv zero :=
  equiv_trans (scalar ⟨zero,ofQComplex_valid _⟩ (k+1)).property
    (power_valid zero (ofQComplex_valid _) (k+1)) (ofQComplex_valid _)
    (scalar_agrees _ (k+1)) (power_zero_succ k)

def function (k : Nat) : DomainFunctions.Map where
  domain _ := True
  eval z _ := scalar z k
  domain_congr _ _ _ := Iff.rfl
  eval_congr z w _ _ he := scalar_names z w he k

def holomorphic (k : Nat) : Holomorphic (function k) :=
  (EntireMonomial.holomorphic k).transfer (function k) (fun _ _ => trivial)
    ⟨fun _ _ => unitError,fun _ _ _ _ => trivial⟩ (fun z _ => equiv_symm (scalar_agrees z k))

end ComputableAnalysis.RiemannHilbert.BalancedMonomial
