import ComputableAnalysis.RiemannHilbert.BalancedMonomial
import ComputableAnalysis.RiemannHilbert.RepresentedReciprocal

/-! Exact finite algebra for the executable balanced powers. Reciprocal
powers are constructed from the represented reciprocal; all cancellation
and name comparison results concern actual valid represented values. -/
namespace ComputableAnalysis.RiemannHilbert.BalancedMonomial
open ComplexRaw FunctionTheory LocalODE DomainFunctions NonzeroBoxSearch
set_option autoImplicit false

private theorem image (z : Scalar) (k : Nat) :
    ComplexRawQuotient.ofRaw (scalar z k).val (scalar z k).property =
      (ComplexRawQuotient.ofRaw z.val z.property)^k :=
  (ComplexRawQuotient.ofRaw_eq_ofRaw (scalar_agrees z k)).trans
    (ScalarAlgebra.ofRaw_power z.val z.property k)

private theorem power_add (x : ScalarAlgebra.Value) (p q : Nat) :
    x^(p+q)=x^p*x^q := by
  induction q with
  | zero => exact (ComplexRawQuotient.mul_one _).symm
  | succ q ih => change x^(p+q)*x=x^p*(x^q*x); rw [ih,ComplexRawQuotient.mul_assoc]

private theorem power_product (x y : ScalarAlgebra.Value) (k : Nat) :
    (x*y)^k=x^k*y^k := by
  induction k with
  | zero => exact (ComplexRawQuotient.one_mul _).symm
  | succ k ih => change (x*y)^k*(x*y)=(x^k*x)*(y^k*y); rw [ih]; grind only

private theorem power_one (k : Nat) : (1 : ScalarAlgebra.Value)^k=1 := by
  induction k with
  | zero => rfl
  | succ k ih => change (1 : ScalarAlgebra.Value)^k*1=1; rw [ih]; grind only

theorem scalar_add (z : Scalar) (p q : Nat) :
    scalarProduct (scalar z p) (scalar z q)≈scalar z (p+q) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (scalarProduct (scalar z p) (scalar z q)).property)
    (hright := (scalar z (p+q)).property)
  change ComplexRawQuotient.ofRaw (scalar z p).val (scalar z p).property *
    ComplexRawQuotient.ofRaw (scalar z q).val (scalar z q).property = _
  rw [image,image,image,power_add]

theorem scalar_one (z : Scalar) : scalar z 1≈z :=
  equiv_trans (scalar z 1).property (EntireMonomial.scalar z 1).property z.property
    (scalar_agrees z 1) (one_mul_equiv _ z.property)

theorem scalar_zero_name (z : Scalar) (hz : z.val.Equiv zero) (k : Nat) (hk : 0<k) :
    (scalar z k).val.Equiv zero := by
  cases k with
  | zero => omega
  | succ k =>
      exact equiv_trans (scalar z (k+1)).property
        (scalar ⟨zero,ofQComplex_valid _⟩ (k+1)).property (ofQComplex_valid _)
        (scalar_names z ⟨zero,ofQComplex_valid _⟩ hz (k+1)) (scalar_zero_succ k)

def inversePower (z : Scalar) (hz : Nonzero z) (k : Nat) : Scalar :=
  scalar (RepresentedReciprocal.inverse z hz) k

theorem inversePower_names (z w : Scalar) (hz : Nonzero z) (hw : Nonzero w)
    (he : z≈w) (k : Nat) : inversePower z hz k≈inversePower w hw k :=
  scalar_names _ _ (RepresentedReciprocal.inverse_congr z w hz hw he) k

theorem power_inverse (z : Scalar) (hz : Nonzero z) (k : Nat) :
    scalarProduct (scalar z k) (inversePower z hz k)≈oneScalar := by
  have hi := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid z.property (RepresentedReciprocal.inverse z hz).property)
    (hright := oneScalar.property) (RepresentedReciprocal.mul_inverse z hz)
  change ComplexRawQuotient.ofRaw z.val z.property *
    ComplexRawQuotient.ofRaw (RepresentedReciprocal.inverse z hz).val
      (RepresentedReciprocal.inverse z hz).property = (1 : ScalarAlgebra.Value) at hi
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (scalarProduct (scalar z k) (inversePower z hz k)).property)
    (hright := oneScalar.property)
  change ComplexRawQuotient.ofRaw (scalar z k).val (scalar z k).property *
    ComplexRawQuotient.ofRaw (scalar (RepresentedReciprocal.inverse z hz) k).val
      (scalar (RepresentedReciprocal.inverse z hz) k).property = 1
  rw [image,image,← power_product,hi,power_one]

theorem scalar_nonzero (z : Scalar) (hz : Nonzero z) (k : Nat) : Nonzero (scalar z k) :=
  RepresentedReciprocal.nonzero_of_inverse (scalar z k) (inversePower z hz k) (power_inverse z hz k)

theorem inversePower_reciprocal (z : Scalar) (hz : Nonzero z) (k : Nat) :
    inversePower z hz k≈RepresentedReciprocal.inverse (scalar z k) (scalar_nonzero z hz k) :=
  equiv_symm (RepresentedReciprocal.inverse_unique (scalar z k) (scalar_nonzero z hz k)
    (inversePower z hz k) (power_inverse z hz k))

theorem inversePower_add (z : Scalar) (hz : Nonzero z) (p q : Nat) :
    scalarProduct (inversePower z hz p) (inversePower z hz q)≈inversePower z hz (p+q) :=
  scalar_add (RepresentedReciprocal.inverse z hz) p q

theorem clear_cancel (z : Scalar) (hz : Nonzero z) (k : Nat) (v : Scalar) :
    scalarProduct (inversePower z hz k) (scalarProduct (scalar z k) v)≈v := by
  have hi := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := (scalarProduct (scalar z k) (inversePower z hz k)).property)
    (hright := oneScalar.property) (power_inverse z hz k)
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (scalarProduct (inversePower z hz k) (scalarProduct (scalar z k) v)).property)
    (hright := v.property)
  let P := ComplexRawQuotient.ofRaw (scalar z k).val (scalar z k).property
  let R := ComplexRawQuotient.ofRaw (inversePower z hz k).val (inversePower z hz k).property
  let V := ComplexRawQuotient.ofRaw v.val v.property
  change P*R=1 at hi
  change R*(P*V)=V
  grind only

end ComputableAnalysis.RiemannHilbert.BalancedMonomial
