import ComputableAnalysis.RiemannHilbert.ScalarPolynomial
import ComputableAnalysis.RepresentedPolynomial

/-! The existing finite monomial evaluator agrees exactly with literal Horner
arithmetic, for arbitrary valid represented coefficients and inputs. -/
namespace ComputableAnalysis.RiemannHilbert.ScalarPolynomialHorner
open ComplexRaw FunctionTheory DomainFunctions RectangularContour ScalarPolynomial
set_option autoImplicit false

def certificate (z : Scalar) : ComplexCert := ⟨z.val,z.property⟩
def coefficients (P : Polynomial) : RepresentedPolynomial.Coefficients := P.map certificate
def horner (P : Polynomial) (z : Scalar) : Scalar :=
  ⟨(RepresentedPolynomial.eval (coefficients P) (certificate z)).raw,
    (RepresentedPolynomial.eval (coefficients P) (certificate z)).valid⟩

theorem horner_compute (P : Polynomial) (z : Scalar) (n : Nat) :
    (horner P z).val.compute n =
      RepresentedPolynomial.evalBox (P.map (fun a => a.val.compute n)) (z.val.compute n) := by
  simpa [horner,coefficients,List.map_map,certificate] using
    RepresentedPolynomial.eval_compute (coefficients P) (certificate z) n

theorem monomial_value (z : Scalar) (k : Nat) :
    gridScalarValue (BalancedMonomial.scalar z k)=(gridScalarValue z)^k :=
  (ComplexRawQuotient.ofRaw_eq_ofRaw (BalancedMonomial.scalar_agrees z k)).trans
    (ScalarAlgebra.ofRaw_power z.val z.property k)

theorem sum_split (f : Nat → ScalarAlgebra.Value) (N : Nat) :
    gridValueSum (N+1) f=f 0+gridValueSum N (fun k => f (k+1)) := by
  induction N with
  | zero => simp only [gridValueSum]; grind only
  | succ N ih =>
    change gridValueSum (N+1) f+f (N+1)=
      f 0+(gridValueSum N (fun k => f (k+1))+f (N+1))
    rw [ih]
    grind only

theorem sum_mul (a : ScalarAlgebra.Value) (f : Nat → ScalarAlgebra.Value) (N : Nat) :
    gridValueSum N (fun k => a*f k)=a*gridValueSum N f := by
  induction N with
  | zero => simp only [gridValueSum]; grind only
  | succ N ih => simp only [gridValueSum,ih]; grind only

theorem value_cons (a : Scalar) (P : Polynomial) (z : Scalar) :
    value (a::P) z≈scalarSum a (scalarProduct z (value P z)) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (value (a::P) z).property)
    (hright := (scalarSum a (scalarProduct z (value P z))).property)
  change gridScalarValue (value (a::P) z)=
    gridScalarValue a+gridScalarValue z*gridScalarValue (value P z)
  simp only [value,finiteSum,gridScalarSum_value,List.length_cons]
  have term (Q : Polynomial) (k : Nat) :
      gridScalarValue (scalarProduct (BalancedMonomial.scalar z k) (coefficient Q k))=
        (gridScalarValue z)^k*gridScalarValue (coefficient Q k) := by
    change gridScalarValue (BalancedMonomial.scalar z k)*gridScalarValue (coefficient Q k)=_
    rw [monomial_value]
  simp only [term]
  rw [sum_split]
  have head : coefficient (a::P) 0=a := by simp [coefficient]
  have tail (k : Nat) : coefficient (a::P) (k+1)=coefficient P k := by
    simp [coefficient]
  simp only [head,tail]
  have power_term (k : Nat) :
      (gridScalarValue z)^(k+1)*gridScalarValue (coefficient P k)=
        gridScalarValue z*((gridScalarValue z)^k*gridScalarValue (coefficient P k)) := by
    change ((gridScalarValue z)^k*gridScalarValue z)*_= _
    grind only
  simp only [power_term]
  rw [sum_mul]
  change (1 : ScalarAlgebra.Value)*gridScalarValue a+_= _
  grind only

theorem horner_agrees (P : Polynomial) (z : Scalar) : horner P z≈value P z := by
  induction P with
  | nil => exact Setoid.refl _
  | cons a P ih =>
    exact Setoid.trans (add_equiv (Setoid.refl a)
      (mul_equiv z.property z.property (horner P z).property (value P z).property
        (Setoid.refl z) ih)) (Setoid.symm (value_cons a P z))

theorem horner_names (P Q : Polynomial) (hl : P.length=Q.length)
    (hc : ∀ k, k<P.length → coefficient P k≈coefficient Q k)
    (z w : Scalar) (he : z≈w) : horner P z≈horner Q w :=
  Setoid.trans (horner_agrees P z)
    (Setoid.trans (value_names P Q hl hc z w he) (Setoid.symm (horner_agrees Q w)))

end ComputableAnalysis.RiemannHilbert.ScalarPolynomialHorner
