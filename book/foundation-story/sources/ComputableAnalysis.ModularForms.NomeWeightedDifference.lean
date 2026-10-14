import ComputableAnalysis.ModularForms.PolynomialNomeMoments

/-! Finite difference telescoping for actual weighted nome powers. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

def nomeCoefficientPrefix (z : Scalar) (a : Nat → Scalar) (N : Nat) : ComplexRaw :=
  ScalarSeries.block (fun n => mul (a (n+1)).val (LocalODE.power z.val (n+1))) 0 N

theorem nomeCoefficientPrefix_valid (z : Scalar) (a : Nat → Scalar) (N : Nat) :
    (nomeCoefficientPrefix z a N).Valid :=
  ScalarSeries.block_valid _ (fun n => mul_valid (a (n+1)).property (LocalODE.power_valid _ z.property (n+1))) 0 N

def nomeCoefficientDifference (a : Nat → Scalar) (n : Nat) : Scalar :=
  ⟨sub (a n).val (a (n-1)).val,sub_valid (a n).property (a (n-1)).property⟩

theorem nomeCoefficientPrefix_difference_identity (z : Scalar) (a : Nat → Scalar) (N : Nat) :
    (mul (sub (ofQComplex QComplex.one) z.val) (nomeCoefficientPrefix z a N)).Equiv
      (add (sub (nomeCoefficientPrefix z (nomeCoefficientDifference a) N)
        (mul (a N).val (LocalODE.power z.val (N+1)))) (mul (a 0).val z.val)) := by
  let Z := ComplexRawQuotient.ofRaw z.val z.property
  let A := fun n => ComplexRawQuotient.ofRaw (a n).val (a n).property
  let P := fun n => ComplexRawQuotient.ofRaw (nomeCoefficientPrefix z a n) (nomeCoefficientPrefix_valid z a n)
  let D := fun n => ComplexRawQuotient.ofRaw (nomeCoefficientPrefix z (nomeCoefficientDifference a) n)
    (nomeCoefficientPrefix_valid z (nomeCoefficientDifference a) n)
  have h (n : Nat) : (1-Z)*P n=D n-A n*Z^(n+1)+A 0*Z := by
    induction n with
    | zero => change (1-Z)*0=0-A 0*Z^1+A 0*Z; grind only
    | succ n ih =>
      have hp : P (n+1)=P n+A (n+1)*Z^(n+1) := by
        simp only [P,nomeCoefficientPrefix,ScalarSeries.block.eq_2,Nat.zero_add]
        change P n+A (n+1)*ComplexRawQuotient.ofRaw (LocalODE.power z.val (n+1))
          (LocalODE.power_valid _ z.property (n+1))=P n+A (n+1)*Z^(n+1)
        rw [ScalarAlgebra.ofRaw_power _ z.property]
      have hd : D (n+1)=D n+(A (n+1)-A n)*Z^(n+1) := by
        simp only [D,nomeCoefficientPrefix,ScalarSeries.block.eq_2,Nat.zero_add,nomeCoefficientDifference,Nat.add_sub_cancel]
        change D n+(A (n+1)-A n)*ComplexRawQuotient.ofRaw (LocalODE.power z.val (n+1))
          (LocalODE.power_valid _ z.property (n+1))=D n+(A (n+1)-A n)*Z^(n+1)
        rw [ScalarAlgebra.ofRaw_power _ z.property]
      rw [hp,hd]
      grind only
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := mul_valid (sub_valid (ofQComplex_valid _) z.property) (nomeCoefficientPrefix_valid z a N))
    (hright := add_valid (sub_valid (nomeCoefficientPrefix_valid z (nomeCoefficientDifference a) N)
      (mul_valid (a N).property (LocalODE.power_valid _ z.property (N+1))))
      (mul_valid (a 0).property z.property))
  change (1-Z)*P N=D N-A N*ComplexRawQuotient.ofRaw (LocalODE.power z.val (N+1))
    (LocalODE.power_valid _ z.property (N+1))+A 0*Z
  rw [ScalarAlgebra.ofRaw_power _ z.property]
  exact h N

def polynomialNomeCoefficient (k n : Nat) : Scalar :=
  ⟨scaleRat ((n:Rat)^k) (ofQComplex QComplex.one),scaleRat_valid (ofQComplex_valid _)⟩

theorem polynomialNomeMomentPrefix_coefficient_agreement (z : Scalar) (k N : Nat) :
    (polynomialNomeMomentPrefix z k N).Equiv
      (nomeCoefficientPrefix z (polynomialNomeCoefficient k) N) := by
  apply ScalarSeries.block_congr
  intro n
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := polynomialNomeMomentTerm_valid z k n)
    (hright := mul_valid (polynomialNomeCoefficient k (n+1)).property
      (LocalODE.power_valid _ z.property (n+1)))
  let Q := ComplexRawQuotient.ofRaw (LocalODE.power z.val (n+1)) (LocalODE.power_valid _ z.property (n+1))
  change ComplexRawQuotient.scaleRat (((n+1:Nat):Rat)^k) Q=
    ComplexRawQuotient.scaleRat (((n+1:Nat):Rat)^k) 1*Q
  rw [←ComplexRawQuotient.scaleRat_mul]
  have ho : (1:ComplexRawQuotient.Value)*Q=Q := by grind only
  rw [ho]

end ComputableAnalysis.ModularForms
