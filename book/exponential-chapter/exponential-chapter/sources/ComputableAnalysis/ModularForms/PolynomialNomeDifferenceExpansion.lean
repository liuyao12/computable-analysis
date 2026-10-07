import ComputableAnalysis.ModularForms.PolynomialNomeDifferenceSeries

/-! Checked low-degree backward differences and their actual represented term expansions. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

private theorem quotient_sub_scale (c d : Rat) (v : ComplexRawQuotient.Value) :
    ComplexRawQuotient.scaleRat c v-ComplexRawQuotient.scaleRat d v=
      ComplexRawQuotient.scaleRat (c-d) v := by
  change ComplexRawQuotient.scaleRat c v+ -ComplexRawQuotient.scaleRat d v=_
  rw [ComplexRawQuotient.neg_scaleRat,ComplexRawQuotient.add_scaleRat]
  congr 1
  grind only

theorem polynomialNomeDifferenceWeight_degree_2 (n : Nat) :
    polynomialNomeDifferenceWeight 2 n=((2*(((n+1:Nat):Rat)^1))-(((n+1:Nat):Rat)^0)) := by
  unfold polynomialNomeDifferenceWeight
  simp only [Rat.pow_succ,Rat.pow_zero,Rat.natCast_add]
  grind only

theorem polynomialNomeDifferenceTerm_degree_2 (z : Scalar) (n : Nat) :
    (polynomialNomeDifferenceTerm z 2 n).Equiv (sub (scaleRat 2 (polynomialNomeMomentTerm z 1 n)) (polynomialNomeMomentTerm z 0 n)) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := polynomialNomeDifferenceTerm_valid z 2 n)
    (hright := (sub_valid (scaleRat_valid (polynomialNomeMomentTerm_valid z 1 n)) (polynomialNomeMomentTerm_valid z 0 n)))
  let Q := ComplexRawQuotient.ofRaw (LocalODE.power z.val (n+1)) (LocalODE.power_valid _ z.property (n+1))
  change ComplexRawQuotient.scaleRat (polynomialNomeDifferenceWeight 2 n) Q=((ComplexRawQuotient.scaleRat 2 (ComplexRawQuotient.scaleRat (((n+1:Nat):Rat)^1) Q))-(ComplexRawQuotient.scaleRat (((n+1:Nat):Rat)^0) Q))
  simp only [ComplexRawQuotient.scaleRat_scaleRat,ComplexRawQuotient.add_scaleRat,quotient_sub_scale]
  rw [polynomialNomeDifferenceWeight_degree_2]

theorem polynomialNomeDifferenceWeight_degree_3 (n : Nat) :
    polynomialNomeDifferenceWeight 3 n=(((3*(((n+1:Nat):Rat)^2))-(3*(((n+1:Nat):Rat)^1)))+(((n+1:Nat):Rat)^0)) := by
  unfold polynomialNomeDifferenceWeight
  simp only [Rat.pow_succ,Rat.pow_zero,Rat.natCast_add]
  grind only

theorem polynomialNomeDifferenceTerm_degree_3 (z : Scalar) (n : Nat) :
    (polynomialNomeDifferenceTerm z 3 n).Equiv (add (sub (scaleRat 3 (polynomialNomeMomentTerm z 2 n)) (scaleRat 3 (polynomialNomeMomentTerm z 1 n))) (polynomialNomeMomentTerm z 0 n)) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := polynomialNomeDifferenceTerm_valid z 3 n)
    (hright := (add_valid (sub_valid (scaleRat_valid (polynomialNomeMomentTerm_valid z 2 n)) (scaleRat_valid (polynomialNomeMomentTerm_valid z 1 n))) (polynomialNomeMomentTerm_valid z 0 n)))
  let Q := ComplexRawQuotient.ofRaw (LocalODE.power z.val (n+1)) (LocalODE.power_valid _ z.property (n+1))
  change ComplexRawQuotient.scaleRat (polynomialNomeDifferenceWeight 3 n) Q=(((ComplexRawQuotient.scaleRat 3 (ComplexRawQuotient.scaleRat (((n+1:Nat):Rat)^2) Q))-(ComplexRawQuotient.scaleRat 3 (ComplexRawQuotient.scaleRat (((n+1:Nat):Rat)^1) Q)))+(ComplexRawQuotient.scaleRat (((n+1:Nat):Rat)^0) Q))
  simp only [ComplexRawQuotient.scaleRat_scaleRat,ComplexRawQuotient.add_scaleRat,quotient_sub_scale]
  rw [polynomialNomeDifferenceWeight_degree_3]

theorem polynomialNomeDifferenceWeight_degree_4 (n : Nat) :
    polynomialNomeDifferenceWeight 4 n=((((4*(((n+1:Nat):Rat)^3))-(6*(((n+1:Nat):Rat)^2)))+(4*(((n+1:Nat):Rat)^1)))-(((n+1:Nat):Rat)^0)) := by
  unfold polynomialNomeDifferenceWeight
  simp only [Rat.pow_succ,Rat.pow_zero,Rat.natCast_add]
  grind only

theorem polynomialNomeDifferenceTerm_degree_4 (z : Scalar) (n : Nat) :
    (polynomialNomeDifferenceTerm z 4 n).Equiv (sub (add (sub (scaleRat 4 (polynomialNomeMomentTerm z 3 n)) (scaleRat 6 (polynomialNomeMomentTerm z 2 n))) (scaleRat 4 (polynomialNomeMomentTerm z 1 n))) (polynomialNomeMomentTerm z 0 n)) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := polynomialNomeDifferenceTerm_valid z 4 n)
    (hright := (sub_valid (add_valid (sub_valid (scaleRat_valid (polynomialNomeMomentTerm_valid z 3 n)) (scaleRat_valid (polynomialNomeMomentTerm_valid z 2 n))) (scaleRat_valid (polynomialNomeMomentTerm_valid z 1 n))) (polynomialNomeMomentTerm_valid z 0 n)))
  let Q := ComplexRawQuotient.ofRaw (LocalODE.power z.val (n+1)) (LocalODE.power_valid _ z.property (n+1))
  change ComplexRawQuotient.scaleRat (polynomialNomeDifferenceWeight 4 n) Q=((((ComplexRawQuotient.scaleRat 4 (ComplexRawQuotient.scaleRat (((n+1:Nat):Rat)^3) Q))-(ComplexRawQuotient.scaleRat 6 (ComplexRawQuotient.scaleRat (((n+1:Nat):Rat)^2) Q)))+(ComplexRawQuotient.scaleRat 4 (ComplexRawQuotient.scaleRat (((n+1:Nat):Rat)^1) Q)))-(ComplexRawQuotient.scaleRat (((n+1:Nat):Rat)^0) Q))
  simp only [ComplexRawQuotient.scaleRat_scaleRat,ComplexRawQuotient.add_scaleRat,quotient_sub_scale]
  rw [polynomialNomeDifferenceWeight_degree_4]

theorem polynomialNomeDifferenceWeight_degree_5 (n : Nat) :
    polynomialNomeDifferenceWeight 5 n=(((((5*(((n+1:Nat):Rat)^4))-(10*(((n+1:Nat):Rat)^3)))+(10*(((n+1:Nat):Rat)^2)))-(5*(((n+1:Nat):Rat)^1)))+(((n+1:Nat):Rat)^0)) := by
  unfold polynomialNomeDifferenceWeight
  simp only [Rat.pow_succ,Rat.pow_zero,Rat.natCast_add]
  grind only

theorem polynomialNomeDifferenceTerm_degree_5 (z : Scalar) (n : Nat) :
    (polynomialNomeDifferenceTerm z 5 n).Equiv (add (sub (add (sub (scaleRat 5 (polynomialNomeMomentTerm z 4 n)) (scaleRat 10 (polynomialNomeMomentTerm z 3 n))) (scaleRat 10 (polynomialNomeMomentTerm z 2 n))) (scaleRat 5 (polynomialNomeMomentTerm z 1 n))) (polynomialNomeMomentTerm z 0 n)) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := polynomialNomeDifferenceTerm_valid z 5 n)
    (hright := (add_valid (sub_valid (add_valid (sub_valid (scaleRat_valid (polynomialNomeMomentTerm_valid z 4 n)) (scaleRat_valid (polynomialNomeMomentTerm_valid z 3 n))) (scaleRat_valid (polynomialNomeMomentTerm_valid z 2 n))) (scaleRat_valid (polynomialNomeMomentTerm_valid z 1 n))) (polynomialNomeMomentTerm_valid z 0 n)))
  let Q := ComplexRawQuotient.ofRaw (LocalODE.power z.val (n+1)) (LocalODE.power_valid _ z.property (n+1))
  change ComplexRawQuotient.scaleRat (polynomialNomeDifferenceWeight 5 n) Q=(((((ComplexRawQuotient.scaleRat 5 (ComplexRawQuotient.scaleRat (((n+1:Nat):Rat)^4) Q))-(ComplexRawQuotient.scaleRat 10 (ComplexRawQuotient.scaleRat (((n+1:Nat):Rat)^3) Q)))+(ComplexRawQuotient.scaleRat 10 (ComplexRawQuotient.scaleRat (((n+1:Nat):Rat)^2) Q)))-(ComplexRawQuotient.scaleRat 5 (ComplexRawQuotient.scaleRat (((n+1:Nat):Rat)^1) Q)))+(ComplexRawQuotient.scaleRat (((n+1:Nat):Rat)^0) Q))
  simp only [ComplexRawQuotient.scaleRat_scaleRat,ComplexRawQuotient.add_scaleRat,quotient_sub_scale]
  rw [polynomialNomeDifferenceWeight_degree_5]

end ComputableAnalysis.ModularForms
