import ComputableAnalysis.ModularForms.HorizontalLatticeRowCoordinates
import ComputableAnalysis.ModularForms.PairedDivisionQuarticPiNormalization

/-! Exact comparison of actual horizontal weight-six rows with inverse-sixth coefficient prefixes. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

private theorem pair_class (z : Scalar) (hz : InUpperHalfPlane z.val) (n : Nat) :
    ComplexRawQuotient.ofRaw (upperPointPower z hz 6 ⟨-((n+1:Nat):Int),0⟩) (upperPointPower_valid z hz 6 _)+
      ComplexRawQuotient.ofRaw (upperPointPower z hz 6 ⟨((n+1:Nat):Int),0⟩) (upperPointPower_valid z hz 6 _)=
      -ComplexRawQuotient.ofRaw (pairedCenterQuarticTerm n) (pairedCenterQuarticTerm_valid n) := by
  have hp := upperPointPower_horizontal z hz ((n+1:Nat):Int) (by omega) 6
  have hr : (((n+1:Nat):Rat)⁻¹)^6=reciprocalSquare (n+1)*(reciprocalSquare (n+1)*reciprocalSquare (n+1)) := by
    unfold reciprocalSquare
    rw [Rat.inv_mul_rev]
    grind only
  simp only [Rat.intCast_natCast] at hp
  rw [hr] at hp
  have hn := upperPointPower_even_neg z hz 3 (⟨((n+1:Nat):Int),0⟩ : QuadraticOrder163)
  have hpos := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := upperPointPower_valid z hz 6 _) (hright := ofQComplex_valid _) hp
  have hneg := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := upperPointPower_valid z hz 6 _) (hright := upperPointPower_valid z hz 6 _) hn
  have hc2 := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid (pairedCenterReciprocal n).property (pairedCenterReciprocal n).property)
    (hright := ofQComplex_valid _) (rationalRealProduct_equiv (reciprocalSquare (n+1)) (reciprocalSquare (n+1)))
  have hc3 := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid (pairedCenterReciprocal n).property (ofQComplex_valid _))
    (hright := ofQComplex_valid _) (rationalRealProduct_equiv (reciprocalSquare (n+1))
      (reciprocalSquare (n+1)*reciprocalSquare (n+1)))
  let A := ComplexRawQuotient.ofQComplex ⟨reciprocalSquare (n+1)*(reciprocalSquare (n+1)*reciprocalSquare (n+1)),0⟩
  let P := ComplexRawQuotient.ofRaw (upperPointPower z hz 6 ⟨((n+1:Nat):Int),0⟩) (upperPointPower_valid z hz 6 _)
  let M := ComplexRawQuotient.ofRaw (upperPointPower z hz 6 ⟨-((n+1:Nat):Int),0⟩) (upperPointPower_valid z hz 6 _)
  let C := ComplexRawQuotient.ofRaw (pairedCenterReciprocal n).val (pairedCenterReciprocal n).property
  change P=A at hpos
  change M=P at hneg
  change C*C=ComplexRawQuotient.ofQComplex ⟨reciprocalSquare (n+1)*reciprocalSquare (n+1),0⟩ at hc2
  change C*ComplexRawQuotient.ofQComplex ⟨reciprocalSquare (n+1)*reciprocalSquare (n+1),0⟩=A at hc3
  change M+P= -(ComplexRawQuotient.scaleRat (-2) (C*(C*C)))
  rw [hneg,hpos,hc2,hc3,ComplexRawQuotient.neg_scaleRat]
  simp only [Rat.neg_neg]
  have h := ComplexRawQuotient.add_scaleRat 1 1 A
  rw [ComplexRawQuotient.scaleRat_one,show (1:Rat)+1=2 by decide +kernel] at h
  exact h

/-- Every actual finite horizontal weight-six row is the negative quartic
coefficient prefix with the same cutoff. -/
theorem upperHorizontalWeightSix_finite_coefficient (z : Scalar) (hz : InUpperHalfPlane z.val) (N : Nat) :
    (upperLatticeFiniteRow z hz 6 N 0).val.Equiv
      (neg (ScalarSeries.block pairedCenterQuarticTerm 0 N)) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (upperLatticeFiniteRow z hz 6 N 0).property)
    (hright := neg_valid (ScalarSeries.block_valid _ pairedCenterQuarticTerm_valid 0 N))
  rw [upperLatticeFiniteRow_horizontal_class]
  change symmetricLatticeSum (fun x => ComplexRawQuotient.ofRaw (upperPointPower z hz 6 ⟨x,0⟩)
    (upperPointPower_valid z hz 6 _)) N=
    -ComplexRawQuotient.ofRaw (ScalarSeries.block pairedCenterQuarticTerm 0 N)
      (ScalarSeries.block_valid _ pairedCenterQuarticTerm_valid 0 N)
  rw [ScalarSeries.prefix_image]
  let f := fun x => ComplexRawQuotient.ofRaw (upperPointPower z hz 6 ⟨x,0⟩) (upperPointPower_valid z hz 6 _)
  let q := fun n => ComplexRawQuotient.ofRaw (pairedCenterQuarticTerm n) (pairedCenterQuarticTerm_valid n)
  change symmetricLatticeSum f N= -FiniteProducts.partialSum q N
  have hzero : f 0=0 := by
    change ComplexRawQuotient.ofRaw (upperPointPower z hz 6 QuadraticOrder163.zero) (upperPointPower_valid z hz 6 _)=0
    simp only [upperPointPower,dif_neg (show ¬QuadraticOrder163.zero≠QuadraticOrder163.zero from fun h => h rfl)]
    rfl
  induction N with
  | zero =>
    change f 0= -0
    rw [hzero]
    grind only
  | succ N ih =>
    change symmetricLatticeSum f N+f (-((N+1:Nat):Int))+f ((N+1:Nat):Int)=
      -(FiniteProducts.partialSum q N+q N)
    have hp : f (-((N+1:Nat):Int))+f ((N+1:Nat):Int)= -q N := pair_class z hz N
    rw [ih]
    generalize FiniteProducts.partialSum q N=A,q N=B,f (-((N+1:Nat):Int))=C,f ((N+1:Nat):Int)=D at hp ⊢
    grind only

end ComputableAnalysis.ModularForms
