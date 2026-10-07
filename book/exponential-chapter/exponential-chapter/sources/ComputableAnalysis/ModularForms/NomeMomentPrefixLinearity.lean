import ComputableAnalysis.ModularForms.PolynomialNomeDifferenceExpansion

/-! Exact finite-prefix linearity beneath polynomial nome difference reductions. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

theorem representedBlock_sub (t u : Nat → ComplexRaw)
    (ht : ∀ n, (t n).Valid) (hu : ∀ n, (u n).Valid) (M N : Nat) :
    (ScalarSeries.block (fun n => sub (t n) (u n)) M N).Equiv
      (sub (ScalarSeries.block t M N) (ScalarSeries.block u M N)) := by
  induction N with
  | zero =>
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := ScalarSeries.block_valid _ (fun n => sub_valid (ht n) (hu n)) M 0)
      (hright := sub_valid (ScalarSeries.block_valid t ht M 0) (ScalarSeries.block_valid u hu M 0))
    change (0:ComplexRawQuotient.Value)=0-0
    grind only
  | succ N ih =>
    have h := ComplexRawQuotient.ofRaw_eq_ofRaw
      (hleft := ScalarSeries.block_valid _ (fun n => sub_valid (ht n) (hu n)) M N)
      (hright := sub_valid (ScalarSeries.block_valid t ht M N) (ScalarSeries.block_valid u hu M N)) ih
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := ScalarSeries.block_valid _ (fun n => sub_valid (ht n) (hu n)) M (N+1))
      (hright := sub_valid (ScalarSeries.block_valid t ht M (N+1)) (ScalarSeries.block_valid u hu M (N+1)))
    simp only [ScalarSeries.block.eq_2]
    let S := ComplexRawQuotient.ofRaw (ScalarSeries.block (fun n => sub (t n) (u n)) M N)
      (ScalarSeries.block_valid _ (fun n => sub_valid (ht n) (hu n)) M N)
    let T := ComplexRawQuotient.ofRaw (ScalarSeries.block t M N) (ScalarSeries.block_valid t ht M N)
    let U := ComplexRawQuotient.ofRaw (ScalarSeries.block u M N) (ScalarSeries.block_valid u hu M N)
    let A := ComplexRawQuotient.ofRaw (t (M+N)) (ht (M+N))
    let B := ComplexRawQuotient.ofRaw (u (M+N)) (hu (M+N))
    change S=T-U at h
    change S+(A-B)=(T+A)-(U+B)
    generalize S=s,T=t,U=u,A=a,B=b at h ⊢
    grind only

theorem representedBlock_scale (t : Nat → ComplexRaw) (ht : ∀ n, (t n).Valid)
    (c : Rat) (M N : Nat) :
    (ScalarSeries.block (fun n => scaleRat c (t n)) M N).Equiv
      (scaleRat c (ScalarSeries.block t M N)) := by
  induction N with
  | zero =>
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := ScalarSeries.block_valid _ (fun n => scaleRat_valid (ht n)) M 0)
      (hright := scaleRat_valid (ScalarSeries.block_valid t ht M 0))
    change (0:ComplexRawQuotient.Value)=ComplexRawQuotient.scaleRat c 0
    exact (ComplexRawQuotient.scaleRat_zero c).symm
  | succ N ih =>
    have h := ComplexRawQuotient.ofRaw_eq_ofRaw
      (hleft := ScalarSeries.block_valid _ (fun n => scaleRat_valid (ht n)) M N)
      (hright := scaleRat_valid (ScalarSeries.block_valid t ht M N)) ih
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := ScalarSeries.block_valid _ (fun n => scaleRat_valid (ht n)) M (N+1))
      (hright := scaleRat_valid (ScalarSeries.block_valid t ht M (N+1)))
    simp only [ScalarSeries.block.eq_2]
    let S := ComplexRawQuotient.ofRaw (ScalarSeries.block (fun n => scaleRat c (t n)) M N)
      (ScalarSeries.block_valid _ (fun n => scaleRat_valid (ht n)) M N)
    let T := ComplexRawQuotient.ofRaw (ScalarSeries.block t M N) (ScalarSeries.block_valid t ht M N)
    let A := ComplexRawQuotient.ofRaw (t (M+N)) (ht (M+N))
    change S=ComplexRawQuotient.scaleRat c T at h
    change S+ComplexRawQuotient.scaleRat c A=ComplexRawQuotient.scaleRat c (T+A)
    rw [h,ComplexRawQuotient.scaleRat_add]

theorem polynomialNomeDifferencePrefix_degree_two (z : Scalar) (N : Nat) :
    (ScalarSeries.block (polynomialNomeDifferenceTerm z 2) 0 N).Equiv
      (sub (scaleRat 2 (polynomialNomeMomentPrefix z 1 N)) (polynomialNomeMomentPrefix z 0 N)) := by
  let t := fun n => scaleRat 2 (polynomialNomeMomentTerm z 1 n)
  let u := polynomialNomeMomentTerm z 0
  have ht n : (t n).Valid := scaleRat_valid (polynomialNomeMomentTerm_valid z 1 n)
  have hu := polynomialNomeMomentTerm_valid z 0
  have h1 := ScalarSeries.block_congr _ _ (fun n => polynomialNomeDifferenceTerm_degree_2 z n) 0 N
  have h2 := representedBlock_sub t u ht hu 0 N
  have h3 := FunctionTheory.sub_congr
    (representedBlock_scale (polynomialNomeMomentTerm z 1) (polynomialNomeMomentTerm_valid z 1) 2 0 N)
    (equiv_refl _ (polynomialNomeMomentPrefix_valid z 0 N))
  exact equiv_trans (ScalarSeries.block_valid _ (polynomialNomeDifferenceTerm_valid z 2) 0 N)
    (ScalarSeries.block_valid _ (fun n => sub_valid (ht n) (hu n)) 0 N)
    (sub_valid (scaleRat_valid (polynomialNomeMomentPrefix_valid z 1 N)) (polynomialNomeMomentPrefix_valid z 0 N)) h1
    (equiv_trans (ScalarSeries.block_valid _ (fun n => sub_valid (ht n) (hu n)) 0 N)
      (sub_valid (ScalarSeries.block_valid t ht 0 N) (ScalarSeries.block_valid u hu 0 N))
      (sub_valid (scaleRat_valid (polynomialNomeMomentPrefix_valid z 1 N)) (polynomialNomeMomentPrefix_valid z 0 N)) h2 h3)

end ComputableAnalysis.ModularForms
