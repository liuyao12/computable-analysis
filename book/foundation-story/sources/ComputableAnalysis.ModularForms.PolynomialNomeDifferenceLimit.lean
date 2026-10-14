import ComputableAnalysis.ModularForms.PolynomialNomeDifferenceSeries

/-! Concrete polynomial nome moments satisfy the proved backward-difference limit identity. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

private theorem scaled_one_product (c : Rat) (x : Scalar) :
    (mul (scaleRat c (ofQComplex QComplex.one)) x.val).Equiv (scaleRat c x.val) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := mul_valid (scaleRat_valid (ofQComplex_valid _)) x.property)
    (hright := scaleRat_valid x.property)
  let X := ComplexRawQuotient.ofRaw x.val x.property
  change ComplexRawQuotient.scaleRat c 1*X=ComplexRawQuotient.scaleRat c X
  rw [←ComplexRawQuotient.scaleRat_mul]
  have ho : (1:ComplexRawQuotient.Value)*X=X := by grind only
  rw [ho]

private theorem polynomial_difference_prefix (z : Scalar) (k N : Nat) :
    (ScalarSeries.block (polynomialNomeDifferenceTerm z k) 0 N).Equiv
      (nomeCoefficientPrefix z (nomeCoefficientDifference (polynomialNomeCoefficient k)) N) := by
  apply ScalarSeries.block_congr
  intro n
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := polynomialNomeDifferenceTerm_valid z k n)
    (hright := mul_valid (nomeCoefficientDifference (polynomialNomeCoefficient k) (n+1)).property
      (LocalODE.power_valid _ z.property (n+1)))
  let Q := ComplexRawQuotient.ofRaw (LocalODE.power z.val (n+1)) (LocalODE.power_valid _ z.property (n+1))
  let c := ((n+1:Nat):Rat)^k
  let d := (n:Rat)^k
  simp only [nomeCoefficientDifference,polynomialNomeCoefficient,Nat.add_sub_cancel]
  change ComplexRawQuotient.scaleRat (c-d) Q=
    (ComplexRawQuotient.scaleRat c 1-ComplexRawQuotient.scaleRat d 1)*Q
  have hs : ComplexRawQuotient.scaleRat c (1:ComplexRawQuotient.Value)-ComplexRawQuotient.scaleRat d 1=
      ComplexRawQuotient.scaleRat (c-d) 1 := by
    change ComplexRawQuotient.scaleRat c 1+ -ComplexRawQuotient.scaleRat d 1=_
    rw [ComplexRawQuotient.neg_scaleRat,ComplexRawQuotient.add_scaleRat]
    congr 1
    grind only
  rw [hs,←ComplexRawQuotient.scaleRat_mul]
  have ho : (1:ComplexRawQuotient.Value)*Q=Q := by grind only
  rw [ho]

theorem polynomialNomeMoment_difference_identity (z : Scalar) (r : Rat) (k : Nat) (hr : 0≤r)
    (hlocal : polynomialNomeMomentRatio r k≤(1:Rat)/2) (hz : Small z.val r) :
    (mul (sub (ofQComplex QComplex.one) z.val) (polynomialNomeMomentSum z r k)).Equiv
      (add (polynomialNomeDifferenceSum z r k) (mul (polynomialNomeCoefficient k 0).val z.val)) := by
  let s : Scalar := ⟨polynomialNomeMomentSum z r k,polynomialNomeMomentSum_valid z r k hr hlocal hz⟩
  let d : Scalar := ⟨polynomialNomeDifferenceSum z r k,polynomialNomeDifferenceSum_valid z r k hr hlocal hz⟩
  let e := fun (N : Nat) => 4*r*(polynomialNomeMomentRatio r k)^N
  have he : ShrinksToZero e := LocalODE.tail_bound_shrinks r _ hr
    (polynomialNomeMomentRatio_nonneg r k hr) hlocal
  have hen (N : Nat) : 0≤e N := Rat.mul_nonneg (Rat.mul_nonneg (by decide) hr)
    (Rat.pow_nonneg (polynomialNomeMomentRatio_nonneg r k hr))
  apply nomeCoefficient_difference_limit z (polynomialNomeCoefficient k) s d e e e he he he hen
  · intro N
    exact Small.congr
      (sub_valid s.property (polynomialNomeMomentPrefix_valid z k N))
      (sub_valid s.property (nomeCoefficientPrefix_valid z (polynomialNomeCoefficient k) N))
      (FunctionTheory.sub_congr (equiv_refl _ s.property)
        (polynomialNomeMomentPrefix_coefficient_agreement z k N))
      (polynomialNomeMomentSum_close z r k hr hlocal hz N)
  · intro N
    exact Small.congr
      (sub_valid d.property (ScalarSeries.block_valid _ (polynomialNomeDifferenceTerm_valid z k) 0 N))
      (sub_valid d.property (nomeCoefficientPrefix_valid z (nomeCoefficientDifference (polynomialNomeCoefficient k)) N))
      (FunctionTheory.sub_congr (equiv_refl _ d.property) (polynomial_difference_prefix z k N))
      (polynomialNomeDifferenceSum_close z r k hr hlocal hz N)
  · intro N
    let q : Scalar := ⟨LocalODE.power z.val (N+1),LocalODE.power_valid _ z.property (N+1)⟩
    have h := (polynomialNome_boundary_bound z r k hr hz N).mono (show
        2*r*(polynomialNomeMomentRatio r k)^N≤e N from by
      have hp := Rat.pow_nonneg (n := N) (polynomialNomeMomentRatio_nonneg r k hr)
      have hprod := Rat.mul_nonneg hr hp
      dsimp [e]
      grind only)
    exact Small.congr (scaleRat_valid q.property)
      (mul_valid (polynomialNomeCoefficient k N).property q.property)
      (equiv_symm (scaled_one_product ((N:Rat)^k) q)) h

end ComputableAnalysis.ModularForms
