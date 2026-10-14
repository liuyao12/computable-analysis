import ComputableAnalysis.ModularForms.NomeMomentFirstQuotient
import ComputableAnalysis.ModularForms.LambertPositivePowers

/-! Zeroth polynomial nome moment agrees with the actual Lambert construction. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

theorem polynomialNomeMomentRatio_zero (r : Rat) : polynomialNomeMomentRatio r 0=2*r := by
  simp only [polynomialNomeMomentRatio,Rat.pow_zero,Rat.mul_one]

theorem polynomialNomeMomentPrefix_zero (z : Scalar) (N : Nat) :
    (polynomialNomeMomentPrefix z 0 N).Equiv (lambertPositivePrefix z N) := by
  have hp (n : Nat) :
      ScalarSeries.block (fun n => LocalODE.power z.val (n+1)) 0 n=
        ScalarSeries.block (LocalODE.power z.val) 1 n := by
    induction n with
    | zero => rfl
    | succ n ih => simp only [ScalarSeries.block.eq_2,Nat.zero_add,ih,Nat.add_comm]
  have he := ScalarSeries.block_congr (polynomialNomeMomentTerm z 0)
    (fun n => LocalODE.power z.val (n+1)) (fun n => by
      simp only [polynomialNomeMomentTerm,Rat.pow_zero]
      apply ComplexRawQuotient.equiv_of_ofRaw_eq
        (hleft := scaleRat_valid (r := 1) (LocalODE.power_valid _ z.property (n+1)))
        (hright := LocalODE.power_valid _ z.property (n+1))
      change ComplexRawQuotient.scaleRat 1 (ComplexRawQuotient.ofRaw
        (LocalODE.power z.val (n+1)) (LocalODE.power_valid _ z.property (n+1)))=_
      exact ComplexRawQuotient.scaleRat_one _) 0 N
  rw [hp] at he
  exact he

theorem polynomialNomeMomentSum_zero_lambert (z : Scalar) (r : Rat) (hr : 0≤r)
    (hlocal : 2*r≤(1:Rat)/2) (hz : Small z.val r) :
    (polynomialNomeMomentSum z r 0).Equiv (lambertFactor z r) := by
  have hl : polynomialNomeMomentRatio r 0≤(1:Rat)/2 := by
    rw [polynomialNomeMomentRatio_zero]; exact hlocal
  let e := fun (N : Nat) => 4*r*(2*r)^N
  let f := fun (N : Nat) => 4*(2*r)^(N+1)
  have he : ShrinksToZero e := LocalODE.tail_bound_shrinks r _ hr (Rat.mul_nonneg (by decide) hr) hlocal
  have hf : ShrinksToZero f := lambertPositiveTail_shrinks r hr hlocal
  have hen (N : Nat) : 0≤e N := Rat.mul_nonneg (Rat.mul_nonneg (by decide) hr)
    (Rat.pow_nonneg (Rat.mul_nonneg (by decide) hr))
  have hfn (N : Nat) : 0≤f N := Rat.mul_nonneg (by decide)
    (Rat.pow_nonneg (Rat.mul_nonneg (by decide) hr))
  apply RepresentedCauchySum.unique (lambertPositivePrefix z) (lambertPositivePrefix_valid z)
    (fun N => e N+f N) (RepresentedCauchySum.sum_shrinks e f he hf) _ _
    (polynomialNomeMomentSum_valid z r 0 hr hl hz) (lambertFactor_valid z r hr hlocal hz)
  · intro N
    have h := polynomialNomeMomentSum_close z r 0 hr hl hz N
    rw [polynomialNomeMomentRatio_zero] at h
    have h' := Small.congr
      (sub_valid (polynomialNomeMomentSum_valid z r 0 hr hl hz) (polynomialNomeMomentPrefix_valid z 0 N))
      (sub_valid (polynomialNomeMomentSum_valid z r 0 hr hl hz) (lambertPositivePrefix_valid z N))
      (FunctionTheory.sub_congr (equiv_refl _ (polynomialNomeMomentSum_valid z r 0 hr hl hz))
        (polynomialNomeMomentPrefix_zero z N)) h
    exact h'.mono (by have hfN := hfn N; grind only)
  · intro N
    exact (lambertPositivePrefix_close z r hr hlocal hz N).mono (by
      have heN := hen N; grind only)

theorem polynomialNomeMomentSum_zero_quotient (z : Scalar) (r : Rat) (hr : 0≤r)
    (hlocal : 2*r≤(1:Rat)/2) (hz : Small z.val r)
    (hn : NonzeroBoxSearch.Nonzero (nomeDenominator z)) :
    (polynomialNomeMomentSum z r 0).Equiv
      (mul z.val (RepresentedReciprocal.inverse (nomeDenominator z) hn).val) := by
  have hl : polynomialNomeMomentRatio r 0≤(1:Rat)/2 := by
    rw [polynomialNomeMomentRatio_zero]; exact hlocal
  let j := RepresentedReciprocal.inverse (nomeDenominator z) hn
  have hg := equiv_symm (RepresentedReciprocal.inverse_unique (nomeDenominator z) hn
    ⟨nomeGeometricSum z r,nomeGeometricSum_valid z r hr hlocal hz⟩
    (nomeGeometricSum_inverse z r hr hlocal hz))
  exact equiv_trans (polynomialNomeMomentSum_valid z r 0 hr hl hz)
    (lambertFactor_valid z r hr hlocal hz) (mul_valid z.property j.property)
    (polynomialNomeMomentSum_zero_lambert z r hr hlocal hz)
    (mul_equiv z.property z.property (nomeGeometricSum_valid z r hr hlocal hz) j.property
      (equiv_refl _ z.property) hg)

end ComputableAnalysis.ModularForms
