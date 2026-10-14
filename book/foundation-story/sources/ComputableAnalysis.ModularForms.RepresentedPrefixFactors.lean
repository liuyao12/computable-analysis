import ComputableAnalysis.ModularForms.NomeMomentLambertComparison
import ComputableAnalysis.ModularForms.CMOrbitDenominatorBounds163
import ComputableAnalysis.RiemannHilbert.DomainDerivativeBounds

/-! Finite factorization and quantitative limit transport for actual scalar prefixes. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

/-- Finite prefixes commute with multiplication by a fixed represented factor. -/
theorem representedPrefix_mul_left (t : Nat → ComplexRaw) (ht : ∀ n, (t n).Valid)
    (c : Scalar) (N : Nat) :
    (ScalarSeries.block (fun n => mul c.val (t n)) 0 N).Equiv
      (mul c.val (ScalarSeries.block t 0 N)) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := ScalarSeries.block_valid _ (fun n => mul_valid c.property (ht n)) 0 N)
    (hright := mul_valid c.property (ScalarSeries.block_valid t ht 0 N))
  rw [ScalarSeries.prefix_image _ (fun n => mul_valid c.property (ht n))]
  change FiniteProducts.partialSum (fun n => ComplexRawQuotient.ofRaw c.val c.property *
    ComplexRawQuotient.ofRaw (t n) (ht n)) N=
    ComplexRawQuotient.ofRaw c.val c.property * ComplexRawQuotient.ofRaw (ScalarSeries.block t 0 N)
      (ScalarSeries.block_valid t ht 0 N)
  rw [ScalarSeries.prefix_image t ht]
  have hf : (fun n => ComplexRawQuotient.ofRaw c.val c.property * ComplexRawQuotient.ofRaw (t n) (ht n))=
      (fun n => ComplexRawQuotient.ofRaw (t n) (ht n) * ComplexRawQuotient.ofRaw c.val c.property) := by
    funext n
    exact ComplexRawQuotient.mul_comm _ _
  rw [hf,FiniteProducts.prefix_mul]
  exact ComplexRawQuotient.mul_comm _ _

/-- Rational scaling can be incorporated into a fixed represented factor. -/
theorem representedScale_mul_factor (a b : Scalar) (c : Rat) :
    (scaleRat c (mul a.val b.val)).Equiv (mul (scaleRat c a.val) b.val) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := scaleRat_valid (mul_valid a.property b.property))
    (hright := mul_valid (scaleRat_valid a.property) b.property)
  change ComplexRawQuotient.scaleRat c (ComplexRawQuotient.ofRaw a.val a.property * ComplexRawQuotient.ofRaw b.val b.property)=
    ComplexRawQuotient.scaleRat c (ComplexRawQuotient.ofRaw a.val a.property) * ComplexRawQuotient.ofRaw b.val b.property
  exact ComplexRawQuotient.scaleRat_mul _ _ _

/-- A fixed-factor limit follows from actual common prefixes and shrinking errors. -/
theorem representedFactor_limit_comparison (F G c : Scalar) (p q : Nat → Scalar)
    (e f : Nat → Rat) (he : ShrinksToZero e) (hf : ShrinksToZero f)
    (hf0 : ∀ N, 0≤f N)
    (hF : ∀ N, Small (sub F.val (p N).val) (e N))
    (hG : ∀ N, Small (sub G.val (q N).val) (f N))
    (hpq : ∀ N, (p N).val.Equiv (mul c.val (q N).val)) :
    F.val.Equiv (mul c.val G.val) := by
  let C := DomainFunctions.scalarBound c
  have hC : 0≤C := Rat.le_of_lt (DomainFunctions.scalarBound_pos c)
  have hs := RepresentedCauchySum.sum_shrinks _ _ he
    (SeriesLimitLaws.shrinks_scale _ hf (2*C) (Rat.mul_nonneg (by decide) hC))
  apply SeriesLimitLaws.equiv_of_small_sub_zero
  apply SeriesLimitLaws.small_closed _ 0 (fun N => e N+2*C*f N) hs
  intro N
  have hGc := representedFactor_difference_small c.val G.val (q N).val
    c.property G.property (q N).property C (f N) hC (hf0 N) (DomainFunctions.scalar_small c) (hG N)
  have hFp : Small (sub F.val (mul c.val (q N).val)) (e N) :=
    Small.congr (sub_valid F.property (p N).property)
      (sub_valid F.property (mul_valid c.property (q N).property))
      (FunctionTheory.sub_congr (equiv_refl F.val F.property) (hpq N)) (hF N)
  have heq : (sub (sub F.val (mul c.val (q N).val))
      (sub (mul c.val G.val) (mul c.val (q N).val))).Equiv (sub F.val (mul c.val G.val)) := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := sub_valid (sub_valid F.property (mul_valid c.property (q N).property))
        (sub_valid (mul_valid c.property G.property) (mul_valid c.property (q N).property)))
      (hright := sub_valid F.property (mul_valid c.property G.property))
    let A := ComplexRawQuotient.ofRaw F.val F.property
    let B := ComplexRawQuotient.ofRaw c.val c.property
    let D := ComplexRawQuotient.ofRaw G.val G.property
    let Q := ComplexRawQuotient.ofRaw (q N).val (q N).property
    change (A-B*Q)-(B*D-B*Q)=A-B*D
    generalize A=a,B=b,D=d,Q=q
    grind only
  have h := Small.congr
    (sub_valid (sub_valid F.property (mul_valid c.property (q N).property))
      (sub_valid (mul_valid c.property G.property) (mul_valid c.property (q N).property)))
    (sub_valid F.property (mul_valid c.property G.property)) heq (SeriesLimitLaws.small_sub hFp hGc)
  simpa only [Rat.zero_add] using h

end ComputableAnalysis.ModularForms
