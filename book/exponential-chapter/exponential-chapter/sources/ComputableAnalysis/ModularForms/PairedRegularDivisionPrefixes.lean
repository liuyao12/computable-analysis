import ComputableAnalysis.ModularForms.PairedRegularDivisionSeries

/-! Finite-prefix multiplication for the constructed regular-division series. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory
set_option maxHeartbeats 200000

theorem pairedRegularDivisionPrefix_product (z : Scalar) (hz : Small z.val (1/4)) (N : Nat) :
    (mul z.val (ScalarSeries.block (fun n => (pairedRegularDivisionTerm z hz n).val) 0 N)).Equiv
      (ScalarSeries.block (fun n => (pairedFullTerm z
        (pairedSmallDisk_domain z (1/4) (by decide +kernel) (by decide +kernel) hz) n).val) 0 N) := by
  let t := fun n => (pairedRegularDivisionTerm z hz n).val
  let ht := fun n => (pairedRegularDivisionTerm z hz n).property
  let hd := pairedSmallDisk_domain z (1/4) (by decide +kernel) (by decide +kernel) hz
  let u := fun n => (pairedFullTerm z hd n).val
  let hu := fun n => (pairedFullTerm z hd n).property
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := mul_valid z.property (ScalarSeries.block_valid t ht 0 N))
    (hright := ScalarSeries.block_valid u hu 0 N)
  change ComplexRawQuotient.ofRaw z.val z.property *
    ComplexRawQuotient.ofRaw (ScalarSeries.block t 0 N) (ScalarSeries.block_valid t ht 0 N) =
    ComplexRawQuotient.ofRaw (ScalarSeries.block u 0 N) (ScalarSeries.block_valid u hu 0 N)
  rw [ScalarSeries.block_image _ ht,ScalarSeries.block_image _ hu]
  let Z := ComplexRawQuotient.ofRaw z.val z.property
  let f := fun n => ComplexRawQuotient.ofRaw (t n) (ht n)
  let g := fun n => ComplexRawQuotient.ofRaw (u n) (hu n)
  have hterm (n : Nat) : Z*f n=g n :=
    ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := mul_valid z.property (ht n)) (hright := hu n)
      (pairedRegularDivisionTerm_product z hz n)
  change Z*FiniteProducts.block f 0 N=FiniteProducts.block g 0 N
  simp only [FiniteProducts.block,Nat.zero_add]
  induction N with
  | zero => change Z*0=0; grind only
  | succ N ih =>
    simp only [FiniteProducts.partialSum.eq_2]
    have he := hterm N
    grind only

theorem pairedRegularDivisionTerm_congr (z w : Scalar) (hz : Small z.val (1/4))
    (hw : Small w.val (1/4)) (he : z.val.Equiv w.val) (n : Nat) :
    (pairedRegularDivisionTerm z hz n).val.Equiv (pairedRegularDivisionTerm w hw n).val :=
  scaleRat_equiv (RepresentedReciprocal.inverse_congr _ _ _ _
    (FunctionTheory.sub_congr (mul_equiv z.property w.property z.property w.property he he)
      (equiv_refl _ (ofQComplex_valid _))))

theorem pairedRegularDivisionValue_congr (z w : Scalar) (hz : Small z.val (1/4))
    (hw : Small w.val (1/4)) (he : z.val.Equiv w.val) :
    (pairedRegularDivisionValue z hz).Equiv (pairedRegularDivisionValue w hw) :=
  inverseSquareSeriesValue_congr _ _ _ _ 8
    (pairedRegularDivisionTerm_bound z hz) (pairedRegularDivisionTerm_bound w hw)
    (pairedRegularDivisionTerm_congr z w hz hw he)

end ComputableAnalysis.ModularForms
