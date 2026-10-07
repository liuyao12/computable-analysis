import ComputableAnalysis.ExponentialComputations.ComplexFunctions
import ComputableAnalysis.ModularForms.EntireNomeKernelClassification

/-! Full exponential fibers and logarithm branch periods. The period is
constructed from the computable geometric half-pi, not Mathlib's constants. -/
namespace ComputableAnalysis.ExponentialComputations.Complex
open ComplexRaw FunctionTheory RiemannHilbert LocalODE DomainFunctions NonzeroBoxSearch ModularForms
set_option maxHeartbeats 1000000
private def scalarClass (z : Scalar) := ComplexRawQuotient.ofRaw z.val z.property

/-- The represented value `2*pi*i*k`, using the geometric half-pi. -/
def period (k : Int) : Scalar :=
  ModularForms.scalarProduct nomeSlope ⟨ofQComplex ⟨(k:Rat),0⟩,ofQComplex_valid _⟩

theorem exp_period (k : Int) : (exp (period k)).val.Equiv one := by
  let o : Scalar := ⟨zero,ofQComplex_valid _⟩
  let c : Scalar := ⟨ofQComplex ⟨(k:Rat),0⟩,ofQComplex_valid _⟩
  have hc : (integerShiftScalar o k).val.Equiv c.val := by
    intro n
    apply (compareAt_overlap_iff _ _ n n).mpr
    simp [integerShiftScalar,integerAffine,o,c,zero,translate,scaleRat,ofQComplex,add,
      QBox.scaleRat,QBox.add,QComplex.add,QComplex.zero,QBox.Overlaps,QComplex.le_def,Rat.zero_add]
  have ho : (ModularForms.scalarProduct nomeSlope o).val.Equiv zero := mul_zero_equiv _ nomeSlope.property
  exact equiv_trans (exp (period k)).property (entireNomeMap.eval c (entireNomeMap_mem c)).property
    (ofQComplex_valid _) (equiv_symm (entireNomeMap_exponent c))
    (equiv_trans (entireNomeMap.eval c (entireNomeMap_mem c)).property
      (entireNomeMap.eval (integerShiftScalar o k) (entireNomeMap_mem _)).property (ofQComplex_valid _)
      (entireNomeMap.eval_congr _ _ _ _ (equiv_symm hc))
      (equiv_trans (entireNomeMap.eval (integerShiftScalar o k) (entireNomeMap_mem _)).property
        (entireNomeMap.eval o (entireNomeMap_mem o)).property (ofQComplex_valid _)
        (entireNomeMap_period_int o k)
        (equiv_trans (entireNomeMap.eval o (entireNomeMap_mem o)).property
          (exp (ModularForms.scalarProduct nomeSlope o)).property (ofQComplex_valid _) (entireNomeMap_exponent o)
          (equiv_trans (exp (ModularForms.scalarProduct nomeSlope o)).property (exp o).property (ofQComplex_valid _)
            (exp_congr _ _ ho) entireExponential_zero))))

theorem exp_translate_period (z : Scalar) (k : Int) :
    (exp (scalarSum z (period k))).val.Equiv (exp z).val :=
  equiv_trans (exp (scalarSum z (period k))).property
    (mul_valid (exp z).property (exp (period k)).property) (exp z).property
    (equiv_symm (exp_add z (period k)))
    (equiv_trans (mul_valid (exp z).property (exp (period k)).property)
      (mul_valid (exp z).property (ofQComplex_valid _)) (exp z).property
      (mul_equiv (exp z).property (exp z).property (exp (period k)).property (ofQComplex_valid _)
        (equiv_refl _ (exp z).property) (exp_period k)) (mul_one_equiv _ (exp z).property))

theorem exp_kernel (z : Scalar) (he : (exp z).val.Equiv one) :
    ∃ k : Int, z.val.Equiv (period k).val := by
  let w := ModularForms.scalarProduct nomeInverseSlope z
  have hi := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid nomeSlope.property nomeInverseSlope.property) (hright := ofQComplex_valid _)
    (RepresentedReciprocal.mul_inverse nomeSlope nomeSlope_nonzero)
  have hw : (ModularForms.scalarProduct nomeSlope w).val.Equiv z.val := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := (ModularForms.scalarProduct nomeSlope w).property) (hright := z.property)
    let S := scalarClass nomeSlope
    let I := scalarClass nomeInverseSlope
    let Z := scalarClass z
    change S*I=1 at hi
    change S*(I*Z)=Z
    grind only
  have hn := equiv_trans (entireNomeMap.eval w (entireNomeMap_mem w)).property
    (exp (ModularForms.scalarProduct nomeSlope w)).property (ofQComplex_valid _) (entireNomeMap_exponent w)
    (equiv_trans (exp (ModularForms.scalarProduct nomeSlope w)).property (exp z).property (ofQComplex_valid _)
      (exp_congr _ _ hw) he)
  obtain ⟨k,hk⟩ := entireNome_kernel_exists_integer w hn
  exact ⟨k,equiv_trans z.property (ModularForms.scalarProduct nomeSlope w).property (period k).property
    (equiv_symm hw) (mul_equiv nomeSlope.property nomeSlope.property w.property
      (ofQComplex_valid _) (equiv_refl _ nomeSlope.property) hk)⟩

theorem exp_fiber (z w : Scalar) (h : (exp z).val.Equiv (exp w).val) :
    ∃ k : Int, (sub z.val w.val).Equiv (period k).val :=
  exp_kernel ⟨sub z.val w.val,sub_valid z.property w.property⟩
    (entireExponential_fiber_difference z w h)

/-- One integer works throughout the nonempty actual overlap. -/
theorem LogSeed.overlap_period (s t : LogSeed) (p : Scalar)
    (hp : s.function.domain p ∧ t.function.domain p) :
    ∃ k : Int, ∀ z : Scalar, ∀ hz : s.function.domain z ∧ t.function.domain z,
      (sub (s.function.eval z hz.1).val (t.function.eval z hz.2).val).Equiv (period k).val := by
  have he := equiv_trans (exp (s.function.eval p hp.1)).property p.property
    (exp (t.function.eval p hp.2)).property (s.exponential_eval p hp.1)
    (equiv_symm (t.exponential_eval p hp.2))
  obtain ⟨k,hk⟩ := exp_fiber _ _ he
  refine ⟨k,fun z hz => ?_⟩
  exact equiv_trans (sub_valid (s.function.eval z hz.1).property (t.function.eval z hz.2).property)
    (sub_valid (s.function.eval p hp.1).property (t.function.eval p hp.2).property) (period k).property
    (s.overlap_difference t p z hp hz) hk

/-- The branch is the inverse on the neighborhood of its chosen seed.
The chart hypothesis concerns the exponential image; proximity selects
which logarithm of that image is meant. -/
theorem LogSeed.log_exp (s : LogSeed) (w : Scalar)
    (hw : s.function.domain (exp w)) (hnear : Small (sub w.val s.value.val) 1) :
    (s.function.eval (exp w) hw).val.Equiv w.val := by
  let u := RelativeLogarithm.point s.center s.nonzero (exp w)
  let l := LocalLogarithm.function.eval u hw
  let o : Scalar := ⟨zero,ofQComplex_valid _⟩
  have hzero := LocalLogarithm.initial
  have hu := interior_bound LocalLogarithm.radius.val u hw
  have hdiff : (sub u.val o.val).Equiv u.val := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := sub_valid u.property o.property) (hright := u.property)
    change scalarClass u-0=scalarClass u
    grind only
  have hb := LocalLogarithm.lipschitz o u (interior_zero _ LocalLogarithm.radius.property) hw
    LocalLogarithm.radius (Small.congr u.property (sub_valid u.property o.property) (equiv_symm hdiff) hu)
  have hL : (sub l.val (LocalLogarithm.function.eval o (interior_zero _ LocalLogarithm.radius.property)).val).Equiv l.val := by
    have hi := ComplexRawQuotient.ofRaw_eq_ofRaw
      (hleft := (LocalLogarithm.function.eval o (interior_zero _ LocalLogarithm.radius.property)).property)
      (hright := ofQComplex_valid _) hzero
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := sub_valid l.property (LocalLogarithm.function.eval o (interior_zero _ LocalLogarithm.radius.property)).property)
      (hright := l.property)
    let L := scalarClass l
    let O := scalarClass (LocalLogarithm.function.eval o (interior_zero _ LocalLogarithm.radius.property))
    change O=0 at hi
    change L-O=L
    grind only
  have hl : Small l.val 1 := (Small.congr
    (sub_valid l.property (LocalLogarithm.function.eval o (interior_zero _ LocalLogarithm.radius.property)).property)
    l.property hL hb).mono (by decide +kernel)
  let a := s.function.eval (exp w) hw
  let d : Scalar := ⟨sub a.val w.val,sub_valid a.property w.property⟩
  have hd : d.val.Equiv (sub l.val (sub w.val s.value.val)) := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := d.property) (hright := sub_valid l.property (sub_valid w.property s.value.property))
    let A := scalarClass s.value
    let L := scalarClass l
    let W := scalarClass w
    change (A+L)-W=L-(W-A)
    grind only
  have hbound := Small.congr (sub_valid l.property (sub_valid w.property s.value.property)) d.property
    (equiv_symm hd) (SeriesLimitLaws.small_sub hl hnear)
  have hb4 := hbound.mono (show (1+1:Rat)≤4 by decide +kernel)
  have hz := entireExponential_kernel_four_strip d hb4.2.2.1 hb4.2.2.2
    (entireExponential_fiber_difference a w (s.exponential_eval (exp w) hw))
  have he := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := d.property) (hright := ofQComplex_valid _) hz
  apply ComplexRawQuotient.equiv_of_ofRaw_eq (hleft := a.property) (hright := w.property)
  let A := scalarClass a
  let W := scalarClass w
  change A-W=0 at he
  change A=W
  grind only

/-- The positive real logarithm extends as a full complex value throughout
the real part of its normalized chart, not merely in its real coordinate. -/
theorem realLogarithmAt_agrees (x y : PositiveInput)
    (hy : (realLogarithmAt x).function.domain (realAxis y.val)) :
    ((realLogarithmAt x).function.eval (realAxis y.val) hy).val.Equiv (realAxis (log y)).val := by
  let s := realLogarithmAt x
  let a := s.function.eval (realAxis y.val) hy
  let b := realAxis (log y)
  let d : Scalar := ⟨sub a.val b.val,sub_valid a.property b.property⟩
  have he := equiv_trans (exp a).property (realAxis y.val).property (exp b).property
    (s.exponential_eval _ hy) (equiv_symm (realLogarithmAt y).exponential)
  have hb := RelativeLogarithm.value_bound (realAxis x.val)
    (positive_real_nonzero x.val x.property) (realAxis y.val) hy
  have hl : (RealRaw.ofRat (-4)).Le d.val.imagPart := by
    intro n m
    have h := hb.2.2.1 n m
    simpa only [d,a,b,s,LogSeed.function,realLogarithmAt,LogarithmBranchCharts.function,
      MatrixExponential.propagatedBranch,DomainFunctions.scalarSum,realAxis,ofRealRaw,sub,add,neg,imagPart,
      QBox.add,QBox.neg,QComplex.add,QComplex.neg,Rat.zero_add,Rat.neg_zero,Rat.add_zero] using h
  have hu : d.val.imagPart.Le (RealRaw.ofRat 4) := by
    intro n m
    have h := hb.2.2.2 n m
    simpa only [d,a,b,s,LogSeed.function,realLogarithmAt,LogarithmBranchCharts.function,
      MatrixExponential.propagatedBranch,DomainFunctions.scalarSum,realAxis,ofRealRaw,sub,add,neg,imagPart,
      QBox.add,QBox.neg,QComplex.add,QComplex.neg,Rat.zero_add,Rat.neg_zero,Rat.add_zero] using h
  have hz := entireExponential_kernel_four_strip d hl hu (entireExponential_fiber_difference a b he)
  have hd := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := d.property) (hright := ofQComplex_valid _) hz
  apply ComplexRawQuotient.equiv_of_ofRaw_eq (hleft := a.property) (hright := b.property)
  let A := scalarClass a
  let B := scalarClass b
  change A-B=0 at hd
  change A=B
  grind only
end ComputableAnalysis.ExponentialComputations.Complex
