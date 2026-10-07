import ComputableAnalysis.ModularForms.ImaginaryExponentialInterval
import ComputableAnalysis.ModularForms.ExponentialFiberRealPart
import ComputableAnalysis.ModularForms.RepresentedOrderTotal

/-! A fixed unit-width imaginary-coordinate separation for actual exponential
fibers, proved from the represented rotation's interval injectivity. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert

private theorem imaginary_add_one (x : RealRaw) (hx : x.Valid) :
    (imaginaryAxis (RealRaw.add x (RealRaw.ofRat 1))).Equiv
      (add (imaginaryAxis x) (imaginaryAxis (RealRaw.ofRat 1))) := by
  intro n
  have ho := RealRaw.interval_order_of_valid x hx n
  apply (compareAt_overlap_iff _ _ n n).mpr
  simp only [imaginaryAxis,mulI,ofRealRaw,RealRaw.add,RealRaw.addCompute,RealRaw.ofRat,
    add,QBox.add,QComplex.add,QBox.Overlaps,QComplex.le_def,Rat.neg_zero,Rat.zero_add]
  constructor <;> constructor <;> grind only

/-- A kernel angle in the semantic interval [0,1] is exactly zero. -/
theorem entireExponential_imaginary_kernel_nonnegative_unit (x : RealRaw) (hx : x.Valid)
    (hl : (RealRaw.ofRat 0).Le x) (hu : x.Le (RealRaw.ofRat 1))
    (he : (entireExponentialValue ⟨imaginaryAxis x,imaginaryAxis_valid hx⟩).val.Equiv one) :
    x.Equiv (RealRaw.ofRat 0) := by
  let a := RealRaw.add x (RealRaw.ofRat 1)
  have ha : a.Valid := RealRaw.add_valid hx (RealRaw.ofRat_valid 1)
  have hal : (RealRaw.ofRat 1).Le a := by
    intro n m
    have h := hl 0 m
    change 0≤(x.compute m).hi at h
    change 1≤(x.compute m).hi+1
    grind only
  have hau : a.Le (RealRaw.ofRat 2) := by
    intro n m
    have h := hu n 0
    change (x.compute n).lo≤1 at h
    change (x.compute n).lo+1≤2
    grind only
  let X : Scalar := ⟨imaginaryAxis x,imaginaryAxis_valid hx⟩
  let O : Scalar := ⟨imaginaryAxis (RealRaw.ofRat 1),imaginaryAxis_valid (show (RealRaw.ofRat 1).Valid from RealRaw.ofRat_valid 1)⟩
  let A : Scalar := ⟨imaginaryAxis a,imaginaryAxis_valid ha⟩
  have hp := mul_equiv (entireExponentialValue X).property (ofQComplex_valid _)
    (entireExponentialValue O).property (entireExponentialValue O).property he
    (equiv_refl _ (entireExponentialValue O).property)
  have hAO : (entireExponentialValue A).val.Equiv (entireExponentialValue O).val :=
    equiv_trans (entireExponentialValue A).property
      (entireExponentialValue (DomainFunctions.scalarSum X O)).property
      (entireExponentialValue O).property
      (entireExponentialValue_congr A (DomainFunctions.scalarSum X O) (imaginary_add_one x hx))
      (equiv_trans (entireExponentialValue (DomainFunctions.scalarSum X O)).property
        (mul_valid (entireExponentialValue X).property (entireExponentialValue O).property)
        (entireExponentialValue O).property (equiv_symm (entireExponential_addition X O))
        (equiv_trans (mul_valid (entireExponentialValue X).property (entireExponentialValue O).property)
          (mul_valid (ofQComplex_valid _) (entireExponentialValue O).property)
          (entireExponentialValue O).property hp (one_mul_equiv _ (entireExponentialValue O).property)))
  have huq := entireExponential_imaginary_interval_injective a (RealRaw.ofRat 1) ha
    (show (RealRaw.ofRat 1).Valid from RealRaw.ofRat_valid 1) hal hau
    (by intro n m; change (1:Rat)≤1; decide +kernel)
    (by intro n m; change (1:Rat)≤2; decide +kernel) hAO
  intro n
  have h := (RealRaw.compareAt_overlap_iff _ _ n n).mp (huq n)
  apply (RealRaw.compareAt_overlap_iff _ _ n n).mpr
  change (x.compute n).lo+1≤1 ∧ 1≤(x.compute n).hi+1 at h
  change (x.compute n).lo≤0 ∧ 0≤(x.compute n).hi
  grind only

/-- There is no nonzero kernel angle in the full semantic interval [-1,1]. -/
theorem entireExponential_imaginary_kernel_unit (x : RealRaw) (hx : x.Valid)
    (hl : (RealRaw.ofRat (-1)).Le x) (hu : x.Le (RealRaw.ofRat 1))
    (he : (entireExponentialValue ⟨imaginaryAxis x,imaginaryAxis_valid hx⟩).val.Equiv one) :
    x.Equiv (RealRaw.ofRat 0) := by
  rcases representedReal_le_total (RealRaw.ofRat 0) x (show (RealRaw.ofRat 0).Valid from RealRaw.ofRat_valid 0) hx with hp | hn
  · exact entireExponential_imaginary_kernel_nonnegative_unit x hx hp hu he
  · let y := RealRaw.neg x
    have hy := RealRaw.neg_valid hx
    have hyl : (RealRaw.ofRat 0).Le y := by
      intro n m
      have h := hn m 0
      change (x.compute m).lo≤0 at h
      change 0≤ -(x.compute m).lo
      grind only
    have hyu : y.Le (RealRaw.ofRat 1) := by
      intro n m
      have h := hl 0 n
      change -1≤(x.compute n).hi at h
      change -(x.compute n).hi≤1
      grind only
    have hneg : (imaginaryAxis y).Equiv (neg (imaginaryAxis x)) := by
      intro n
      have ho := RealRaw.interval_order_of_valid x hx n
      apply (compareAt_overlap_iff _ _ n n).mpr
      change ((0:Rat)≤0 ∧ -(x.compute n).hi≤ -(x.compute n).lo) ∧
        (0≤(0:Rat) ∧ -(x.compute n).hi≤ -(x.compute n).lo)
      constructor <;> constructor <;> grind only
    have hey : (entireExponentialValue ⟨imaginaryAxis y,imaginaryAxis_valid hy⟩).val.Equiv one :=
      equiv_trans (entireExponentialValue ⟨imaginaryAxis y,imaginaryAxis_valid hy⟩).property
        (entireExponentialValue ⟨neg (imaginaryAxis x),neg_valid (imaginaryAxis_valid hx)⟩).property
        (ofQComplex_valid _)
        (entireExponentialValue_congr _ _ hneg)
        (entireExponential_kernel_neg ⟨imaginaryAxis x,imaginaryAxis_valid hx⟩ he)
    have hz := entireExponential_imaginary_kernel_nonnegative_unit y hy hyl hyu hey
    intro n
    have h := (RealRaw.compareAt_overlap_iff _ _ n n).mp (hz n)
    apply (RealRaw.compareAt_overlap_iff _ _ n n).mpr
    change -(x.compute n).hi≤0 ∧ 0≤ -(x.compute n).lo at h
    change (x.compute n).lo≤0 ∧ 0≤(x.compute n).hi
    grind only

/-- Any actual kernel element with imaginary coordinate in [-1,1] is zero.
The real coordinate is proved zero, rather than supplied as a hypothesis. -/
theorem entireExponential_kernel_unit_strip (z : Scalar)
    (hl : (RealRaw.ofRat (-1)).Le z.val.imagPart)
    (hu : z.val.imagPart.Le (RealRaw.ofRat 1))
    (he : (entireExponentialValue z).val.Equiv one) : z.val.Equiv zero := by
  have hr := entireExponential_kernel_real_zero z he
  have haxis : z.val.Equiv (imaginaryAxis z.val.imagPart) := by
    intro n
    have h := (RealRaw.compareAt_overlap_iff _ _ n n).mp (hr n)
    have ho := (valid_ordered z.property n).2
    apply (compareAt_overlap_iff _ _ n n).mpr
    exact ⟨⟨h.1,ho⟩,⟨h.2,ho⟩⟩
  have hphase := entireExponentialValue_congr z
    ⟨imaginaryAxis z.val.imagPart,imaginaryAxis_valid (imagPart_valid z.property)⟩ haxis
  have hi := entireExponential_imaginary_kernel_unit z.val.imagPart (imagPart_valid z.property) hl hu
    (equiv_trans (entireExponentialValue ⟨imaginaryAxis z.val.imagPart,imaginaryAxis_valid (imagPart_valid z.property)⟩).property
      (entireExponentialValue z).property (ofQComplex_valid _) (equiv_symm hphase) he)
  intro n
  have hR := (RealRaw.compareAt_overlap_iff _ _ n n).mp (hr n)
  have hI := (RealRaw.compareAt_overlap_iff _ _ n n).mp (hi n)
  apply (compareAt_overlap_iff _ _ n n).mpr
  exact ⟨⟨hR.1,hI.1⟩,⟨hR.2,hI.2⟩⟩

/-- Equal exponential values force exact input equality whenever their
imaginary-coordinate difference belongs to [-1,1]. -/
theorem entireExponential_fiber_unit_strip (z w : Scalar)
    (hl : (RealRaw.ofRat (-1)).Le (sub z.val w.val).imagPart)
    (hu : (sub z.val w.val).imagPart.Le (RealRaw.ofRat 1))
    (he : (entireExponentialValue z).val.Equiv (entireExponentialValue w).val) :
    z.val.Equiv w.val := by
  have hd := entireExponential_kernel_unit_strip ⟨sub z.val w.val,sub_valid z.property w.property⟩ hl hu
    (entireExponential_fiber_difference z w he)
  have hD := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := sub_valid z.property w.property)
    (hright := ofQComplex_valid _) hd
  apply ComplexRawQuotient.equiv_of_ofRaw_eq (hleft := z.property) (hright := w.property)
  let Z := gridScalarValue z
  let W := gridScalarValue w
  change Z-W=0 at hD
  change Z=W
  grind only

end ComputableAnalysis.ModularForms
