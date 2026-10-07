import ComputableAnalysis.ModularForms.ExponentialKernelUnitStrip
import ComputableAnalysis.ModularForms.UpperSquareRootSeparation
import ComputableAnalysis.ModularForms.ExponentialPowers

/-! Kernel triviality on the fixed imaginary-coordinate strip [-4,4].
This is the strip needed for reducing by the known full geometric period. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert

/-- Positivity on the actual angle interval is independent of its raw name. -/
theorem imaginary_exponential_upper_of_bounds (x : RealRaw) (hx : x.Valid)
    (hl : (RealRaw.ofRat 1).Le x) (hu : x.Le (RealRaw.ofRat 2)) :
    InUpperHalfPlane (entireExponentialValue ⟨imaginaryAxis x,imaginaryAxis_valid hx⟩).val := by
  let A := boundedAngleFromBounds x hx hl hu
  have he := entireExponentialValue_congr
    ⟨imaginaryAxis A.raw,imaginaryAxis_valid A.valid⟩ ⟨imaginaryAxis x,imaginaryAxis_valid hx⟩
    (imaginaryAxis_equiv A.valid hx (boundedAngleFromBounds_agreement x hx hl hu))
  exact (upperHalfPlane_congr
    (entireExponentialValue ⟨imaginaryAxis A.raw,imaginaryAxis_valid A.valid⟩).property
    (entireExponentialValue ⟨imaginaryAxis x,imaginaryAxis_valid hx⟩).property he).mp A.exponential_positive_imaginary

/-- A nonnegative kernel angle at most four is exactly zero. -/
theorem entireExponential_imaginary_kernel_nonnegative_four (x : RealRaw) (hx : x.Valid)
    (hl : (RealRaw.ofRat 0).Le x) (hu : x.Le (RealRaw.ofRat 4))
    (he : (entireExponentialValue ⟨imaginaryAxis x,imaginaryAxis_valid hx⟩).val.Equiv one) :
    x.Equiv (RealRaw.ofRat 0) := by
  rcases representedReal_le_total x (RealRaw.ofRat 1) hx
    (show (RealRaw.ofRat 1).Valid from RealRaw.ofRat_valid 1) with h1 | h1
  · exact entireExponential_imaginary_kernel_nonnegative_unit x hx hl h1 he
  · rcases representedReal_le_total x (RealRaw.ofRat 2) hx
      (show (RealRaw.ofRat 2).Valid from RealRaw.ofRat_valid 2) with h2 | h2
    · have hp := imaginary_exponential_upper_of_bounds x hx h1 h2
      have h := (upperHalfPlane_congr
        (entireExponentialValue ⟨imaginaryAxis x,imaginaryAxis_valid hx⟩).property
        (ofQComplex_valid _) he).mp hp
      obtain ⟨N,hN⟩ := h
      change (0:Rat)<0 at hN
      contradiction
    · let y := RealRaw.scaleRat (1/2) x
      have hy : y.Valid := RealRaw.scaleRat_valid hx
      have hyl : (RealRaw.ofRat 1).Le y := by
        intro n m
        have h := h2 0 m
        change 2≤(x.compute m).hi at h
        simp only [y,RealRaw.Le,RealRaw.ofRat,RealRaw.scaleRat,RealRaw.scaleRatCompute,
          if_pos (show (0:Rat)≤1/2 by decide +kernel)]
        grind only
      have hyu : y.Le (RealRaw.ofRat 2) := by
        intro n m
        have h := hu n 0
        change (x.compute n).lo≤4 at h
        simp only [y,RealRaw.ofRat,RealRaw.scaleRat,RealRaw.scaleRatCompute,
          if_pos (show (0:Rat)≤1/2 by decide +kernel)]
        grind only
      let Y : Scalar := ⟨imaginaryAxis y,imaginaryAxis_valid hy⟩
      have hp := imaginary_exponential_upper_of_bounds y hy hyl hyu
      have hn := entireExponential_nat_multiple Y 2
      have hc : ((2:Nat):Rat)=(2:Rat) := by decide +kernel
      rw [hc] at hn
      have hscale : (scaleRat 2 Y.val).Equiv (imaginaryAxis x) := by
        intro n
        have ho := RealRaw.interval_order_of_valid x hx n
        apply (compareAt_overlap_iff _ _ n n).mpr
        simp only [Y,y,scaleRat,imaginaryAxis,mulI,ofRealRaw,RealRaw.scaleRat,
          RealRaw.scaleRatCompute,QBox.scaleRat,if_pos (show (0:Rat)≤2 by decide +kernel),
          if_pos (show (0:Rat)≤1/2 by decide +kernel),Rat.neg_zero,Rat.mul_zero,
          QBox.Overlaps,QComplex.le_def]
        constructor <;> constructor <;> grind only
      have hpow : (LocalODE.power (entireExponentialValue Y).val 2).Equiv one :=
        equiv_trans (LocalODE.power_valid _ (entireExponentialValue Y).property 2)
          (entireExponentialValue ⟨scaleRat 2 Y.val,scaleRat_valid Y.property⟩).property (ofQComplex_valid _)
          (equiv_symm hn)
          (equiv_trans (entireExponentialValue ⟨scaleRat 2 Y.val,scaleRat_valid Y.property⟩).property
            (entireExponentialValue ⟨imaginaryAxis x,imaginaryAxis_valid hx⟩).property (ofQComplex_valid _)
            (entireExponentialValue_congr _ _ hscale) he)
      exact False.elim (upper_square_ne_one (entireExponentialValue Y) hp hpow)

/-- A kernel angle anywhere in [-4,4] is exactly zero. -/
theorem entireExponential_imaginary_kernel_four (x : RealRaw) (hx : x.Valid)
    (hl : (RealRaw.ofRat (-4)).Le x) (hu : x.Le (RealRaw.ofRat 4))
    (he : (entireExponentialValue ⟨imaginaryAxis x,imaginaryAxis_valid hx⟩).val.Equiv one) :
    x.Equiv (RealRaw.ofRat 0) := by
  rcases representedReal_le_total (RealRaw.ofRat 0) x
    (show (RealRaw.ofRat 0).Valid from RealRaw.ofRat_valid 0) hx with hp | hn
  · exact entireExponential_imaginary_kernel_nonnegative_four x hx hp hu he
  · let y := RealRaw.neg x
    have hy := RealRaw.neg_valid hx
    have hyl : (RealRaw.ofRat 0).Le y := by
      intro n m
      have h := hn m 0
      change (x.compute m).lo≤0 at h
      change 0≤ -(x.compute m).lo
      grind only
    have hyu : y.Le (RealRaw.ofRat 4) := by
      intro n m
      have h := hl 0 n
      change -4≤(x.compute n).hi at h
      change -(x.compute n).hi≤4
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
        (ofQComplex_valid _) (entireExponentialValue_congr _ _ hneg)
        (entireExponential_kernel_neg ⟨imaginaryAxis x,imaginaryAxis_valid hx⟩ he)
    have hz := entireExponential_imaginary_kernel_nonnegative_four y hy hyl hyu hey
    intro n
    have h := (RealRaw.compareAt_overlap_iff _ _ n n).mp (hz n)
    apply (RealRaw.compareAt_overlap_iff _ _ n n).mpr
    change -(x.compute n).hi≤0 ∧ 0≤ -(x.compute n).lo at h
    change (x.compute n).lo≤0 ∧ 0≤(x.compute n).hi
    grind only

/-- Every actual exponential kernel element whose imaginary coordinate lies
in [-4,4] is exactly zero. Its real coordinate is proved zero internally. -/
theorem entireExponential_kernel_four_strip (z : Scalar)
    (hl : (RealRaw.ofRat (-4)).Le z.val.imagPart)
    (hu : z.val.imagPart.Le (RealRaw.ofRat 4))
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
  have hi := entireExponential_imaginary_kernel_four z.val.imagPart (imagPart_valid z.property) hl hu
    (equiv_trans (entireExponentialValue ⟨imaginaryAxis z.val.imagPart,imaginaryAxis_valid (imagPart_valid z.property)⟩).property
      (entireExponentialValue z).property (ofQComplex_valid _) (equiv_symm hphase) he)
  intro n
  have hR := (RealRaw.compareAt_overlap_iff _ _ n n).mp (hr n)
  have hI := (RealRaw.compareAt_overlap_iff _ _ n n).mp (hi n)
  apply (compareAt_overlap_iff _ _ n n).mpr
  exact ⟨⟨hR.1,hI.1⟩,⟨hR.2,hI.2⟩⟩

end ComputableAnalysis.ModularForms
