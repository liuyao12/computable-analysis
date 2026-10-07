import ComputableAnalysis.ModularForms.PairedRiccatiConstantSeparation

/-! The actual lattice Riccati constant is real and strictly negative. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert

def latticeFrequencySquare : RealRaw := -pairedRiccatiCenterConstant.val.realPart

theorem latticeFrequencySquare_valid : latticeFrequencySquare.Valid :=
  RealRaw.neg_valid (realPart_valid pairedRiccatiCenterConstant.property)

theorem latticeFrequencySquare_positive : latticeFrequencySquare.Pos := by
  have hs := (pairedRiccatiCenterConstant_prefix_error 7).2.1
  obtain ⟨K,hK⟩ := (realPart_valid pairedRiccatiCenterConstant.property).2.2
    (⟨1,by decide +kernel⟩ : QPos)
  have hb := hs K 0
  have hw := hK K (Nat.le_refl _)
  change (pairedRiccatiCenterConstant.val.compute K).lo.re+ -(3*pairedZeroSquarePrefix 8)≤24*(8:Rat)⁻¹ at hb
  change (pairedRiccatiCenterConstant.val.compute K).hi.re-
    (pairedRiccatiCenterConstant.val.compute K).lo.re≤1 at hw
  have hp : 3*pairedZeroSquarePrefix 8+24*(8:Rat)⁻¹+1<0 := by decide +kernel
  refine ⟨K,?_⟩
  change 0< -(pairedRiccatiCenterConstant.val.compute K).hi.re
  grind only

theorem latticeRiccatiConstant_imaginary_zero :
    pairedRiccatiCenterConstant.val.imagPart.Equiv (RealRaw.ofRat 0) := by
  let z := ofRealRaw pairedRiccatiCenterConstant.val.imagPart
  have hb : ∀ N, Small z (24*((N+1:Nat):Rat)⁻¹) := by
    intro N
    have hs := pairedRiccatiCenterConstant_prefix_error N
    have hn : 0≤24*((N+1:Nat):Rat)⁻¹ :=
      Rat.mul_nonneg (by decide +kernel)
        (Rat.le_of_lt (Rat.inv_pos.mpr (by exact_mod_cast (show 0<N+1 by omega))))
    refine ⟨?_,?_,?_,?_⟩ <;> intro n m
    · have h := hs.2.2.1 n m
      change -(24*((N+1:Nat):Rat)⁻¹)≤(pairedRiccatiCenterConstant.val.compute m).hi.im
      simpa only [imagPart,RealRaw.ofRat,sub,add,neg,ofQComplex,QBox.add,QBox.neg,QComplex.add,QComplex.neg,Rat.neg_zero,Rat.add_zero] using h
    · have h := hs.2.2.2 n m
      change (pairedRiccatiCenterConstant.val.compute n).lo.im≤24*((N+1:Nat):Rat)⁻¹
      simpa only [imagPart,RealRaw.ofRat,sub,add,neg,ofQComplex,QBox.add,QBox.neg,QComplex.add,QComplex.neg,Rat.neg_zero,Rat.add_zero] using h
    · change -(24*((N+1:Nat):Rat)⁻¹)≤0; grind only
    · change 0≤24*((N+1:Nat):Rat)⁻¹; exact hn
  have hzero : Small z 0 := by
    apply SeriesLimitLaws.small_closed z 0 (fun N => 24*((N+1:Nat):Rat)⁻¹)
      (pairedReciprocalTail_shrinks 24)
    simpa only [Rat.zero_add] using hb
  intro n
  apply (RealRaw.compareAt_overlap_iff _ _ n n).2
  -- The real coordinate of the embedding is the original imaginary coordinate.
  have hl := hzero.1 n n
  have hh := hzero.2.1 n n
  change 0≤(pairedRiccatiCenterConstant.val.compute n).hi.im at hl
  change (pairedRiccatiCenterConstant.val.compute n).lo.im≤0 at hh
  exact ⟨hh,hl⟩

theorem latticeRiccatiConstant_real_embedding :
    pairedRiccatiCenterConstant.val.Equiv
      (ofRealRaw pairedRiccatiCenterConstant.val.realPart) := by
  intro n
  apply (compareAt_overlap_iff _ _ n n).2
  have hi := (RealRaw.compareAt_overlap_iff _ _ n n).mp (latticeRiccatiConstant_imaginary_zero n)
  have hr := (realPart_valid pairedRiccatiCenterConstant.property).1 n
  change (pairedRiccatiCenterConstant.val.compute n).lo.im≤0 ∧
    0≤(pairedRiccatiCenterConstant.val.compute n).hi.im at hi
  have ho : (pairedRiccatiCenterConstant.val.compute n).lo.re≤(pairedRiccatiCenterConstant.val.compute n).hi.re := by
    change 0≤(pairedRiccatiCenterConstant.val.compute n).hi.re-(pairedRiccatiCenterConstant.val.compute n).lo.re at hr
    grind only
  exact ⟨⟨ho,hi.1⟩,⟨ho,hi.2⟩⟩

end ComputableAnalysis.ModularForms
