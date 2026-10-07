import ComputableAnalysis.ModularForms.PairedEntireRiccatiPeriodicity

/-! Executable integer translation into a fixed strip, without choosing a real floor. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

def stripBoxRecognized (z : Scalar) (N : Nat) : Bool :=
  decide ((z.val.compute N).width ≤ 1)

theorem stripBoxRecognized_eventually (z : Scalar) :
    ∃ M, ∀ N, M≤N → stripBoxRecognized z N=true := by
  obtain ⟨M,hM⟩ := z.property.2.2 ⟨1,by decide +kernel⟩
  exact ⟨M,fun N hN => by simpa only [stripBoxRecognized,decide_eq_true_eq] using (hM N hN).1⟩

def stripBoxStage (z : Scalar) : Nat :=
  PrecisionSearch.firstFrom (stripBoxRecognized z) (stripBoxRecognized_eventually z) 0

def stripTranslation (z : Scalar) : Int := -((z.val.compute (stripBoxStage z)).lo.re.floor)

def stripRepresentative (z : Scalar) : Scalar := integerShiftScalar z (stripTranslation z)

theorem stripRepresentative_real_bounds (z : Scalar) :
    RealRaw.Le (RealRaw.ofRat 0) (stripRepresentative z).val.realPart ∧
      RealRaw.Le (stripRepresentative z).val.realPart (RealRaw.ofRat 2) := by
  let N := stripBoxStage z
  let a := (z.val.compute N).lo.re
  have hw : (z.val.compute N).width ≤ 1 := by
    exact of_decide_eq_true (PrecisionSearch.firstFrom_spec (stripBoxRecognized z)
      (stripBoxRecognized_eventually z) 0).2
  have hf := Rat.floor_le a
  have ht := Rat.lt_floor_add_one a
  have hv := realPart_valid z.property
  have ho (n : Nat) := (RealRaw.compareAt_overlap_iff z.val.realPart z.val.realPart N n).mp
    (RealRaw.allStagesOverlap_refl _ hv N n)
  constructor
  · intro m n
    have hh := (ho n).1
    change a ≤ (z.val.compute n).hi.re at hh
    change 0 ≤ ((stripRepresentative z).val.realPart.compute n).hi
    simp only [stripRepresentative,stripTranslation,integerShiftScalar,integerAffine,
      translate,scaleRat,QBox.scaleRat,realPart,add,ofQComplex,QBox.add,QComplex.add,
      Rat.intCast_one,if_pos (show (0:Rat)≤1 by decide),Rat.one_mul,Rat.intCast_neg]
    change 0 ≤ (z.val.compute n).hi.re + -(a.floor:Rat)
    grind only
  · intro n m
    have hh := (ho n).2
    change (z.val.compute n).lo.re ≤ (z.val.compute N).hi.re at hh
    change ((stripRepresentative z).val.realPart.compute n).lo ≤ 2
    simp only [stripRepresentative,stripTranslation,integerShiftScalar,integerAffine,
      translate,scaleRat,QBox.scaleRat,realPart,add,ofQComplex,QBox.add,QComplex.add,
      Rat.intCast_one,if_pos (show (0:Rat)≤1 by decide),Rat.one_mul,Rat.intCast_neg]
    change (z.val.compute n).lo.re + -(a.floor:Rat) ≤ 2
    change (z.val.compute N).hi.re-a ≤ 1 at hw
    rw [Rat.intCast_add,Rat.intCast_one] at ht
    grind only

theorem pairedEntireRiccatiMap_strip_agreement (z : Scalar) :
    (pairedEntireRiccatiMap.eval (stripRepresentative z) trivial).val.Equiv
      (pairedEntireRiccatiMap.eval z trivial).val :=
  pairedEntireRiccatiMap_period_int (stripTranslation z) z

theorem stripRepresentative_imaginary_agreement (z : Scalar) :
    (stripRepresentative z).val.imagPart.Equiv z.val.imagPart := by
  intro n
  apply (RealRaw.compareAt_overlap_iff _ _ n n).mpr
  have hi := (imagPart_valid z.property).1 n
  change 0 ≤ (z.val.compute n).hi.im-(z.val.compute n).lo.im at hi
  simp only [stripRepresentative,integerShiftScalar,integerAffine,translate,scaleRat,
    QBox.scaleRat,imagPart,add,ofQComplex,QBox.add,QComplex.add,Rat.intCast_one,
    if_pos (show (0:Rat)≤1 by decide),Rat.one_mul,Rat.add_zero,QInterval.Overlaps]
  constructor <;> grind only

theorem pairedEntireRiccatiMap_bound_of_strip_bound (C : Rat)
    (hb : ∀ w : Scalar, RealRaw.Le (RealRaw.ofRat 0) w.val.realPart →
      RealRaw.Le w.val.realPart (RealRaw.ofRat 2) →
      Small (pairedEntireRiccatiMap.eval w trivial).val C) (z : Scalar) :
    Small (pairedEntireRiccatiMap.eval z trivial).val C :=
  Small.congr (pairedEntireRiccatiMap.eval (stripRepresentative z) trivial).property
    (pairedEntireRiccatiMap.eval z trivial).property
    (pairedEntireRiccatiMap_strip_agreement z)
    (hb (stripRepresentative z) (stripRepresentative_real_bounds z).1
      (stripRepresentative_real_bounds z).2)

end ComputableAnalysis.ModularForms
