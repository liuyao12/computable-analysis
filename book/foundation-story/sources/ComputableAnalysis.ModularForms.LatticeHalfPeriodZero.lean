import ComputableAnalysis.ModularForms.PairedGlobalOffPoleIntegerPeriodicity
import ComputableAnalysis.ModularForms.PairedGlobalReflectionValue
import ComputableAnalysis.ModularForms.WeightedGridCellAgreement

/-! Exact half-period zero of the actual global lattice reciprocal series. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

def latticeHalfPoint : Scalar := ⟨ofQComplex ⟨1/2,0⟩,ofQComplex_valid _⟩

theorem latticeHalfPoint_mem : pairedOffPoleDomain latticeHalfPoint := by
  apply pairedOffPoleDomain_of_integer_nonzero
  intro k he
  have ho := (compareAt_overlap_iff (integerShiftScalar latticeHalfPoint k).val zero 0 0).1 (he 0)
  have hl := ho.2.1
  have hu := ho.1.1
  simp [integerShiftScalar,integerAffine,latticeHalfPoint,translate,scaleRat,ofQComplex,
    QBox.scaleRat,add,QBox.add,QComplex.add,zero,QComplex.zero] at hl hu
  cases k with
  | ofNat n =>
    have hn : (0:Rat)≤(Int.ofNat n:Rat) := Rat.intCast_nonneg.mpr (Int.natCast_nonneg n)
    grind only
  | negSucc n =>
    have hn : (0:Rat)≤(n:Rat) := Rat.natCast_nonneg
    have hc : ((Int.negSucc n):Rat)= -((n:Rat)+1) := by
      rw [show Int.negSucc n= -((n+1:Nat):Int) by omega]
      simp only [Rat.intCast_neg,Rat.intCast_natCast,Rat.natCast_add]
      rfl
    rw [hc] at hl
    grind only

theorem latticeHalfPoint_reflected_shift :
    (integerShiftScalar (pairedReflectionMap.eval latticeHalfPoint trivial) 1).val.Equiv
      latticeHalfPoint.val := by
  intro n
  apply (compareAt_overlap_iff _ _ n n).mpr
  change ((integerShiftScalar (pairedReflectionMap.eval latticeHalfPoint trivial) 1).val.compute 0).Overlaps
    (latticeHalfPoint.val.compute 0)
  decide +kernel

theorem globalOffPoleValue_halfPeriod_zero :
    (globalOffPoleValue latticeHalfPoint latticeHalfPoint_mem).Equiv zero := by
  let z := latticeHalfPoint
  let hz := latticeHalfPoint_mem
  let w := pairedReflectionMap.eval z trivial
  let hw := pairedOffPoleDomain_reflection z hz
  have hp := globalOffPoleClass_period_int w hw 1
  have hc := globalOffPoleClass_congr (integerShiftScalar w 1) z
    (pairedOffPoleDomain_shift w hw 1) hz latticeHalfPoint_reflected_shift
  have hr := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := globalOffPoleValue_valid w hw) (hright := neg_valid (globalOffPoleValue_valid z hz))
    (globalOffPoleValue_reflection z hz)
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := globalOffPoleValue_valid z hz) (hright := ofQComplex_valid _)
  let P := globalOffPoleClass z hz
  let Q := globalOffPoleClass w hw
  change Q= -P at hr
  change _=(0:ScalarAlgebra.Value)
  change P=0
  have he : P+P=0 := by grind only
  have hs := congrArg (ComplexRawQuotient.scaleRat (1/2)) he
  rw [←gridValue_scale_two,ComplexRawQuotient.scaleRat_scaleRat] at hs
  have ht : (1/2:Rat)*2=1 := by decide +kernel
  rw [ht,ComplexRawQuotient.scaleRat_one] at hs
  change P=ComplexRawQuotient.scaleRat (1/2) (0:ScalarAlgebra.Value) at hs
  exact hs.trans (by
    apply Quotient.sound
    intro n
    apply (compareAt_overlap_iff _ _ n n).mpr
    change ((scaleRat (1/2) zero).compute 0).Overlaps (zero.compute 0)
    decide +kernel)

end ComputableAnalysis.ModularForms
