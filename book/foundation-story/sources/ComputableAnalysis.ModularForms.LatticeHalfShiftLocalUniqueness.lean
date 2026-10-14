import ComputableAnalysis.ModularForms.HomogeneousLocalUniqueness
import ComputableAnalysis.ModularForms.LatticeHalfShiftLocalCoefficient
import ComputableAnalysis.ModularForms.DomainSegmentBisection

/-! Actual local equality by segment linearization and rational contraction. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions
set_option maxHeartbeats 2000000

noncomputable def latticeHalfShiftDifference_centerContinuous :
    ContinuousAt latticeHalfShiftDifferenceMap pairedZeroScalar latticeHalfShiftDifference_zero_mem :=
  (latticeHalfShiftDifferenceMap_holomorphic.atPoint pairedZeroScalar latticeHalfShiftDifference_zero_mem).continuousAt

noncomputable def latticeHalfShiftUniquenessRadius : QPos :=
  minRadius latticeHalfShiftComparisonRadius
    (minRadius (latticeHalfShiftDifference_centerContinuous.delta unitError) ⟨1/16,by decide +kernel⟩)

def latticeHalfShiftLocalDomain (z : Scalar) : Prop :=
  Small (sub z.val pairedZeroScalar.val) latticeHalfShiftUniquenessRadius.val

theorem latticeHalfShiftLocal_mem (z : Scalar) (hz : latticeHalfShiftLocalDomain z) :
    latticeHalfShiftDifferenceMap.domain z :=
  latticeHalfShiftComparison_mem z (hz.mono (minRadius_left _ _))

theorem latticeHalfShiftLocal_origin : latticeHalfShiftLocalDomain pairedZeroScalar := by
  exact Small.congr (ofQComplex_valid _) (sub_valid pairedZeroScalar.property pairedZeroScalar.property)
    (by
      apply ComplexRawQuotient.equiv_of_ofRaw_eq
        (hleft := ofQComplex_valid _) (hright := sub_valid pairedZeroScalar.property pairedZeroScalar.property)
      change (0:ScalarAlgebra.Value)=0-0
      grind only)
    (Small.zero (Rat.le_of_lt latticeHalfShiftUniquenessRadius.property))

theorem latticeHalfShiftLocal_segment (z : Scalar) (hz : latticeHalfShiftLocalDomain z)
    (t : UnitInterval.Point) :
    latticeHalfShiftLocalDomain (RepresentedAffineSegment.point pairedZeroScalar z t) :=
  RepresentedAffineSegment.offset_bound pairedZeroScalar pairedZeroScalar z t _
    latticeHalfShiftLocal_origin hz

theorem latticeHalfShiftLocal_initial_bound (z : Scalar) (hz : latticeHalfShiftLocalDomain z) :
    Small (latticeHalfShiftDifferenceMap.eval z (latticeHalfShiftLocal_mem z hz)).val 1 := by
  have hr := latticeHalfShiftDifference_centerContinuous.estimate unitError z (latticeHalfShiftLocal_mem z hz)
    (hz.mono (Rat.le_trans (minRadius_right _ _) (minRadius_left _ _)))
  have he : (sub (latticeHalfShiftDifferenceMap.eval z (latticeHalfShiftLocal_mem z hz)).val
      (latticeHalfShiftDifferenceMap.eval pairedZeroScalar latticeHalfShiftDifference_zero_mem).val).Equiv
      (latticeHalfShiftDifferenceMap.eval z (latticeHalfShiftLocal_mem z hz)).val := by
    have h0 := ComplexRawQuotient.ofRaw_eq_ofRaw
      (hleft := (latticeHalfShiftDifferenceMap.eval pairedZeroScalar latticeHalfShiftDifference_zero_mem).property)
      (hright := ofQComplex_valid _) (latticeHalfShiftDifference_center pairedZeroScalar
        latticeHalfShiftDifference_zero_mem (equiv_refl _ (ofQComplex_valid _)))
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := sub_valid (latticeHalfShiftDifferenceMap.eval z (latticeHalfShiftLocal_mem z hz)).property
        (latticeHalfShiftDifferenceMap.eval pairedZeroScalar latticeHalfShiftDifference_zero_mem).property)
      (hright := (latticeHalfShiftDifferenceMap.eval z (latticeHalfShiftLocal_mem z hz)).property)
    let F := gridScalarValue (latticeHalfShiftDifferenceMap.eval z (latticeHalfShiftLocal_mem z hz))
    let Z := gridScalarValue (latticeHalfShiftDifferenceMap.eval pairedZeroScalar latticeHalfShiftDifference_zero_mem)
    change Z=0 at h0
    change F-Z=F
    rw [h0]
    grind only
  exact Small.congr (sub_valid (latticeHalfShiftDifferenceMap.eval z (latticeHalfShiftLocal_mem z hz)).property
    (latticeHalfShiftDifferenceMap.eval pairedZeroScalar latticeHalfShiftDifference_zero_mem).property)
    (latticeHalfShiftDifferenceMap.eval z (latticeHalfShiftLocal_mem z hz)).property he hr

theorem latticeHalfShiftLocal_contract (B : Rat) (hB : 0<B)
    (hb : ∀ z hz, Small (latticeHalfShiftDifferenceMap.eval z (latticeHalfShiftLocal_mem z hz)).val B)
    (z : Scalar) (hz : latticeHalfShiftLocalDomain z) :
    Small (latticeHalfShiftDifferenceMap.eval z (latticeHalfShiftLocal_mem z hz)).val (B/2) := by
  let W := latticeHalfShiftUniquenessRadius
  let eps : QPos := ⟨2*B,Rat.mul_pos (by decide +kernel) hB⟩
  let hdom := fun t => latticeHalfShiftLocal_mem _ (latticeHalfShiftLocal_segment z hz t)
  have hder (t : UnitInterval.Point) :
      Small (sub (latticeHalfShiftDifferenceMap_holomorphic.derivative
        (RepresentedAffineSegment.point pairedZeroScalar z t) (hdom t)).val zero) eps.val := by
    let w := RepresentedAffineSegment.point pairedZeroScalar z t
    let hw := latticeHalfShiftLocal_segment z hz t
    have hc := latticeHalfShiftCoefficient_local_bound w (hdom t) (hw.mono (minRadius_left _ _))
    have hm := Small.mul (latticeHalfShiftCoefficientMap.eval w (hdom t)).property
      (latticeHalfShiftDifferenceMap.eval w (hdom t)).property (by decide +kernel : (0:Rat)≤1)
      (Rat.le_of_lt hB) hc (hb w hw)
    have hd := Small.congr
      (mul_valid (latticeHalfShiftCoefficientMap.eval w (hdom t)).property
        (latticeHalfShiftDifferenceMap.eval w (hdom t)).property)
      (latticeHalfShiftDifferenceMap_holomorphic.derivative w (hdom t)).property
      (equiv_symm (latticeHalfShiftDifference_coefficient_equation w (hdom t))) hm
    have hs := SeriesLimitLaws.small_sub hd (Small.zero (by decide +kernel : (0:Rat)≤0))
    simpa only [Rat.mul_one,Rat.one_mul,Rat.add_zero] using hs
  have hr := domainSegment_remainder_bound latticeHalfShiftDifferenceMap
    latticeHalfShiftDifferenceMap_holomorphic pairedZeroScalar z ⟨zero,ofQComplex_valid _⟩
    latticeHalfShiftDifference_zero_mem (latticeHalfShiftLocal_mem z hz) W eps hdom hz hder
  have he : (DomainFunctions.remainder latticeHalfShiftDifferenceMap pairedZeroScalar
      latticeHalfShiftDifference_zero_mem ⟨zero,ofQComplex_valid _⟩ z (latticeHalfShiftLocal_mem z hz)).Equiv
      (latticeHalfShiftDifferenceMap.eval z (latticeHalfShiftLocal_mem z hz)).val := by
    have h0 := ComplexRawQuotient.ofRaw_eq_ofRaw
      (hleft := (latticeHalfShiftDifferenceMap.eval pairedZeroScalar latticeHalfShiftDifference_zero_mem).property)
      (hright := ofQComplex_valid _) (latticeHalfShiftDifference_center pairedZeroScalar
        latticeHalfShiftDifference_zero_mem (equiv_refl _ (ofQComplex_valid _)))
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := DomainFunctions.remainder_valid _ _ _ _ _ _)
      (hright := (latticeHalfShiftDifferenceMap.eval z (latticeHalfShiftLocal_mem z hz)).property)
    let F := gridScalarValue (latticeHalfShiftDifferenceMap.eval z (latticeHalfShiftLocal_mem z hz))
    let Z := gridScalarValue (latticeHalfShiftDifferenceMap.eval pairedZeroScalar latticeHalfShiftDifference_zero_mem)
    let X := gridScalarValue z
    change Z=0 at h0
    change (F-Z)-0*(X-0)=F
    rw [h0]
    grind only
  have hs := Small.congr (DomainFunctions.remainder_valid _ _ _ _ _ _)
    (latticeHalfShiftDifferenceMap.eval z (latticeHalfShiftLocal_mem z hz)).property he hr
  apply hs.mono
  have hradius : W.val≤(1:Rat)/16 := Rat.le_trans (minRadius_right _ _) (minRadius_right _ _)
  have hm := Rat.mul_le_mul_of_nonneg_left hradius (Rat.le_of_lt hB)
  dsimp [eps]
  grind only

theorem latticeHalfShiftLocal_geometric_bound (n : Nat) :
    ∀ z hz, Small (latticeHalfShiftDifferenceMap.eval z (latticeHalfShiftLocal_mem z hz)).val
      (((1:Rat)/2)^n) := by
  induction n with
  | zero => intro z hz; simpa only [Rat.pow_zero] using latticeHalfShiftLocal_initial_bound z hz
  | succ n ih =>
    intro z hz
    have hs := latticeHalfShiftLocal_contract _ (Rat.pow_pos (by decide +kernel)) ih z hz
    have he : (((1:Rat)/2)^n)/2=((1:Rat)/2)^(n+1) := by
      rw [Rat.pow_succ,Rat.div_def]
      have hc : (2:Rat)⁻¹=(1:Rat)/2 := by decide +kernel
      rw [hc]
    rw [he] at hs
    exact hs

theorem latticeHalfShiftLocal_difference_zero (z : Scalar) (hz : latticeHalfShiftLocalDomain z) :
    (latticeHalfShiftDifferenceMap.eval z (latticeHalfShiftLocal_mem z hz)).val.Equiv zero := by
  apply HomogeneousLocalUniqueness.zero_on latticeHalfShiftDifferenceMap
    latticeHalfShiftDifferenceMap_holomorphic pairedZeroScalar latticeHalfShiftDifference_zero_mem
    latticeHalfShiftUniquenessRadius latticeHalfShiftLocal_mem latticeHalfShiftCoefficientMap.eval
    1 (by decide +kernel)
    (by
      have hr : latticeHalfShiftUniquenessRadius.val≤(1:Rat)/16 :=
        Rat.le_trans (minRadius_right _ _) (minRadius_right _ _)
      grind only)
    (fun w hw => latticeHalfShiftCoefficient_local_bound w (latticeHalfShiftLocal_mem w hw)
      (hw.mono (minRadius_left _ _)))
    latticeHalfShiftDifference_coefficient_equation
    (latticeHalfShiftDifference_center pairedZeroScalar latticeHalfShiftDifference_zero_mem
      (equiv_refl _ (ofQComplex_valid _)))
    unitError latticeHalfShiftLocal_initial_bound z hz

theorem latticeHalfShiftLocal_agreement (z : Scalar) (hz : latticeHalfShiftLocalDomain z) :
    (shiftedLatticeKernelMap.eval z (latticeHalfShiftLocal_mem z hz).1).val.Equiv
      (scaledLatticeReciprocalMap.eval z (latticeHalfShiftLocal_mem z hz).2).val := by
  let hm := latticeHalfShiftLocal_mem z hz
  have hd := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := (latticeHalfShiftDifferenceMap.eval z hm).property) (hright := ofQComplex_valid _)
    (latticeHalfShiftLocal_difference_zero z hz)
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (shiftedLatticeKernelMap.eval z hm.1).property)
    (hright := (scaledLatticeReciprocalMap.eval z hm.2).property)
  let Q := gridScalarValue (shiftedLatticeKernelMap.eval z hm.1)
  let S := gridScalarValue (scaledLatticeReciprocalMap.eval z hm.2)
  change Q+ -S=0 at hd
  change Q=S
  grind only

end ComputableAnalysis.ModularForms
