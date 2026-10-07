import ComputableAnalysis.ModularForms.LatticeRiccatiRealConstant
import ComputableAnalysis.RepresentedPositiveSquareRoot

/-! A finite reboxing algorithm for the positive lattice frequency radicand. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert

def latticeFrequencyGuard : QInterval := ⟨1,31⟩

theorem latticeFrequencySquare_guard_overlap (n : Nat) :
    (latticeFrequencySquare.compute n).Overlaps latticeFrequencyGuard := by
  have hl := (pairedRiccatiCenterConstant_prefix_error 0).1 0 n
  have hu := (pairedRiccatiCenterConstant_prefix_error 7).2.1 n 0
  change -(24*(1:Rat)⁻¹)≤(pairedRiccatiCenterConstant.val.compute n).hi.re+ -(3*pairedZeroSquarePrefix 1) at hl
  change (pairedRiccatiCenterConstant.val.compute n).lo.re+ -(3*pairedZeroSquarePrefix 8)≤24*(8:Rat)⁻¹ at hu
  have hp : 3*pairedZeroSquarePrefix 1= -6 := by decide +kernel
  have hq : 3*pairedZeroSquarePrefix 8+24*(8:Rat)⁻¹≤ -3 := by decide +kernel
  have hone : -(24*(1:Rat)⁻¹)= -24 := by decide +kernel
  rw [hp,hone] at hl
  change -(pairedRiccatiCenterConstant.val.compute n).hi.re≤31 ∧
    1≤ -(pairedRiccatiCenterConstant.val.compute n).lo.re
  constructor <;> grind only

def latticeFrequencyRadicand : RealRaw where
  compute := fun n => QInterval.intersection (latticeFrequencySquare.compute n) latticeFrequencyGuard

theorem latticeFrequencyRadicand_ordered (n : Nat) :
    (latticeFrequencyRadicand.compute n).lo≤(latticeFrequencyRadicand.compute n).hi := by
  have hw := latticeFrequencySquare_valid.1 n
  have ho : (latticeFrequencySquare.compute n).lo≤(latticeFrequencySquare.compute n).hi := by
    change 0≤(latticeFrequencySquare.compute n).hi-(latticeFrequencySquare.compute n).lo at hw
    grind only
  exact QInterval.intersection_ordered_of_overlaps ho (by decide +kernel)
    (latticeFrequencySquare_guard_overlap n)

theorem latticeFrequencyRadicand_valid : latticeFrequencyRadicand.Valid := by
  refine ⟨?_,?_,?_⟩
  · intro n
    have h := latticeFrequencyRadicand_ordered n
    change 0≤(latticeFrequencyRadicand.compute n).hi-(latticeFrequencyRadicand.compute n).lo
    grind only
  · intro n m hnm
    have h := latticeFrequencySquare_valid.2.1 n m hnm
    have ho := latticeFrequencyRadicand_ordered m
    change max (latticeFrequencySquare.compute n).lo 1≤max (latticeFrequencySquare.compute m).lo 1 ∧
      max (latticeFrequencySquare.compute m).lo 1≤min (latticeFrequencySquare.compute m).hi 31 ∧
      min (latticeFrequencySquare.compute m).hi 31≤min (latticeFrequencySquare.compute n).hi 31
    constructor
    · grind
    · exact ⟨ho,by grind⟩
  · intro eps
    obtain ⟨N,hN⟩ := latticeFrequencySquare_valid.2.2 eps
    refine ⟨N,?_⟩
    intro n hn
    have h := hN n hn
    have hc := QInterval.intersection_contained_left (latticeFrequencySquare.compute n) latticeFrequencyGuard
    change (latticeFrequencyRadicand.compute n).hi-(latticeFrequencyRadicand.compute n).lo≤eps.val
    change (latticeFrequencySquare.compute n).hi-(latticeFrequencySquare.compute n).lo≤eps.val at h
    change (latticeFrequencySquare.compute n).lo≤(latticeFrequencyRadicand.compute n).lo ∧
      (latticeFrequencyRadicand.compute n).hi≤(latticeFrequencySquare.compute n).hi at hc
    grind only

theorem latticeFrequencyRadicand_equiv : latticeFrequencyRadicand.Equiv latticeFrequencySquare := by
  intro n
  apply (RealRaw.compareAt_overlap_iff _ _ n n).2
  have h := latticeFrequencyRadicand_ordered n
  have hc := QInterval.intersection_contained_left (latticeFrequencySquare.compute n) latticeFrequencyGuard
  exact ⟨Rat.le_trans h hc.2,Rat.le_trans hc.1 h⟩

def latticeFrequencyInput : RepresentedPositiveSquareRoot.PositiveInput 31 1 where
  raw := latticeFrequencyRadicand
  valid := latticeFrequencyRadicand_valid
  margin_pos := by decide +kernel
  center_le_bound := by
    intro n
    have h := (QInterval.midpoint_mem (latticeFrequencyRadicand_ordered n)).2
    have hg := (QInterval.intersection_contained_right (latticeFrequencySquare.compute n) latticeFrequencyGuard).2
    exact Rat.le_trans h hg
  margin_sq_le_center := by
    intro n
    have h := (QInterval.midpoint_mem (latticeFrequencyRadicand_ordered n)).1
    have hg := (QInterval.intersection_contained_right (latticeFrequencySquare.compute n) latticeFrequencyGuard).1
    have he : sq (1:Rat)=1 := by decide +kernel
    rw [he]
    exact Rat.le_trans hg h

def latticeFrequency : Scalar :=
  ⟨RepresentedPositiveSquareRoot.PositiveInput.awayRootRaw latticeFrequencyInput,
    RepresentedPositiveSquareRoot.PositiveInput.awayRootRaw_valid latticeFrequencyInput⟩

theorem latticeFrequency_square_identity :
    (mul latticeFrequency.val latticeFrequency.val).Equiv (ofRealRaw latticeFrequencySquare) :=
  equiv_trans (mul_valid latticeFrequency.property latticeFrequency.property)
    (ofRealRaw_valid latticeFrequencyRadicand latticeFrequencyRadicand_valid)
    (ofRealRaw_valid latticeFrequencySquare latticeFrequencySquare_valid)
    (RepresentedPositiveSquareRoot.PositiveInput.awayRootRaw_square_equiv_raw latticeFrequencyInput)
    (ofRealRaw_equiv_of_equiv latticeFrequencyRadicand_valid latticeFrequencySquare_valid
      latticeFrequencyRadicand_equiv)

theorem latticeFrequency_positive : latticeFrequency.val.realPart.Pos := by
  have h := RepresentedPositiveSquareRoot.PositiveInput.awayRootRaw_nested_guard latticeFrequencyInput 0
  change QBox.NestedIn _ _ at h
  simp only [QBox.NestedIn,QComplex.le_def] at h
  have hl := h.1.1
  change (1:Rat)/2≤(latticeFrequency.val.compute 0).lo.re at hl
  refine ⟨0,?_⟩
  change 0<(latticeFrequency.val.compute 0).lo.re
  generalize (latticeFrequency.val.compute 0).lo.re=r at hl ⊢
  grind only

end ComputableAnalysis.ModularForms
