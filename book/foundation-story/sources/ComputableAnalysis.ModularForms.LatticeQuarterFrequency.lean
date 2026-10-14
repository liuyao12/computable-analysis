import ComputableAnalysis.ModularForms.LatticeFrequencySquareBounds

/-! A tighter rational radicand name and its agreement with the actual lattice frequency. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert

 def latticeQuarterGuard : QInterval := ⟨4,16⟩

def latticeQuarterRadicand : RealRaw where
  compute := fun n => QInterval.intersection (latticeFrequencySquare.compute n) latticeQuarterGuard

theorem latticeQuarterRadicand_ordered (n : Nat) :
    (latticeQuarterRadicand.compute n).lo≤(latticeQuarterRadicand.compute n).hi := by
  have hw := latticeFrequencySquare_valid.1 n
  have ho : (latticeFrequencySquare.compute n).lo≤(latticeFrequencySquare.compute n).hi := by
    change 0≤(latticeFrequencySquare.compute n).hi-(latticeFrequencySquare.compute n).lo at hw
    grind only
  exact QInterval.intersection_ordered_of_overlaps ho (by decide +kernel)
    (latticeFrequencySquare_quarter_guard_overlap n)

theorem latticeQuarterRadicand_valid : latticeQuarterRadicand.Valid := by
  refine ⟨?_,?_,?_⟩
  · intro n
    have h := latticeQuarterRadicand_ordered n
    change 0≤(latticeQuarterRadicand.compute n).hi-(latticeQuarterRadicand.compute n).lo
    grind only
  · intro n m hnm
    have h := latticeFrequencySquare_valid.2.1 n m hnm
    have ho := latticeQuarterRadicand_ordered m
    change max (latticeFrequencySquare.compute n).lo 4≤max (latticeFrequencySquare.compute m).lo 4 ∧
      max (latticeFrequencySquare.compute m).lo 4≤min (latticeFrequencySquare.compute m).hi 16 ∧
      min (latticeFrequencySquare.compute m).hi 16≤min (latticeFrequencySquare.compute n).hi 16
    constructor
    · grind
    · exact ⟨ho,by grind⟩
  · intro eps
    obtain ⟨N,hN⟩ := latticeFrequencySquare_valid.2.2 eps
    refine ⟨N,?_⟩
    intro n hn
    have h := hN n hn
    have hc := QInterval.intersection_contained_left (latticeFrequencySquare.compute n) latticeQuarterGuard
    change (latticeQuarterRadicand.compute n).hi-(latticeQuarterRadicand.compute n).lo≤eps.val
    change (latticeFrequencySquare.compute n).hi-(latticeFrequencySquare.compute n).lo≤eps.val at h
    change (latticeFrequencySquare.compute n).lo≤(latticeQuarterRadicand.compute n).lo ∧
      (latticeQuarterRadicand.compute n).hi≤(latticeFrequencySquare.compute n).hi at hc
    grind only

theorem latticeQuarterRadicand_equiv : latticeQuarterRadicand.Equiv latticeFrequencySquare := by
  intro n
  apply (RealRaw.compareAt_overlap_iff _ _ n n).2
  have h := latticeQuarterRadicand_ordered n
  have hc := QInterval.intersection_contained_left (latticeFrequencySquare.compute n) latticeQuarterGuard
  exact ⟨Rat.le_trans h hc.2,Rat.le_trans hc.1 h⟩

def latticeQuarterFrequencyInput : RepresentedPositiveSquareRoot.PositiveInput 31 1 where
  raw := latticeQuarterRadicand
  valid := latticeQuarterRadicand_valid
  margin_pos := by decide +kernel
  center_le_bound := by
    intro n
    have h := (QInterval.midpoint_mem (latticeQuarterRadicand_ordered n)).2
    have hg := (QInterval.intersection_contained_right (latticeFrequencySquare.compute n) latticeQuarterGuard).2
    have ht : (16:Rat)≤31 := by decide +kernel
    exact Rat.le_trans (Rat.le_trans h hg) ht
  margin_sq_le_center := by
    intro n
    have h := (QInterval.midpoint_mem (latticeQuarterRadicand_ordered n)).1
    have hg := (QInterval.intersection_contained_right (latticeFrequencySquare.compute n) latticeQuarterGuard).1
    have he : sq (1:Rat)=1 := by decide +kernel
    rw [he]
    have ht : (1:Rat)≤4 := by decide +kernel
    exact Rat.le_trans ht (Rat.le_trans hg h)


def latticeQuarterFrequency : Scalar :=
  ⟨RepresentedPositiveSquareRoot.PositiveInput.awayRootRaw latticeQuarterFrequencyInput,
    RepresentedPositiveSquareRoot.PositiveInput.awayRootRaw_valid latticeQuarterFrequencyInput⟩

theorem latticeQuarterRadicand_original_agreement :
    latticeQuarterRadicand.Equiv latticeFrequencyRadicand :=
  RealRaw.equiv_trans latticeQuarterRadicand_valid latticeFrequencySquare_valid latticeFrequencyRadicand_valid
    latticeQuarterRadicand_equiv (RealRaw.equiv_symm latticeFrequencyRadicand_equiv)

theorem latticeQuarterFrequency_agreement : latticeQuarterFrequency.val.Equiv latticeFrequency.val := by
  let A := latticeQuarterFrequencyInput
  let B := latticeFrequencyInput
  have ha := RepresentedPositiveSquareRoot.PositiveInput.awayRootRaw_equiv_sqrtComplex A
  have hb := RepresentedPositiveSquareRoot.PositiveInput.awayRootRaw_equiv_sqrtComplex B
  have hc := RepresentedPositiveSquareRoot.PositiveInput.sqrtComplex_equiv_of_input_equiv A B
    latticeQuarterRadicand_original_agreement
  exact equiv_trans latticeQuarterFrequency.property
    (RepresentedPositiveSquareRoot.PositiveInput.sqrtComplex_valid A) latticeFrequency.property ha
    (equiv_trans (RepresentedPositiveSquareRoot.PositiveInput.sqrtComplex_valid A)
      (RepresentedPositiveSquareRoot.PositiveInput.sqrtComplex_valid B) latticeFrequency.property hc (equiv_symm hb))

theorem latticeQuarterFrequency_guard_overlap (n : Nat) :
    (latticeQuarterFrequency.val.realPart.compute n).Overlaps (⟨2,4⟩ : QInterval) := by
  let k := n+RepresentedPositiveSquareRoot.PositiveInput.guardShift 31 1
  let I := RepresentedPositiveSquareRoot.PositiveInput.approximation latticeQuarterFrequencyInput k
  have hs := RepresentedPositiveSquareRoot.PositiveInput.approximation_spec latticeQuarterFrequencyInput k
  have hc := RepresentedPositiveSquareRoot.PositiveInput.awayRootRaw_contains_shifted_approximation latticeQuarterFrequencyInput n
  have hm := QInterval.midpoint_mem (latticeQuarterRadicand_ordered k)
  have hg := QInterval.intersection_contained_right (latticeFrequencySquare.compute k) latticeQuarterGuard
  have hlo : (4:Rat)≤(latticeQuarterRadicand.compute k).midpoint := Rat.le_trans hg.1 hm.1
  have hhi : (latticeQuarterRadicand.compute k).midpoint≤16 := Rat.le_trans hm.2 hg.2
  have hil : I.lo≤4 := by
    apply le_of_sq_le_sq_of_nonneg_right (by decide +kernel : (0:Rat)≤4)
    have he : (16:Rat)=sq (4:Rat) := by decide +kernel
    rw [←he]
    exact Rat.le_trans hs.2.2.1 hhi
  have hih : (2:Rat)≤I.hi := by
    apply le_of_sq_le_sq_of_nonneg_right (Rat.le_trans hs.1 hs.2.1)
    have he : sq (2:Rat)=4 := by decide +kernel
    rw [he]
    exact Rat.le_trans hlo hs.2.2.2
  simp only [QBox.NestedIn,QComplex.le_def] at hc
  have hl := hc.1.1
  have hh := hc.2.1
  change (latticeQuarterFrequency.val.compute n).lo.re≤I.lo at hl
  change I.hi≤(latticeQuarterFrequency.val.compute n).hi.re at hh
  exact ⟨Rat.le_trans hl hil,Rat.le_trans hih hh⟩

end ComputableAnalysis.ModularForms
