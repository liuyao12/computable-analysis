import ComputableAnalysis.ModularForms.LatticeQuarterFrequency

/-! A bounded half-frequency name for the geometric rotation comparison. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert

def latticeQuarterRootReal : RealRaw := latticeQuarterFrequency.val.realPart

theorem latticeQuarterRootReal_valid : latticeQuarterRootReal.Valid := realPart_valid latticeQuarterFrequency.property

def latticeQuarterRootGuard : QInterval := ⟨2,4⟩

theorem latticeQuarterRootReal_guard_overlap (n : Nat) :
    (latticeQuarterRootReal.compute n).Overlaps latticeQuarterRootGuard := latticeQuarterFrequency_guard_overlap n

def latticeQuarterReboxedRoot : RealRaw where
  compute := fun n => QInterval.intersection (latticeQuarterRootReal.compute n) latticeQuarterRootGuard

theorem latticeQuarterReboxedRoot_ordered (n : Nat) :
    (latticeQuarterReboxedRoot.compute n).lo≤(latticeQuarterReboxedRoot.compute n).hi := by
  have hw := latticeQuarterRootReal_valid.1 n
  have ho : (latticeQuarterRootReal.compute n).lo≤(latticeQuarterRootReal.compute n).hi := by
    change 0≤(latticeQuarterRootReal.compute n).hi-(latticeQuarterRootReal.compute n).lo at hw
    grind only
  exact QInterval.intersection_ordered_of_overlaps ho (by decide +kernel)
    (latticeQuarterRootReal_guard_overlap n)

theorem latticeQuarterReboxedRoot_valid : latticeQuarterReboxedRoot.Valid := by
  refine ⟨?_,?_,?_⟩
  · intro n
    have h := latticeQuarterReboxedRoot_ordered n
    change 0≤(latticeQuarterReboxedRoot.compute n).hi-(latticeQuarterReboxedRoot.compute n).lo
    grind only
  · intro n m hnm
    have h := latticeQuarterRootReal_valid.2.1 n m hnm
    have ho := latticeQuarterReboxedRoot_ordered m
    change max (latticeQuarterRootReal.compute n).lo 2≤max (latticeQuarterRootReal.compute m).lo 2 ∧
      max (latticeQuarterRootReal.compute m).lo 2≤min (latticeQuarterRootReal.compute m).hi 4 ∧
      min (latticeQuarterRootReal.compute m).hi 4≤min (latticeQuarterRootReal.compute n).hi 4
    constructor
    · grind
    · exact ⟨ho,by grind⟩
  · intro eps
    obtain ⟨N,hN⟩ := latticeQuarterRootReal_valid.2.2 eps
    refine ⟨N,?_⟩
    intro n hn
    have h := hN n hn
    have hc := QInterval.intersection_contained_left (latticeQuarterRootReal.compute n) latticeQuarterRootGuard
    change (latticeQuarterReboxedRoot.compute n).hi-(latticeQuarterReboxedRoot.compute n).lo≤eps.val
    change (latticeQuarterRootReal.compute n).hi-(latticeQuarterRootReal.compute n).lo≤eps.val at h
    change (latticeQuarterRootReal.compute n).lo≤(latticeQuarterReboxedRoot.compute n).lo ∧
      (latticeQuarterReboxedRoot.compute n).hi≤(latticeQuarterRootReal.compute n).hi at hc
    grind only

theorem latticeQuarterReboxedRoot_equiv : latticeQuarterReboxedRoot.Equiv latticeQuarterRootReal := by
  intro n
  apply (RealRaw.compareAt_overlap_iff _ _ n n).2
  have h := latticeQuarterReboxedRoot_ordered n
  have hc := QInterval.intersection_contained_left (latticeQuarterRootReal.compute n) latticeQuarterRootGuard
  exact ⟨Rat.le_trans h hc.2,Rat.le_trans hc.1 h⟩


def latticeHalfFrequencyName : RealRaw := RealRaw.scaleRat (1/2) latticeQuarterReboxedRoot

theorem latticeHalfFrequencyName_valid : latticeHalfFrequencyName.Valid :=
  RealRaw.scaleRat_valid latticeQuarterReboxedRoot_valid

theorem latticeHalfFrequencyName_bounds (n : Nat) :
    1≤(latticeHalfFrequencyName.compute n).lo ∧ (latticeHalfFrequencyName.compute n).hi≤2 := by
  have h := QInterval.intersection_contained_right (latticeQuarterRootReal.compute n) latticeQuarterRootGuard
  change 2≤(latticeQuarterReboxedRoot.compute n).lo ∧ (latticeQuarterReboxedRoot.compute n).hi≤4 at h
  simp only [latticeHalfFrequencyName,RealRaw.scaleRat,RealRaw.scaleRatCompute,
    if_pos (show 0≤(1:Rat)/2 by decide +kernel)]
  generalize (latticeQuarterReboxedRoot.compute n).lo=a at h ⊢
  generalize (latticeQuarterReboxedRoot.compute n).hi=b at h ⊢
  constructor <;> grind only

theorem latticeHalfFrequencyName_agreement :
    latticeHalfFrequencyName.Equiv (RealRaw.scaleRat (1/2) latticeFrequency.val.realPart) :=
  RealRaw.scaleRat_equiv (RealRaw.equiv_trans latticeQuarterReboxedRoot_valid latticeQuarterRootReal_valid
    (realPart_valid latticeFrequency.property) latticeQuarterReboxedRoot_equiv
    (realPart_equiv latticeQuarterFrequency_agreement))

end ComputableAnalysis.ModularForms
