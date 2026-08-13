import ComputableAnalysis.Basic

/-!
# Shared rational anchors for computable-real equality

An exact rational witness can replace an appeal to a completed real limit.  If
two valid interval algorithms eventually contain the same rational anchor,
then nesting propagates that witness back to every earlier stage, so the two
algorithms overlap at every stage.  This is a reusable identity certificate,
not a completeness theorem.
-/

namespace ComputableAnalysis

namespace RealRaw

def EventuallyContainsRat (x : RealRaw) (q : Rat) : Prop :=
  ∃ N, ∀ n, N ≤ n → (x.compute n).lo ≤ q ∧ q ≤ (x.compute n).hi

theorem EventuallyContainsRat.contains_all_stages
    {x : RealRaw} (hx : x.Valid) {q : Rat}
    (hanchor : x.EventuallyContainsRat q) :
    ∀ n, (x.compute n).lo ≤ q ∧ q ≤ (x.compute n).hi := by
  rcases hanchor with ⟨N, hN⟩
  intro n
  have hlate := hN (max n N) (Nat.le_max_right n N)
  have hnest := hx.2.1 n (max n N) (Nat.le_max_left n N)
  constructor
  · exact Rat.le_trans hnest.1 hlate.1
  · exact Rat.le_trans hlate.2 hnest.2.2

theorem equiv_of_eventually_shared_rational_anchor
    {x y : RealRaw} (hx : x.Valid) (hy : y.Valid) {q : Rat}
    (hxq : x.EventuallyContainsRat q)
    (hyq : y.EventuallyContainsRat q) :
    x.Equiv y := by
  have hxall := hxq.contains_all_stages hx
  have hyall := hyq.contains_all_stages hy
  apply sameStageOverlap_equiv
  intro n
  apply (compareAt_overlap_iff x y n n).2
  exact ⟨Rat.le_trans (hxall n).1 (hyall n).2,
    Rat.le_trans (hyall n).1 (hxall n).2⟩

theorem allStagesOverlap_of_eventually_shared_rational_anchor
    {x y : RealRaw} (hx : x.Valid) (hy : y.Valid) {q : Rat}
    (hxq : x.EventuallyContainsRat q)
    (hyq : y.EventuallyContainsRat q) :
    x.AllStagesOverlap y := by
  exact allStagesOverlap_of_equiv hx hy
    (equiv_of_eventually_shared_rational_anchor hx hy hxq hyq)

end RealRaw

end ComputableAnalysis
