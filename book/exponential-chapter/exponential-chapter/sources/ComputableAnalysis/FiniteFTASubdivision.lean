import ComputableAnalysis.Basic
import ComputableAnalysis.ComplexInterval

/-!
# Four-quadrant rational subdivision of a complex box

`dyadicChildren` splits an ordered rational complex box at its coordinatewise
midpoint.  The results are finite geometric facts only: the four closed
children are ordered, lie inside the parent, and cover every point of the
parent.  No polynomial, root-existence, or limiting theorem is used here.
-/

namespace ComputableAnalysis

namespace FiniteFTASubdivision

private def southWest (parent : QBox) : QBox :=
  { lo := parent.lo, hi := parent.center }

private def southEast (parent : QBox) : QBox :=
  { lo := { re := parent.center.re, im := parent.lo.im },
    hi := { re := parent.hi.re, im := parent.center.im } }

private def northWest (parent : QBox) : QBox :=
  { lo := { re := parent.lo.re, im := parent.center.im },
    hi := { re := parent.center.re, im := parent.hi.im } }

private def northEast (parent : QBox) : QBox :=
  { lo := parent.center, hi := parent.hi }

/-- The four closed rational quadrants obtained by splitting at the center. -/
def dyadicChildren (parent : QBox) : List QBox :=
  [southWest parent, southEast parent, northWest parent, northEast parent]

/-! Finite-depth recursive schedules. -/

/-- Subdivide a box into four quadrants recursively to the requested depth.
At depth zero the schedule consists of the original parent. -/
def dyadicSubdivide : Nat → QBox → List QBox
  | 0, parent => [parent]
  | n + 1, parent =>
      (dyadicChildren parent).flatMap (dyadicSubdivide n)

/-- The executable finite filter retaining exactly those child boxes whose
polynomial image overlaps the zero box. -/
def survivingChildren (coeffs : CPoly.Coeffs) (parent : QBox) : List QBox :=
  (dyadicChildren parent).filter
    (fun child => QBox.overlaps (QBox.evalPoly coeffs child) QBox.zero)

/-- Recursive finite subdivision retaining only polynomial-image survivors at
each level. -/
def survivingSubdivide (coeffs : CPoly.Coeffs) : Nat → QBox → List QBox
  | 0, parent => [parent]
  | n + 1, parent =>
      (survivingChildren coeffs parent).flatMap (survivingSubdivide coeffs n)

private theorem center_bounds {parent : QBox} (hparent : parent.Ordered) :
    parent.lo.re <= parent.center.re /\
      parent.center.re <= parent.hi.re /\
      parent.lo.im <= parent.center.im /\
      parent.center.im <= parent.hi.im := by
  have hre := QInterval.midpoint_mem
    (I := { lo := parent.lo.re, hi := parent.hi.re }) hparent.1
  have him := QInterval.midpoint_mem
    (I := { lo := parent.lo.im, hi := parent.hi.im }) hparent.2
  exact ⟨by simpa [QBox.center, QInterval.midpoint] using hre.1,
    by simpa [QBox.center, QInterval.midpoint] using hre.2,
    by simpa [QBox.center, QInterval.midpoint] using him.1,
    by simpa [QBox.center, QInterval.midpoint] using him.2⟩

private theorem quadrant_ordered
    {parent : QBox} (hparent : parent.Ordered) :
    (southWest parent).Ordered /\
      (southEast parent).Ordered /\
      (northWest parent).Ordered /\
      (northEast parent).Ordered := by
  have hm := center_bounds hparent
  unfold southWest southEast northWest northEast QBox.Ordered
  exact ⟨⟨hm.1, hm.2.2.1⟩,
    ⟨hm.2.1, hm.2.2.1⟩,
    ⟨hm.1, hm.2.2.2⟩,
    ⟨hm.2.1, hm.2.2.2⟩⟩

private theorem quadrant_nested
    {parent : QBox} (hparent : parent.Ordered) :
    (southWest parent).NestedIn parent /\
      (southEast parent).NestedIn parent /\
      (northWest parent).NestedIn parent /\
      (northEast parent).NestedIn parent := by
  have hm := center_bounds hparent
  unfold southWest southEast northWest northEast QBox.NestedIn
  exact ⟨⟨⟨by simp, by simp⟩, ⟨hm.2.1, hm.2.2.2⟩⟩,
    ⟨⟨hm.1, by simp⟩, ⟨by simp, hm.2.2.2⟩⟩,
    ⟨⟨by simp, hm.2.2.1⟩, ⟨hm.2.1, by simp⟩⟩,
    ⟨⟨hm.1, hm.2.2.1⟩, ⟨by simp, by simp⟩⟩⟩

theorem dyadicChildren_ordered
    {parent : QBox} (hparent : parent.Ordered) :
    ∀ child ∈ dyadicChildren parent, child.Ordered := by
  intro child hchild
  simp [dyadicChildren] at hchild
  rcases hchild with rfl | rfl | rfl | rfl
  · exact (quadrant_ordered hparent).1
  · exact (quadrant_ordered hparent).2.1
  · exact (quadrant_ordered hparent).2.2.1
  · exact (quadrant_ordered hparent).2.2.2

theorem dyadicChildren_nested
    {parent : QBox} (hparent : parent.Ordered) :
    ∀ child ∈ dyadicChildren parent, child.NestedIn parent := by
  intro child hchild
  simp [dyadicChildren] at hchild
  rcases hchild with rfl | rfl | rfl | rfl
  · exact (quadrant_nested hparent).1
  · exact (quadrant_nested hparent).2.1
  · exact (quadrant_nested hparent).2.2.1
  · exact (quadrant_nested hparent).2.2.2

theorem dyadicChildren_cover
    {parent : QBox} (hparent : parent.Ordered) (z : QComplex)
    (hzlo : parent.lo <= z) (hzhi : z <= parent.hi) :
    ∃ child ∈ dyadicChildren parent,
      child.lo <= z /\ z <= child.hi := by
  have hm := center_bounds hparent
  simp only [QComplex.le_def] at hzlo hzhi ⊢
  by_cases hre : z.re <= parent.center.re
  · by_cases him : z.im <= parent.center.im
    · refine ⟨southWest parent, by simp [dyadicChildren], ?_⟩
      exact ⟨⟨hzlo.1, hzlo.2⟩, ⟨hre, him⟩⟩
    · refine ⟨northWest parent, by simp [dyadicChildren], ?_⟩
      have him' : parent.center.im <= z.im := by grind
      exact ⟨⟨hzlo.1, him'⟩, ⟨hre, hzhi.2⟩⟩
  · have hre' : parent.center.re <= z.re := by grind
    by_cases him : z.im <= parent.center.im
    · refine ⟨southEast parent, by simp [dyadicChildren], ?_⟩
      exact ⟨⟨hre', hzlo.2⟩, ⟨hzhi.1, him⟩⟩
    · refine ⟨northEast parent, by simp [dyadicChildren], ?_⟩
      have him' : parent.center.im <= z.im := by grind
      exact ⟨⟨hre', him'⟩, ⟨hzhi.1, hzhi.2⟩⟩

/-- Each quadrant has exactly half the parent width and height. -/
theorem dyadicChildren_width_height
    {parent : QBox} (hparent : parent.Ordered) :
    ∀ child ∈ dyadicChildren parent,
      child.width = parent.width / 2 ∧ child.height = parent.height / 2 := by
  intro child hchild
  simp [dyadicChildren] at hchild
  rcases hchild with rfl | rfl | rfl | rfl
  all_goals
    constructor <;>
      simp [southWest, southEast, northWest, northEast,
        QBox.width, QBox.height, QBox.center] <;>
      grind [Rat.div_def, Rat.sub_eq_add_neg, Rat.add_assoc,
        Rat.add_comm, Rat.add_left_comm]

/-- A root in an ordered parent survives the finite image-overlap filter. -/
theorem root_mem_survivingChildren
    {coeffs : CPoly.Coeffs} {parent : QBox}
    (hparent : parent.Ordered) {z : QComplex}
    (hzlo : parent.lo <= z) (hzhi : z <= parent.hi)
    (hzroot : CPoly.eval coeffs z = QComplex.zero) :
    ∃ child, child ∈ survivingChildren coeffs parent ∧
      child.lo <= z ∧ z <= child.hi := by
  obtain ⟨child, hchild, hchildlo, hchildhi⟩ :=
    dyadicChildren_cover hparent z hzlo hzhi
  have hover : QBox.Overlaps (QBox.evalPoly coeffs child) QBox.zero := by
    by_cases hmiss : QBox.Overlaps (QBox.evalPoly coeffs child) QBox.zero
    · exact hmiss
    · exact False.elim ((QBox.evalPoly_no_root_of_not_overlaps_zero
        hchildlo hchildhi hmiss) hzroot)
  have hover_bool :
      QBox.overlaps (QBox.evalPoly coeffs child) QBox.zero = true := by
    simp [QBox.overlaps, hover]
  refine ⟨child, ?_, hchildlo, hchildhi⟩
  exact List.mem_filter.mpr ⟨hchild, hover_bool⟩

theorem survivingChildren_ordered
    {coeffs : CPoly.Coeffs} {parent child : QBox}
    (hparent : parent.Ordered) (hchild : child ∈ survivingChildren coeffs parent) :
    child.Ordered := by
  exact dyadicChildren_ordered hparent child (List.mem_filter.mp hchild).1

/-- A supplied root survives every finite depth of the recursive polynomial
image-overlap filter. -/
theorem root_mem_survivingSubdivide
    {coeffs : CPoly.Coeffs} {n : Nat} {parent : QBox}
    (hparent : parent.Ordered) {z : QComplex}
    (hzlo : parent.lo <= z) (hzhi : z <= parent.hi)
    (hzroot : CPoly.eval coeffs z = QComplex.zero) :
    ∃ child, child ∈ survivingSubdivide coeffs n parent ∧
      child.lo <= z ∧ z <= child.hi := by
  induction n generalizing parent with
  | zero =>
      exact ⟨parent, by simp [survivingSubdivide], hzlo, hzhi⟩
  | succ n ih =>
      obtain ⟨quadrant, hquadrant, hqlo, hqhi⟩ :=
        root_mem_survivingChildren hparent hzlo hzhi hzroot
      have hdyadic : quadrant ∈ dyadicChildren parent :=
        (List.mem_filter.mp hquadrant).1
      have hquadrant_ordered :=
        dyadicChildren_ordered hparent quadrant hdyadic
      obtain ⟨child, hchild, hchildlo, hchildhi⟩ :=
        ih hquadrant_ordered hqlo hqhi
      refine ⟨child, ?_, hchildlo, hchildhi⟩
      exact List.mem_flatMap.mpr ⟨quadrant, hquadrant, hchild⟩

theorem survivingSubdivide_nonempty_of_root
    {coeffs : CPoly.Coeffs} {n : Nat} {parent : QBox}
    (hparent : parent.Ordered) {z : QComplex}
    (hzlo : parent.lo <= z) (hzhi : z <= parent.hi)
    (hzroot : CPoly.eval coeffs z = QComplex.zero) :
    survivingSubdivide coeffs n parent ≠ [] := by
  obtain ⟨child, hchild, _, _⟩ :=
    root_mem_survivingSubdivide hparent hzlo hzhi hzroot
  exact List.ne_nil_of_mem hchild

theorem survivingSubdivide_nestedIn_parent
    {coeffs : CPoly.Coeffs} {n : Nat} {parent : QBox}
    (hparent : parent.Ordered) :
    ∀ child ∈ survivingSubdivide coeffs n parent,
      child.NestedIn parent := by
  induction n generalizing parent with
  | zero =>
      intro child hchild
      simp [survivingSubdivide] at hchild
      subst child
      exact ⟨QComplex.le_refl parent.lo, QComplex.le_refl parent.hi⟩
  | succ n ih =>
      intro child hchild
      simp only [survivingSubdivide, List.mem_flatMap] at hchild
      obtain ⟨quadrant, hquadrant, hchild⟩ := hchild
      have hdyadic : quadrant ∈ dyadicChildren parent :=
        (List.mem_filter.mp hquadrant).1
      have hquadrant_nested :=
        dyadicChildren_nested hparent quadrant hdyadic
      have hquadrant_ordered :=
        dyadicChildren_ordered hparent quadrant hdyadic
      have hchild_nested := ih hquadrant_ordered child hchild
      exact QBox.nested_trans hchild_nested hquadrant_nested

theorem survivingSubdivide_ordered
    {coeffs : CPoly.Coeffs} {n : Nat} {parent : QBox}
    (hparent : parent.Ordered) :
    ∀ child ∈ survivingSubdivide coeffs n parent,
      child.Ordered := by
  induction n generalizing parent with
  | zero =>
      intro child hchild
      simp [survivingSubdivide] at hchild
      subst child
      exact hparent
  | succ n ih =>
      intro child hchild
      simp only [survivingSubdivide, List.mem_flatMap] at hchild
      obtain ⟨quadrant, hquadrant, hchild⟩ := hchild
      have hdyadic : quadrant ∈ dyadicChildren parent :=
        (List.mem_filter.mp hquadrant).1
      exact ih (dyadicChildren_ordered hparent quadrant hdyadic) child hchild

theorem survivingSubdivide_width_height_exact
    {coeffs : CPoly.Coeffs} {n : Nat} {parent child : QBox}
    (hparent : parent.Ordered)
    (hchild : child ∈ survivingSubdivide coeffs n parent) :
    child.width = parent.width / ((2 ^ n : Nat) : Rat) ∧
      child.height = parent.height / ((2 ^ n : Nat) : Rat) := by
  induction n generalizing parent with
  | zero =>
      simp only [survivingSubdivide, List.mem_singleton] at hchild
      subst child
      rw [Rat.div_def]
      grind [Rat.mul_inv_cancel]
  | succ n ih =>
      simp only [survivingSubdivide] at hchild
      obtain ⟨quadrant, hquadrant, hchild⟩ :=
        List.mem_flatMap.mp hchild
      have hdyadic : quadrant ∈ dyadicChildren parent :=
        (List.mem_filter.mp hquadrant).1
      have hquadrant_ordered :=
        dyadicChildren_ordered hparent quadrant hdyadic
      have hchild_exact := ih hquadrant_ordered hchild
      have hquadrant_exact :=
        dyadicChildren_width_height hparent quadrant hdyadic
      rw [hchild_exact.1, hchild_exact.2,
        hquadrant_exact.1, hquadrant_exact.2]
      constructor <;> rw [Nat.pow_succ]
      · rw [Rat.div_def, Rat.div_def, Rat.div_def]
        have hpow :
            (((2 ^ (n + 1) : Nat) : Rat)) =
              (((2 ^ n : Nat) : Rat)) * 2 := by
          exact_mod_cast (by simpa using (Nat.pow_succ 2 n))
        grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
      · rw [Rat.div_def, Rat.div_def, Rat.div_def]
        have hpow :
            (((2 ^ (n + 1) : Nat) : Rat)) =
              (((2 ^ n : Nat) : Rat)) * 2 := by
          exact_mod_cast (by simpa using (Nat.pow_succ 2 n))
        grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

theorem dyadicSubdivide_nonempty (n : Nat) (parent : QBox) :
    dyadicSubdivide n parent ≠ [] := by
  induction n generalizing parent with
  | zero => simp [dyadicSubdivide]
  | succ n ih =>
      simp only [dyadicSubdivide, dyadicChildren, List.flatMap_cons,
        List.flatMap_nil]
      simp [ih]

theorem dyadicSubdivide_nestedIn_parent
    {n : Nat} {parent : QBox} (hparent : parent.Ordered) :
    ∀ child ∈ dyadicSubdivide n parent, child.NestedIn parent := by
  induction n generalizing parent with
  | zero =>
      intro child hchild
      simp only [dyadicSubdivide, List.mem_singleton] at hchild
      subst child
      exact ⟨QComplex.le_refl _, QComplex.le_refl _⟩
  | succ n ih =>
      intro child hchild
      simp only [dyadicSubdivide] at hchild
      rcases List.mem_flatMap.mp hchild with ⟨quadrant, hquadrant, hchild⟩
      have hquadrant_ordered :=
        dyadicChildren_ordered hparent quadrant hquadrant
      have hlocal := ih hquadrant_ordered child hchild
      exact QBox.nested_trans hlocal
        (dyadicChildren_nested hparent quadrant hquadrant)

/-- Every box at finite subdivision depth remains ordered. -/
theorem dyadicSubdivide_ordered
    {n : Nat} {parent : QBox} (hparent : parent.Ordered) :
    ∀ child ∈ dyadicSubdivide n parent, child.Ordered := by
  induction n generalizing parent with
  | zero =>
      intro child hchild
      simp only [dyadicSubdivide, List.mem_singleton] at hchild
      subst child
      exact hparent
  | succ n ih =>
      intro child hchild
      simp only [dyadicSubdivide] at hchild
      rcases List.mem_flatMap.mp hchild with ⟨quadrant, hquadrant, hchild⟩
      have hquadrant_ordered :=
        dyadicChildren_ordered hparent quadrant hquadrant
      exact ih hquadrant_ordered child hchild

/-- Finite-depth subdivision never increases either box dimension.  The
one-step theorem above gives the sharper exact half-width result. -/
theorem dyadicSubdivide_width_height_le_parent
    {n : Nat} {parent : QBox} (hparent : parent.Ordered) :
    ∀ child ∈ dyadicSubdivide n parent,
      0 <= child.width /\ child.width <= parent.width /\
      0 <= child.height /\ child.height <= parent.height := by
  intro child hchild
  have hchild_ordered := dyadicSubdivide_ordered hparent child hchild
  have hnested := dyadicSubdivide_nestedIn_parent hparent child hchild
  unfold QBox.Ordered at hchild_ordered hparent
  unfold QBox.width QBox.height
  have hw_nonneg : 0 <= child.hi.re - child.lo.re := by
    grind [Rat.sub_eq_add_neg, hchild_ordered.1]
  have hh_nonneg : 0 <= child.hi.im - child.lo.im := by
    grind [Rat.sub_eq_add_neg, hchild_ordered.2]
  have hw_le : child.hi.re - child.lo.re <= parent.hi.re - parent.lo.re := by
    grind [Rat.sub_eq_add_neg, hnested.1.1, hnested.2.1]
  have hh_le : child.hi.im - child.lo.im <= parent.hi.im - parent.lo.im := by
    grind [Rat.sub_eq_add_neg, hnested.1.2, hnested.2.2]
  exact ⟨hw_nonneg, hw_le, hh_nonneg, hh_le⟩

theorem dyadicSubdivide_width_height_exact
    {n : Nat} {parent child : QBox} (hparent : parent.Ordered)
    (hchild : child ∈ dyadicSubdivide n parent) :
    child.width = parent.width / ((2 ^ n : Nat) : Rat) ∧
      child.height = parent.height / ((2 ^ n : Nat) : Rat) := by
  induction n generalizing parent with
  | zero =>
      simp only [dyadicSubdivide, List.mem_singleton] at hchild
      subst child
      rw [Rat.div_def]
      grind [Rat.mul_inv_cancel]
  | succ n ih =>
      simp only [dyadicSubdivide] at hchild
      obtain ⟨quadrant, hquadrant, hchild⟩ :=
        List.mem_flatMap.mp hchild
      have hquadrant_ordered :=
        dyadicChildren_ordered hparent quadrant hquadrant
      have hchild_exact := ih hquadrant_ordered hchild
      have hquadrant_exact :=
        dyadicChildren_width_height hparent quadrant hquadrant
      rw [hchild_exact.1, hchild_exact.2,
        hquadrant_exact.1, hquadrant_exact.2]
      constructor <;> rw [Nat.pow_succ]
      · rw [Rat.div_def, Rat.div_def, Rat.div_def]
        have hpow :
            (((2 ^ (n + 1) : Nat) : Rat)) =
              (((2 ^ n : Nat) : Rat)) * 2 := by
          exact_mod_cast (by simpa using (Nat.pow_succ 2 n))
        grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
      · rw [Rat.div_def, Rat.div_def, Rat.div_def]
        have hpow :
            (((2 ^ (n + 1) : Nat) : Rat)) =
              (((2 ^ n : Nat) : Rat)) * 2 := by
          exact_mod_cast (by simpa using (Nat.pow_succ 2 n))
        grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

end FiniteFTASubdivision

end ComputableAnalysis
