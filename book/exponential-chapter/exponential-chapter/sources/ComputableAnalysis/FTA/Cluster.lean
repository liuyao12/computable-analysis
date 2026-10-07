import ComputableAnalysis.FTA.Enclosures

/-! A bounded sequence of rational complex points has a represented cluster
point. The proof constructs nested rational boxes by a finite-cover argument;
it does not import an ambient completed complex space or a compactness theorem.

Choice is used only in this existence proof. This is not a uniform executable
subsequence-selection algorithm. Concrete interval operations remain unchanged.
-/
namespace ComputableAnalysis.RepresentedPolynomial

private def Often (P : Nat → Prop) : Prop := ∀ N, ∃ k, N ≤ k ∧ P k

private theorem often_finite_cover {α : Type} (xs : List α) (P : α → Nat → Prop)
    (h : Often (fun k => ∃ a ∈ xs, P a k)) : ∃ a ∈ xs, Often (P a) := by
  classical
  induction xs with
  | nil =>
      obtain ⟨k, _, hk⟩ := h 0
      simp at hk
  | cons a xs ih =>
      by_cases ha : Often (P a)
      · exact ⟨a, by simp, ha⟩
      · have hbound : ∃ N, ∀ k, N ≤ k → ¬ P a k := by
          apply Classical.byContradiction
          intro hnone
          apply ha
          intro N
          apply Classical.byContradiction
          intro hN
          exact hnone ⟨N, fun k hk hpk => hN ⟨k, hk, hpk⟩⟩
        obtain ⟨N, hN⟩ := hbound
        have htail : Often (fun k => ∃ b ∈ xs, P b k) := by
          intro M
          obtain ⟨k, hk, b, hb, hbk⟩ := h (max N M)
          refine ⟨k, by omega, b, ?_, hbk⟩
          have hb' : b = a ∨ b ∈ xs := by simpa using hb
          rcases hb' with rfl | hb'
          · exact False.elim (hN k (by omega) hbk)
          · exact hb'
        obtain ⟨b, hb, hfreq⟩ := ih htail
        exact ⟨b, by simp [hb], hfreq⟩

/-- Every box of the represented cluster point contains arbitrarily late
members of the sequence. This is an exact statement using rational bounds. -/
def Clusters (points : Nat → QComplex) (z : ComplexCert) : Prop :=
  ∀ n N, ∃ k, N ≤ k ∧
    (z.raw.compute n).lo ≤ points k ∧ points k ≤ (z.raw.compute n).hi

/-- Bounded rational sequences have cluster points in the raw foundation.
The represented point is constructed from a dyadic box branch. No pre-existing
real or complex limit is used in the proof. -/
theorem exists_cluster (points : Nat → QComplex) (initial : QBox)
    (hordered : initial.Ordered)
    (hbounded : ∀ k, initial.lo ≤ points k ∧ points k ≤ initial.hi) :
    ∃ z : ComplexCert, z.raw.compute 0 = initial ∧ Clusters points z := by
  classical
  let Node := { B : QBox // B.Ordered ∧ Often (fun k => B.lo ≤ points k ∧ points k ≤ B.hi) }
  have advance : ∀ node : Node, ∃ child : Node,
      child.val ∈ FiniteFTASubdivision.dyadicChildren node.val := by
    intro node
    have hcover : Often (fun k => ∃ child ∈ FiniteFTASubdivision.dyadicChildren node.val,
        child.lo ≤ points k ∧ points k ≤ child.hi) := by
      intro N
      obtain ⟨k, hk, hlo, hhi⟩ := node.property.2 N
      obtain ⟨child, hmem, hchildlo, hchildhi⟩ :=
        FiniteFTASubdivision.dyadicChildren_cover node.property.1 (points k) hlo hhi
      exact ⟨k, hk, child, hmem, hchildlo, hchildhi⟩
    obtain ⟨child, hmem, hchild⟩ := often_finite_cover
      (FiniteFTASubdivision.dyadicChildren node.val)
      (fun B k => B.lo ≤ points k ∧ points k ≤ B.hi) hcover
    exact ⟨⟨child, FiniteFTASubdivision.dyadicChildren_ordered node.property.1 child hmem,
      hchild⟩, hmem⟩
  let start : Node := ⟨initial, hordered, fun N => ⟨N, Nat.le_refl _, hbounded N⟩⟩
  let next : Node → Node := fun node => Classical.choose (advance node)
  let nodes : Nat → Node := fun n => Nat.rec start (fun _ node => next node) n
  let boxes : Nat → QBox := fun n => (nodes n).val
  have hstep : ∀ n, boxes (n+1) ∈ FiniteFTASubdivision.dyadicChildren (boxes n) := by
    intro n
    exact Classical.choose_spec (advance (nodes n))
  refine ⟨dyadicValue boxes hordered hstep, rfl, ?_⟩
  intro n N
  exact (nodes n).property.2 N

end ComputableAnalysis.RepresentedPolynomial
