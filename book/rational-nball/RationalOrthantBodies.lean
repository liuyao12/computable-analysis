import RationalConvexBodies

/-! Positive-orthant rational ball bodies. The inner hull contains the origin.
The outer body uses coordinate halfspaces and all sampled tangent normals, including coordinate-axis points.
These are finite convexity and containment statements, not volume axioms. -/
namespace ComputableAnalysis.RationalOrthantBodies
open RationalConvexBodies
abbrev Point (n : Nat) := RationalConvexBodies.Point n

def orthant (n : Nat) : Set (Point n) := {x | ∀ i, 0 ≤ x i}
def ball (n : Nat) : Set (Point n) := unitBall n ∩ orthant n

def inner {n : Nat} (samples : Finset (Point n)) : Set (Point n) :=
  convexHull ℚ (insert 0 (samples : Set (Point n)))

def outer {n : Nat} (samples : Finset (Point n)) : Set (Point n) :=
  orthant n ∩ RationalConvexBodies.outer samples

theorem orthant_convex (n : Nat) : Convex ℚ (orthant n) := by
  intro x hx y hy a b ha hb _ i
  exact add_nonneg (mul_nonneg ha (hx i)) (mul_nonneg hb (hy i))

theorem ball_convex (n : Nat) : Convex ℚ (ball n) :=
  (unitBall_convex n).inter (orthant_convex n)

theorem origin_mem_inner {n : Nat} (samples : Finset (Point n)) :
    (0 : Point n) ∈ inner samples :=
  subset_convexHull ℚ _ (Set.mem_insert 0 _)

theorem inner_subset_ball {n : Nat} (samples : Finset (Point n))
    (hunit : ∀ p ∈ samples, normSq p = 1)
    (hpositive : ∀ p ∈ samples, ∀ i, 0 ≤ p i) : inner samples ⊆ ball n := by
  apply convexHull_min
  · intro p hp
    rcases hp with hp | hp
    · subst p
      constructor
      · simp [unitBall, normSq]
      · intro i; simp
    · exact ⟨by change normSq p ≤ 1; rw [hunit p hp], hpositive p hp⟩
  · exact ball_convex n

theorem ball_subset_outer {n : Nat} (samples : Finset (Point n))
    (hunit : ∀ p ∈ samples, normSq p = 1) : ball n ⊆ outer samples := by
  classical
  intro x hx
  refine ⟨hx.2, ?_⟩
  intro p hp
  exact tangent_bound p x (hunit p hp) hx.1

/-- The axis tangents and coordinate planes bound the outer body by the unit cube. -/
theorem outer_axis_bound {n : Nat} (samples : Finset (Point n))
    (haxes : ∀ i, axis i ∈ samples) (x : Point n) (hx : x ∈ outer samples) :
    ∀ i, 0 ≤ x i ∧ x i ≤ 1 := by
  intro i
  have hi := hx.2 (axis i) (haxes i)
  rw [dot_axis] at hi
  exact ⟨hx.1 i,hi⟩

theorem inner_refines {n : Nat} {S T : Finset (Point n)} (h : S ⊆ T) :
    inner S ⊆ inner T := by
  apply convexHull_mono
  intro p hp
  rcases hp with hp | hp
  · exact Or.inl hp
  · exact Or.inr (h hp)

theorem outer_refines {n : Nat} {S T : Finset (Point n)} (h : S ⊆ T) :
    outer T ⊆ outer S := by
  classical
  intro x hx
  refine ⟨hx.1, ?_⟩
  intro p hp
  exact hx.2 p (h hp)

theorem outer_convex {n : Nat} (samples : Finset (Point n)) : Convex ℚ (outer samples) :=
  (orthant_convex n).inter (RationalConvexBodies.outer_convex samples)

/-- A positive coefficient of any nonnegative tangent bounds that coordinate.
The axis tangent gives the bound one. -/
theorem outer_coordinate_bound {n : Nat} (samples : Finset (Point n))
    (p : Point n) (hp : p ∈ samples) (hpositive : ∀ j, 0 ≤ p j)
    (i : Fin n) (hi : 0 < p i) (x : Point n) (hx : x ∈ outer samples) :
    0 ≤ x i ∧ x i ≤ 1 / p i := by
  have hsum : p i*x i ≤ dot p x := by
    exact Finset.single_le_sum (fun j _ => mul_nonneg (hpositive j) (hx.1 j)) (Finset.mem_univ i)
  have ht := hx.2 p hp
  refine ⟨hx.1 i, ?_⟩
  apply (le_div_iff₀ hi).mpr
  rw [mul_comm]
  exact le_trans hsum ht

#print axioms orthant_convex
#print axioms ball_convex
#print axioms origin_mem_inner
#print axioms inner_subset_ball
#print axioms ball_subset_outer
#print axioms outer_axis_bound
#print axioms inner_refines
#print axioms outer_refines
#print axioms outer_convex
#print axioms outer_coordinate_bound
end ComputableAnalysis.RationalOrthantBodies

open Lean
run_cmd do
  let env ← Lean.getEnv
  let deps := RationalProofAudit.audit env [
    `ComputableAnalysis.RationalOrthantBodies.orthant_convex,
    `ComputableAnalysis.RationalOrthantBodies.ball_convex,
    `ComputableAnalysis.RationalOrthantBodies.origin_mem_inner,
    `ComputableAnalysis.RationalOrthantBodies.inner_subset_ball,
    `ComputableAnalysis.RationalOrthantBodies.ball_subset_outer,
    `ComputableAnalysis.RationalOrthantBodies.outer_axis_bound,
    `ComputableAnalysis.RationalOrthantBodies.inner_refines,
    `ComputableAnalysis.RationalOrthantBodies.outer_refines,
    `ComputableAnalysis.RationalOrthantBodies.outer_convex,
    `ComputableAnalysis.RationalOrthantBodies.outer_coordinate_bound]
  let forbidden := deps.filter fun n => let s := n.toString; s == "Real" || s.startsWith "Real." || s == "Complex" || s.startsWith "Complex." || s.startsWith "MeasureTheory." || s.startsWith "intervalIntegral"
  unless forbidden.isEmpty do throwError "Forbidden scalar/analysis dependencies: {forbidden}"
  logInfo m!"PASS: {deps.size} transitive declaration dependencies; no Mathlib real/complex scalars, measure or integration"
