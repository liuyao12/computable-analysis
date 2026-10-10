import RationalProofAudit
import Mathlib.Analysis.Convex.Hull
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Linarith

/-! The finite-point and finite-halfspace bodies, specialized to rational
coordinates. This file does not use Mathlib real or complex scalars, measure,
integration, or real-analytic sphere-volume theorems. It is an isolated
Mathlib algebra/convexity layer, not an addition to the native import closure.
-/
namespace ComputableAnalysis.RationalConvexBodies
abbrev Point (n : Nat) := Fin n → ℚ

def normSq {n : Nat} (x : Point n) : ℚ := ∑ i, x i^2

def dot {n : Nat} (p x : Point n) : ℚ := ∑ i, p i*x i

def unitBall (n : Nat) : Set (Point n) := {x | normSq x ≤ 1}

def inner {n : Nat} (samples : Finset (Point n)) : Set (Point n) :=
  convexHull ℚ (samples : Set (Point n))

def outer {n : Nat} (samples : Finset (Point n)) : Set (Point n) :=
  {x | ∀ p ∈ samples, dot p x ≤ 1}

theorem normSq_nonneg {n : Nat} (x : Point n) : 0 ≤ normSq x := by
  exact Finset.sum_nonneg (fun i _ => sq_nonneg (x i))

theorem unitBall_convex (n : Nat) : Convex ℚ (unitBall n) := by
  intro x hx y hy a b ha hb hab
  have hcell : ∀ i, (a*x i+b*y i)^2 ≤ a*x i^2+b*y i^2 := by
    intro i
    have hs := mul_nonneg (mul_nonneg ha hb) (sq_nonneg (x i-y i))
    have hxa : a^2 = a-a*b := by nlinarith [hab]
    have hxb : b^2 = b-a*b := by nlinarith [hab]
    nlinarith
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hcell i)
  have hr : (∑ i, (a*x i^2+b*y i^2)) = a*normSq x+b*normSq y := by
    simp [normSq, Finset.sum_add_distrib, Finset.mul_sum]
  rw [hr] at hsum
  have h1 := mul_le_mul_of_nonneg_left hx ha
  have h2 := mul_le_mul_of_nonneg_left hy hb
  change (∑ i, (a*x i+b*y i)^2) ≤ 1
  nlinarith

theorem inner_subset_unitBall {n : Nat} (samples : Finset (Point n))
    (hunit : ∀ p ∈ samples, normSq p = 1) : inner samples ⊆ unitBall n := by
  apply convexHull_min
  · intro p hp
    show normSq p ≤ 1
    rw [hunit p hp]
  · exact unitBall_convex n

theorem tangent_bound {n : Nat} (p x : Point n)
    (hp : normSq p = 1) (hx : normSq x ≤ 1) : dot p x ≤ 1 := by
  have hs := normSq_nonneg (fun i => p i-x i)
  have ht : (∑ i, 2*p i*x i) = 2*dot p x := by
    simp [dot, Finset.mul_sum, mul_assoc]
  have hi : normSq (fun i => p i-x i) = normSq p+normSq x-2*dot p x := by
    simp only [normSq]
    simp_rw [sub_sq]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ht]
    ring
  rw [hi] at hs
  nlinarith

theorem unitBall_subset_outer {n : Nat} (samples : Finset (Point n))
    (hunit : ∀ p ∈ samples, normSq p = 1) : unitBall n ⊆ outer samples := by
  intro x hx p hp
  exact tangent_bound p x (hunit p hp) hx

theorem rational_brackets {n : Nat} (samples : Finset (Point n))
    (hunit : ∀ p ∈ samples, normSq p = 1) :
    inner samples ⊆ unitBall n ∧ unitBall n ⊆ outer samples :=
  ⟨inner_subset_unitBall samples hunit, unitBall_subset_outer samples hunit⟩

theorem inner_refines {n : Nat} {S T : Finset (Point n)} (h : S ⊆ T) :
    inner S ⊆ inner T := convexHull_mono h

theorem outer_refines {n : Nat} {S T : Finset (Point n)} (h : S ⊆ T) :
    outer T ⊆ outer S := by
  intro x hx p hp
  exact hx p (h hp)

def axis {n : Nat} (i : Fin n) : Point n := fun j => if j=i then 1 else 0

def axesPresent {n : Nat} (S : Finset (Point n)) : Prop :=
  ∀ i, axis i ∈ S ∧ (fun j => -axis i j) ∈ S

theorem dot_axis {n : Nat} (i : Fin n) (x : Point n) : dot (axis i) x = x i := by
  simp [dot, axis]

theorem dot_negative_axis {n : Nat} (i : Fin n) (x : Point n) :
    dot (fun j => -axis i j) x = -x i := by
  simp [dot, axis]

theorem outer_bounded {n : Nat} (S : Finset (Point n)) (haxes : axesPresent S)
    (x : Point n) (hx : x ∈ outer S) : ∀ i, -1 ≤ x i ∧ x i ≤ 1 := by
  intro i
  have hupper := hx (axis i) (haxes i).1
  have hlower := hx (fun j => -axis i j) (haxes i).2
  rw [dot_axis] at hupper
  rw [dot_negative_axis] at hlower
  constructor <;> linarith

theorem outer_convex {n : Nat} (S : Finset (Point n)) : Convex ℚ (outer S) := by
  intro x hx y hy a b ha hb hab p hp
  have hd : dot p (a • x+b • y) = a*dot p x+b*dot p y := by
    simp [dot, mul_add, mul_left_comm, Finset.sum_add_distrib, Finset.mul_sum]
  rw [hd]
  have h1 := mul_le_mul_of_nonneg_left (hx p hp) ha
  have h2 := mul_le_mul_of_nonneg_left (hy p hp) hb
  linarith

/-- An arbitrary finite rational halfspace presentation, without a new polytope type. -/
def byHalfspaces {n m : Nat} (normals : Fin m → Point n)
    (offsets : Fin m → ℚ) : Set (Point n) :=
  {x | ∀ j, dot (normals j) x ≤ offsets j}

theorem byHalfspaces_convex {n m : Nat} (normals : Fin m → Point n)
    (offsets : Fin m → ℚ) : Convex ℚ (byHalfspaces normals offsets) := by
  intro x hx y hy a b ha hb hab j
  have hd : dot (normals j) (a • x+b • y) =
      a*dot (normals j) x+b*dot (normals j) y := by
    simp [dot, mul_add, mul_left_comm, Finset.sum_add_distrib, Finset.mul_sum]
  rw [hd]
  have h1 := mul_le_mul_of_nonneg_left (hx j) ha
  have h2 := mul_le_mul_of_nonneg_left (hy j) hb
  calc
    a*dot (normals j) x+b*dot (normals j) y ≤
        a*offsets j+b*offsets j := add_le_add h1 h2
    _ = offsets j := by rw [← add_mul, hab, one_mul]

#print axioms byHalfspaces_convex

#print axioms unitBall_convex
#print axioms inner_subset_unitBall
#print axioms tangent_bound
#print axioms unitBall_subset_outer
#print axioms rational_brackets
#print axioms inner_refines
#print axioms outer_bounded
#print axioms outer_convex
#print axioms outer_refines
end ComputableAnalysis.RationalConvexBodies

open Lean

run_cmd do
  let env ← Lean.getEnv
  let deps := RationalProofAudit.audit env [`ComputableAnalysis.RationalConvexBodies.unitBall_convex, `ComputableAnalysis.RationalConvexBodies.rational_brackets, `ComputableAnalysis.RationalConvexBodies.inner_refines, `ComputableAnalysis.RationalConvexBodies.outer_refines, `ComputableAnalysis.RationalConvexBodies.outer_bounded, `ComputableAnalysis.RationalConvexBodies.outer_convex, `ComputableAnalysis.RationalConvexBodies.byHalfspaces_convex]
  let forbidden := deps.filter fun n => let s := n.toString; s == "Real" || s.startsWith "Real." || s == "Complex" || s.startsWith "Complex." || s.startsWith "MeasureTheory." || s.startsWith "intervalIntegral"
  unless forbidden.isEmpty do throwError "Forbidden scalar/analysis dependencies: {forbidden}"
  logInfo m!"PASS: {deps.size} transitive declaration dependencies; no Mathlib real/complex scalars, measure or integration"
