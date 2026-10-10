import RationalConeVolume
import RationalPolytopeDilation
import RationalFiniteVolumeComparison
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

namespace ComputableAnalysis.RationalPolytopeVolume
open RationalConvexBodies
set_option maxHeartbeats 2000000

/-- Every cap in the incremental subtraction is a subset of the original body. -/
theorem removedCaps_subset {n : Nat} (P : Polytope n) (cuts : List (Point n × ℚ)) :
    ∀ C ∈ removedCaps P cuts,body C ⊆ body P := by
  induction cuts generalizing P with
  | nil => simp [removedCaps]
  | cons ac rest ih =>
    obtain ⟨a,c⟩ := ac
    intro C hC
    rcases List.mem_cons.mp hC with rfl | hC
    · intro x hx; exact (body_clip_eq P (-a) (-c) ▸ hx).1
    · intro x hx
      have ht := ih _ C hC hx
      exact (body_clip_eq P a c ▸ ht).1

/-- Every removed cap remembers an actual plane that removed it. -/
theorem removedCaps_cut {n : Nat} (P : Polytope n) (cuts : List (Point n × ℚ)) :
    ∀ C ∈ removedCaps P cuts,∃ ac ∈ cuts,∀ x ∈ body C,ac.2 ≤ dot ac.1 x := by
  induction cuts generalizing P with
  | nil => simp [removedCaps]
  | cons ac rest ih =>
    obtain ⟨a,c⟩ := ac
    intro C hC
    rcases List.mem_cons.mp hC with rfl | hC
    · refine ⟨(a,c),List.mem_cons_self ..,?_⟩
      intro x hx
      have ht := (body_clip_eq P (-a) (-c) ▸ hx).2
      simpa [dot,Finset.sum_neg_distrib] using ht
    · obtain ⟨ac,hac,hx⟩ := ih _ C hC
      exact ⟨ac,List.mem_cons_of_mem _ hac,hx⟩

/-- A point outside the final retained hull is covered by an actual removed cap. -/
theorem removedCaps_cover_outside {n : Nat} (P : Polytope n) (cuts : List (Point n × ℚ))
    (x : Point n) (hx : x ∈ body P) (hout : x ∉ body (retainedAfterCuts P cuts)) :
    ∃ C ∈ removedCaps P cuts,x ∈ body C := by
  induction cuts generalizing P with
  | nil => exact (hout hx).elim
  | cons ac rest ih =>
    obtain ⟨a,c⟩ := ac
    by_cases hlow : dot a x ≤ c
    · have hmem : x ∈ body (clipVertices P a c) := by rw [body_clip_eq]; exact ⟨hx,hlow⟩
      obtain ⟨C,hC,hxC⟩ := ih _ hmem hout
      exact ⟨C,List.mem_cons_of_mem _ hC,hxC⟩
    · refine ⟨clipVertices P (-a) (-c),List.mem_cons_self ..,?_⟩
      rw [body_clip_eq]
      refine ⟨hx,?_⟩
      simpa [dot,Finset.sum_neg_distrib] using (le_of_not_ge hlow : c ≤ dot a x)

/-- Sequentially removed caps have only flat overlaps. -/
theorem removedCaps_pairwise {n : Nat} (P : Polytope n) (cuts : List (Point n × ℚ))
    (hnormal : ∀ ac ∈ cuts,ac.1 ≠ 0) :
    (removedCaps P cuts).Pairwise (fun C D => Flat (body C ∩ body D)) := by
  induction cuts generalizing P with
  | nil => simp [removedCaps]
  | cons ac rest ih =>
    obtain ⟨a,c⟩ := ac
    have ha := hnormal (a,c) (List.mem_cons_self ..)
    have hr : ∀ ac ∈ rest,ac.1 ≠ 0 := fun ac hac => hnormal ac (List.mem_cons_of_mem _ hac)
    rw [removedCaps,List.pairwise_cons]
    constructor
    · intro C hC
      refine ⟨a,c,ha,?_⟩
      intro x hx
      have hlo := removedCaps_subset (clipVertices P a c) rest C hC hx.2
      have hhi := (body_clip_eq P (-a) (-c) ▸ hx.1).2
      have hlow := (body_clip_eq P a c ▸ hlo).2
      have hhigh : c ≤ dot a x := by simpa [dot,Finset.sum_neg_distrib] using hhi
      exact le_antisymm hlow hhigh
    · exact ih _ hr

theorem normSq_smul {n : Nat} (r : ℚ) (x : Point n) : normSq (r • x)=r^2*normSq x := by
  simp [normSq,mul_pow,Finset.mul_sum]

theorem normSq_append {n m : Nat} (x : Point n) (y : Point m) :
    normSq (Fin.append x y)=normSq x+normSq y := by
  simp [normSq,Fin.sum_univ_add]

theorem dot_smul_right {n : Nat} (a : Point n) (r : ℚ) (x : Point n) :
    dot a (r • x)=r*dot a x := by
  simp [dot,Finset.mul_sum,mul_left_comm]

/-- Rational Cauchy-Schwarz; all scalars are rational, with no square root. -/
theorem unit_dot_sq_le {n : Nat} (q x : Point n) (hq : normSq q=1) :
    (dot q x)^2 ≤ normSq x := by
  have he := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ q x
  change (dot q x)^2 ≤ normSq q*normSq x at he
  simpa [hq] using he

theorem tangent_radius_lower {n : Nat} (q x : Point n) (hq : normSq q=1)
    (a : ℚ) (ha : 0 ≤ a) (hcut : a ≤ dot q x) : a^2 ≤ normSq x := by
  have hc := unit_dot_sq_le q x hq
  nlinarith

theorem tangent_radius_upper {n : Nat} (q x : Point n) (hq : normSq q=1)
    (a : ℚ) (ha : 0 ≤ a) (hball : normSq x ≤ a^2) : dot q x ≤ a := by
  have hc := unit_dot_sq_le q x hq
  nlinarith

/-- Actual rational shell caps: clip the previous scaled inner hull by the
scaled tangent planes of the outer sample. -/
noncomputable def innerShellCaps {n : Nat} (P : Polytope n) (S : Finset (Point n))
    (a b : ℚ) : List (Polytope n) :=
  removedCaps (dilated P b) (S.toList.map (fun q => (q,a)))

theorem innerShellCaps_norm_bounds {n : Nat} (P : Polytope n) (S : Finset (Point n))
    (hP : ∀ x ∈ body P,normSq x ≤ 1) (hS : ∀ q ∈ S,normSq q=1)
    (a b : ℚ) (ha : 0 ≤ a) (C : Polytope n) (hC : C ∈ innerShellCaps P S a b) :
    ∀ x ∈ body C,a^2 ≤ normSq x ∧ normSq x ≤ b^2 := by
  intro x hx
  have hp := removedCaps_subset (dilated P b) _ C hC hx
  rw [body_dilated] at hp
  obtain ⟨p,hp,rfl⟩ := hp
  obtain ⟨⟨q,c⟩,hqc,hcut⟩ := removedCaps_cut (dilated P b) _ C hC
  obtain ⟨q',hq',he⟩ := List.mem_map.mp hqc
  have hEq : q'=q ∧ a=c := by simpa using Prod.mk.inj he
  rcases hEq with ⟨heq,hec⟩
  subst q
  subst c
  have hunit := hS q' (Finset.mem_toList.mp hq')
  constructor
  · exact tangent_radius_lower q' (b • p) hunit a ha (hcut _ hx)
  · rw [normSq_smul]
    nlinarith [hP p hp,sq_nonneg b]

/-- Every lower shell prism fits in the unit ball by a finite quadratic
identity. Consequently it is contained in every actual outer ball polytope. -/
theorem innerShell_product_in_unitBall {n m : Nat} (C : Polytope n) (D : Polytope m)
    (b r : ℚ) (hC : ∀ x ∈ body C,normSq x ≤ b^2)
    (hD : ∀ y ∈ body D,normSq y ≤ 1) (hr : r^2 ≤ 1-b^2) :
    ∀ z ∈ body (productPoly C (dilated D r)),normSq z ≤ 1 := by
  intro z hz
  rw [body_productPoly] at hz
  obtain ⟨y,hy,he⟩ := body_dilated D r ▸ hz.2
  have hp : z=Fin.append (leftCoords z) (rightCoords z) := by
    ext i; refine Fin.addCases (fun j => by simp [leftCoords]) (fun j => by simp [rightCoords]) i
  rw [hp,normSq_append,← he,normSq_smul]
  have hc := hC _ hz.1
  have hd := hD y hy
  nlinarith [sq_nonneg r]

/-- The finite ordinary cylinder-minus-cone remainder is an actual list of
rational caps, computed incrementally from the cylinder. -/
noncomputable def coneRemainderCuts {n : Nat} (P : Polytope n) : List (Point (n+1) × ℚ) :=
  (Classical.choose (pointHull_nonzero_halfspaces (n+1) (by omega) (cone P))).toList

noncomputable def coneRemainder {n : Nat} (P : Polytope n) : List (Polytope (n+1)) :=
  removedCaps (prism P 1) (coneRemainderCuts P)

/-- Exact finite cylinder-minus-cone volume, with no curved body or integral. -/
theorem coneRemainder_volume {n : Nat} (V : Axioms n) (W : Axioms (n+1))
    (P : Polytope n) (hP : (0 : Point n) ∈ body P) :
    ((coneRemainder P).map W.volume).sum = (n:ℚ)/((n+1:Nat):ℚ)*V.volume P := by
  obtain ⟨hnormal,hrepr⟩ := Classical.choose_spec
    (pointHull_nonzero_halfspaces (n+1) (by omega) (cone P))
  have hn : ∀ ac ∈ coneRemainderCuts P,ac.1 ≠ 0 := by
    intro ac hac; exact hnormal ac (Finset.mem_toList.mp hac)
  have hb : body (retainedAfterCuts (prism P 1) (coneRemainderCuts P))=body (cone P) := by
    ext x
    rw [mem_body_retained]
    constructor
    · rintro ⟨_,hx⟩
      exact (hrepr x).mpr (fun ac hac => hx ac (Finset.mem_toList.mpr hac))
    · intro hx
      exact ⟨cone_subset_prism P hP hx,fun ac hac => (hrepr x).mp hx ac (Finset.mem_toList.mp hac)⟩
  have he := sequential_clip_volume W (coneRemainderCuts P) hn (prism P 1)
  rw [W.extensional _ _ hb,cone_volume V W,prism_volume V W P 1 (by decide),one_mul] at he
  change _=((n:ℚ)/((n+1:Nat):ℚ))*V.volume P
  have hdim : ((n+1:Nat):ℚ) ≠ 0 := by positivity
  have hcast : ((n+1:Nat):ℚ)=(n:ℚ)+1 := by simp
  change ((removedCaps (prism P 1) (coneRemainderCuts P)).map W.volume).sum = _
  have hs : ((removedCaps (prism P 1) (coneRemainderCuts P)).map W.volume).sum =
      V.volume P-V.volume P/((n+1:Nat):ℚ) := by linarith [he]
  rw [hs]
  field_simp
  rw [hcast]
  ring

end ComputableAnalysis.RationalPolytopeVolume

-- ARCHIMEDES AUDIT
#print axioms ComputableAnalysis.RationalPolytopeVolume.removedCaps_subset
#print axioms ComputableAnalysis.RationalPolytopeVolume.removedCaps_cut
#print axioms ComputableAnalysis.RationalPolytopeVolume.removedCaps_cover_outside
#print axioms ComputableAnalysis.RationalPolytopeVolume.removedCaps_pairwise
#print axioms ComputableAnalysis.RationalPolytopeVolume.normSq_smul
#print axioms ComputableAnalysis.RationalPolytopeVolume.normSq_append
#print axioms ComputableAnalysis.RationalPolytopeVolume.dot_smul_right
#print axioms ComputableAnalysis.RationalPolytopeVolume.unit_dot_sq_le
#print axioms ComputableAnalysis.RationalPolytopeVolume.tangent_radius_lower
#print axioms ComputableAnalysis.RationalPolytopeVolume.tangent_radius_upper
#print axioms ComputableAnalysis.RationalPolytopeVolume.innerShellCaps_norm_bounds
#print axioms ComputableAnalysis.RationalPolytopeVolume.innerShell_product_in_unitBall
#print axioms ComputableAnalysis.RationalPolytopeVolume.coneRemainder_volume

open Lean
run_cmd do
  let names := [`ComputableAnalysis.RationalPolytopeVolume.removedCaps_subset,
    `ComputableAnalysis.RationalPolytopeVolume.removedCaps_cut,
    `ComputableAnalysis.RationalPolytopeVolume.removedCaps_cover_outside,
    `ComputableAnalysis.RationalPolytopeVolume.removedCaps_pairwise,
    `ComputableAnalysis.RationalPolytopeVolume.normSq_smul,
    `ComputableAnalysis.RationalPolytopeVolume.normSq_append,
    `ComputableAnalysis.RationalPolytopeVolume.dot_smul_right,
    `ComputableAnalysis.RationalPolytopeVolume.unit_dot_sq_le,
    `ComputableAnalysis.RationalPolytopeVolume.tangent_radius_lower,
    `ComputableAnalysis.RationalPolytopeVolume.tangent_radius_upper,
    `ComputableAnalysis.RationalPolytopeVolume.innerShellCaps_norm_bounds,
    `ComputableAnalysis.RationalPolytopeVolume.innerShell_product_in_unitBall,
    `ComputableAnalysis.RationalPolytopeVolume.coneRemainder_volume]
  let env ← Lean.getEnv
  let deps := RationalProofAudit.audit env names
  let forbidden := deps.filter fun n => let s := n.toString; s == "Real" || s.startsWith "Real." || s == "Complex" || s.startsWith "Complex." || s.startsWith "MeasureTheory." || s.startsWith "intervalIntegral"
  unless forbidden.isEmpty do throwError "Forbidden scalar/analysis dependencies: {forbidden}"
  for name in names do
    let axioms ← Lean.collectAxioms name
    unless axioms.all (fun n => n == `propext || n == `Classical.choice || n == `Quot.sound) do
      throwError "Untrusted axioms in {name}: {axioms}"
  logInfo m!"PASS: {names.length} checked rational geometry endpoints; {deps.size} transitive declaration dependencies; no Mathlib real/complex scalars, measure or integration"
