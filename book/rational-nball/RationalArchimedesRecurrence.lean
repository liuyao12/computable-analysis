import RationalArchimedesFiniteComparison
import ComputableAnalysis.BallArchimedesEquivalence

namespace ComputableAnalysis.RationalPolytopeVolume
open RationalConvexBodies
set_option maxHeartbeats 3000000

/-- Archimedes' exact general-dimensional recurrence for supplied valid
exhaustions by the actual rational inner point hulls and outer tangent cuts.
The finite comparison is proved above, not a hypothesis of this theorem. -/
theorem geometric_archimedes_recurrence
    (n : Nat) (hn : 0 < n) (V : ∀ d,Axioms d)
    (samples : ∀ d,Nat → Finset (Point d))
    (haxes : ∀ d s i,axis i ∈ samples d s)
    (hunit : ∀ d s q,q ∈ samples d s → normSq q=1)
    (hpositive : ∀ d s q,q ∈ samples d s → ∀ i,0 ≤ q i)
    (ball : Nat → RealRaw) (hvalid : ∀ d,(ball d).Valid)
    (hlo : ∀ d s,((ball d).compute s).lo=(2:ℚ)^d*(V d).volume (orthantInnerPoly (samples d s)))
    (hhi : ∀ d s,((ball d).compute s).hi=(2:ℚ)^d*(V d).volume (orthantOuterPoly (samples d s))) :
    (ball (n+2)).Equiv (RealRaw.scaleRat (2/((n+2:Nat):ℚ)) (ball 2*ball n)) := by
  classical
  let product := ball 2*ball n
  let c : ℚ := 2/((n+2:Nat):ℚ)
  let B : ℚ := (2:ℚ)^(n+2)
  have hc : 0 ≤ c := (div_pos (by decide) (by positivity)).le
  have hB : 0 < B := pow_pos (by decide) _
  have hbounds (d s : Nat) : 0 ≤ ((ball d).compute s).lo ∧ ((ball d).compute s).hi ≤ (2:ℚ)^d := by
    have hv := orthant_sample_volume_bounds (V d) (samples d s) (haxes d s) (hunit d s) (hpositive d s)
    rw [hlo,hhi]
    constructor
    · exact mul_nonneg (pow_pos (by decide) d).le hv.1
    · simpa using mul_le_mul_of_nonneg_left hv.2.2 (pow_pos (by decide : (0:ℚ) < 2) d).le
  have hpvalid : product.Valid := RealRaw.mul_valid_of_nonneg_bounded
    (hvalid 2) (hvalid n) (pow_pos (by decide) 2) (pow_pos (by decide) n) (hbounds 2) (hbounds n)
  have hscaled := RealRaw.scaleRat_valid_of_nonneg hc hpvalid
  have hproduct (s : Nat) : product.compute s =
      {lo := B*(V n).volume (orthantInnerPoly (samples n s))*(V 2).volume (orthantInnerPoly (samples 2 s)),
       hi := B*(V n).volume (orthantOuterPoly (samples n s))*(V 2).volume (orthantOuterPoly (samples 2 s))} := by
    have he : product.compute s =
      {lo := ((ball 2).compute s).lo*((ball n).compute s).lo,
       hi := ((ball 2).compute s).hi*((ball n).compute s).hi} := by
      change QBox.mulRealInterval _ _ _ _ = _
      exact QBox.mulRealInterval_of_nonneg (hbounds 2 s).1
        (RealRaw.interval_order_of_valid _ (hvalid 2) s) (hbounds n s).1
        (RealRaw.interval_order_of_valid _ (hvalid n) s)
    rw [he,hlo,hhi,hlo,hhi]
    have hpow : B=(2:ℚ)^2*(2:ℚ)^n := by dsimp [B]; rw [pow_add]; ring
    rw [hpow]
    congr 1 <;> ring
  apply RealRaw.equiv_of_endpoint_error (hvalid (n+2)) hscaled
    (fun s => 6*B/((s+1:Nat):ℚ))
    (RationalArchimedesModulus.shrinksToZero_of_ratOverSuccBound (fun _ => Rat.le_refl))
  intro s
  let N := s+1
  have hN : 0 < N := by dsimp [N]; omega
  have hNq : 0 < (N:ℚ) := by exact_mod_cast hN
  let eps : QPos := ⟨(2:ℚ)^n/(N:ℚ)^2,div_pos (pow_pos (by decide) _) (sq_pos_of_pos hNq)⟩
  obtain ⟨K,hK⟩ := (hvalid n).2.2 eps
  let t := max K s
  have hst : s ≤ t := Nat.le_max_right _ _
  have hKt : K ≤ t := Nat.le_max_left _ _
  have hwidth : (V n).volume (orthantOuterPoly (samples n t))-
      (V n).volume (orthantInnerPoly (samples n t)) ≤ 1/(N:ℚ)^2 := by
    have he := hK t hKt
    change ((ball n).compute t).hi-((ball n).compute t).lo ≤ (2:ℚ)^n/(N:ℚ)^2 at he
    rw [hhi,hlo] at he
    have hpow : 0 < (2:ℚ)^n := pow_pos (by decide) _
    apply Rat.le_of_mul_le_mul_left (c := (2:ℚ)^n)
    · convert he using 1 <;> ring
    · exact hpow
  have hgeom := finite_archimedes_polytope_comparison n hn (V n) (V 2) (V (n+2))
    (samples n t) (samples 2 t) (samples (n+2) s)
    (haxes n t) (hunit n t) (hpositive n t)
    (haxes 2 t) (hunit 2 t) (hpositive 2 t)
    (haxes (n+2) s) (hunit (n+2) s) (hpositive (n+2) s) N hN hwidth
  have hupper := mul_le_mul_of_nonneg_left hgeom.1 hB.le
  have hlower := mul_le_mul_of_nonneg_left hgeom.2 hB.le
  have hnest := hpvalid.2.1 s t hst
  have hhiNest := mul_le_mul_of_nonneg_left hnest.2.2 hc
  have hloNest := mul_le_mul_of_nonneg_left hnest.1 hc
  rw [hproduct,hproduct] at hhiNest hloNest
  unfold RealRaw.scaleRat RealRaw.scaleRatCompute
  simp only [hc,if_true]
  rw [hproduct,hlo,hhi]
  change B*(V (n+2)).volume (orthantInnerPoly (samples (n+2) s)) ≤
      c*(B*(V n).volume (orthantOuterPoly (samples n s))*(V 2).volume (orthantOuterPoly (samples 2 s)))+
        6*B/(N:ℚ) ∧
    c*(B*(V n).volume (orthantInnerPoly (samples n s))*(V 2).volume (orthantInnerPoly (samples 2 s))) ≤
      B*(V (n+2)).volume (orthantOuterPoly (samples (n+2) s))+6*B/(N:ℚ)
  have he4 : B*(4/(N:ℚ)) ≤ 6*B/(N:ℚ) := by
    have he := mul_nonneg hB.le (inv_nonneg.mpr hNq.le)
    simp only [div_eq_mul_inv]
    nlinarith [he]
  dsimp [c] at hhiNest hloNest ⊢
  simp only [div_eq_mul_inv] at hupper hlower hhiNest hloNest he4 ⊢
  constructor <;> nlinarith

end ComputableAnalysis.RationalPolytopeVolume

-- ARCHIMEDES AUDIT
#print axioms ComputableAnalysis.RationalPolytopeVolume.geometric_archimedes_recurrence

open Lean
run_cmd do
  let names := [`ComputableAnalysis.RationalPolytopeVolume.geometric_archimedes_recurrence]
  let env ← Lean.getEnv
  let deps := RationalProofAudit.audit env names
  let forbidden := deps.filter fun n => let s := n.toString; s == "Real" || s.startsWith "Real." || s == "Complex" || s.startsWith "Complex." || s.startsWith "MeasureTheory." || s.startsWith "intervalIntegral"
  unless forbidden.isEmpty do throwError "Forbidden scalar/analysis dependencies: {forbidden}"
  for name in names do
    let axioms ← Lean.collectAxioms name
    unless axioms.all (fun n => n == `propext || n == `Classical.choice || n == `Quot.sound) do
      throwError "Untrusted axioms in {name}: {axioms}"
  logInfo m!"PASS: {names.length} checked rational geometry endpoints; {deps.size} transitive declaration dependencies; no Mathlib real/complex scalars, measure or integration"
