import RationalArchimedesArithmetic

namespace ComputableAnalysis.RationalPolytopeVolume
open RationalConvexBodies
set_option maxHeartbeats 2000000

/-- Actual orthant-ball polytopal volumes lie in [0,1]. -/
theorem orthant_sample_volume_bounds {n : Nat} (V : Axioms n) (S : Finset (Point n))
    (haxes : ∀ i,axis i ∈ S) (hunit : ∀ q ∈ S,normSq q=1)
    (hpos : ∀ q ∈ S,∀ i,0 ≤ q i) :
    0 ≤ V.volume (orthantInnerPoly S) ∧
    V.volume (orthantInnerPoly S) ≤ V.volume (orthantOuterPoly S) ∧
    V.volume (orthantOuterPoly S) ≤ 1 := by
  have h := orthant_bracket_refinement V S S (fun _ h => h) haxes hunit hpos
  exact ⟨h.1,h.2.2.1,h.2.2.2.2⟩

/-- Unconditional finite geometric Archimedes comparison for the actual
point hulls and tangent-halfspace polytopes. Precision is a bound on a proved
bracket width, not an assumed sphere recurrence or desired volume inequality. -/
theorem finite_archimedes_polytope_comparison (n : Nat) (hn : 0 < n)
    (V : Axioms n) (W : Axioms 2) (Z : Axioms (n+2))
    (S : Finset (Point n)) (T : Finset (Point 2)) (U : Finset (Point (n+2)))
    (hSaxes : ∀ i,axis i ∈ S) (hSunit : ∀ q ∈ S,normSq q=1) (hSpos : ∀ q ∈ S,∀ i,0 ≤ q i)
    (hTaxes : ∀ i,axis i ∈ T) (hTunit : ∀ q ∈ T,normSq q=1) (hTpos : ∀ q ∈ T,∀ i,0 ≤ q i)
    (hUaxes : ∀ i,axis i ∈ U) (hUunit : ∀ q ∈ U,normSq q=1) (hUpos : ∀ q ∈ U,∀ i,0 ≤ q i)
    (N : Nat) (hN : 0 < N)
    (hwidth : V.volume (orthantOuterPoly S)-V.volume (orthantInnerPoly S) ≤ 1/(N:ℚ)^2) :
    Z.volume (orthantInnerPoly U) ≤
      2/((n+2:Nat):ℚ)*V.volume (orthantOuterPoly S)*W.volume (orthantOuterPoly T)+6/(N:ℚ) ∧
    2/((n+2:Nat):ℚ)*V.volume (orthantInnerPoly S)*W.volume (orthantInnerPoly T) ≤
      Z.volume (orthantOuterPoly U)+4/(N:ℚ) := by
  let P := orthantInnerPoly S
  let Q := orthantOuterPoly S
  let D := orthantInnerPoly T
  let E := orthantOuterPoly T
  have hP : ∀ x ∈ body P,normSq x ≤ 1 ∧ ∀ i,0 ≤ x i := by
    rw [show body P=RationalOrthantBodies.inner S from body_orthantInnerPoly S]
    exact RationalOrthantBodies.inner_subset_ball S hSunit hSpos
  have hQ : ∀ x,normSq x ≤ 1 → (∀ i,0 ≤ x i) → x ∈ body Q := by
    intro x hx hp
    rw [show body Q=RationalOrthantBodies.outer S from body_orthantOuterPoly S hSaxes]
    exact RationalOrthantBodies.ball_subset_outer S hSunit ⟨hx,hp⟩
  have hD : ∀ x ∈ body D,normSq x ≤ 1 ∧ ∀ i,0 ≤ x i := by
    rw [show body D=RationalOrthantBodies.inner T from body_orthantInnerPoly T]
    exact RationalOrthantBodies.inner_subset_ball T hTunit hTpos
  have hE : ∀ x,normSq x ≤ 1 → (∀ i,0 ≤ x i) → x ∈ body E := by
    intro x hx hp
    rw [show body E=RationalOrthantBodies.outer T from body_orthantOuterPoly T hTaxes]
    exact RationalOrthantBodies.ball_subset_outer T hTunit ⟨hx,hp⟩
  have hX : ∀ x ∈ body (orthantInnerPoly U),normSq x ≤ 1 ∧ ∀ i,0 ≤ x i := by
    rw [body_orthantInnerPoly]
    exact RationalOrthantBodies.inner_subset_ball U hUunit hUpos
  have hY : ∀ x,normSq x ≤ 1 → (∀ i,0 ≤ x i) → x ∈ body (orthantOuterPoly U) := by
    intro x hx hp
    rw [body_orthantOuterPoly U hUaxes]
    exact RationalOrthantBodies.ball_subset_outer U hUunit ⟨hx,hp⟩
  obtain ⟨l,u,hl0,hu0,hll,hll',huu,huu'⟩ := radial_disk_radii N hN
  have hb := radial_partition_bounds N hN
  have hlo := finite_inner_shell_comparison hn V W Z P S D (orthantOuterPoly U)
    hSaxes hSunit hP hD hY (radialLower N) (radialUpper N) l hb.1 hb.2.1 hl0 hll hb.2.2.2.2
  have hup := finite_outer_shell_comparison hn V W Z P Q E (orthantInnerPoly U)
    hP hQ hE hX (radialLower N) (radialUpper N) u hb.1 hb.2.1 hu0 hb.2.2.1 huu
    (radial_partition_covers N hN)
  have hSn := orthant_sample_volume_bounds V S hSaxes hSunit hSpos
  have hTn := orthant_sample_volume_bounds W T hTaxes hTunit hTpos
  have hL : 0 ≤ V.volume P := hSn.1
  have hLU : V.volume P ≤ V.volume Q := hSn.2.1
  have hU1 : V.volume Q ≤ 1 := hSn.2.2
  have hL1 : V.volume P ≤ 1 := le_trans hLU hU1
  have hD0 : 0 ≤ W.volume D := hTn.1
  have hD1 : W.volume D ≤ 1 := le_trans hTn.2.1 hTn.2.2
  have hE0 : 0 ≤ W.volume E := le_trans hTn.1 hTn.2.1
  have hE1 : W.volume E ≤ 1 := hTn.2.2
  have hNq : 0 < (N:ℚ) := by exact_mod_cast hN
  let δ : ℚ := 1/(N:ℚ)
  have hδ0 : 0 ≤ δ := (div_pos (by decide) hNq).le
  have hδ1 : δ ≤ 1 := by
    apply (div_le_one hNq).mpr
    exact_mod_cast (show 1 ≤ N by omega)
  have hweight := weighted_radial_shell_bounds n N hn hN (V.volume P) (V.volume Q) δ
    hL hLU hδ0 hδ1 l u hll hll' huu'
  have hgap : (N:ℚ)*(V.volume Q-V.volume P) ≤ δ := by
    have he := mul_le_mul_of_nonneg_left hwidth hNq.le
    have hr : (N:ℚ)*(1/(N:ℚ)^2)=δ := by dsimp [δ]; field_simp
    simpa only [hr] using he
  have hδU := mul_le_mul_of_nonneg_left hU1 hδ0
  have hδL := mul_le_mul_of_nonneg_left hL1 hδ0
  have hloCoeff : 2/((n+2:Nat):ℚ)*V.volume P-4*δ ≤
      ∑ i : Fin N,((radialUpper N i)^n*V.volume P-(radialLower N i)^n*V.volume Q)*(l i)^2 := by
    have h2 : 2/(N:ℚ)=2*δ := by simp [δ,div_eq_mul_inv]
    have he := hweight.1
    rw [h2] at he
    nlinarith
  have hupCoeff :
      (∑ i : Fin N,((radialUpper N i)^n*V.volume Q-(radialLower N i)^n*V.volume P)*(u i)^2) ≤
        2/((n+2:Nat):ℚ)*V.volume Q+6*δ := by
    have h3 : 3/(N:ℚ)=3*δ := by simp [δ,div_eq_mul_inv]
    have he := hweight.2
    rw [h3] at he
    nlinarith
  have hlowDisk := mul_le_mul_of_nonneg_right hloCoeff hD0
  have huppDisk := mul_le_mul_of_nonneg_right hupCoeff hE0
  have hDerr := mul_le_mul_of_nonneg_left hD1 (show 0 ≤ 4*δ by positivity)
  have hEerr := mul_le_mul_of_nonneg_left hE1 (show 0 ≤ 6*δ by positivity)
  rw [← Finset.sum_mul] at hlo hup
  change _ ≤ Z.volume (orthantOuterPoly U) at hlo
  change Z.volume (orthantInnerPoly U) ≤ _ at hup
  have h4 : 4/(N:ℚ)=4*δ := by simp [δ,div_eq_mul_inv]
  have h6 : 6/(N:ℚ)=6*δ := by simp [δ,div_eq_mul_inv]
  change Z.volume (orthantInnerPoly U) ≤ 2/((n+2:Nat):ℚ)*V.volume Q*W.volume E+6/(N:ℚ) ∧
    2/((n+2:Nat):ℚ)*V.volume P*W.volume D ≤ Z.volume (orthantOuterPoly U)+4/(N:ℚ)
  rw [h4,h6]
  constructor <;> nlinarith

end ComputableAnalysis.RationalPolytopeVolume

-- ARCHIMEDES AUDIT
#print axioms ComputableAnalysis.RationalPolytopeVolume.orthant_sample_volume_bounds
#print axioms ComputableAnalysis.RationalPolytopeVolume.finite_archimedes_polytope_comparison

open Lean
run_cmd do
  let names := [`ComputableAnalysis.RationalPolytopeVolume.orthant_sample_volume_bounds,
    `ComputableAnalysis.RationalPolytopeVolume.finite_archimedes_polytope_comparison]
  let env ← Lean.getEnv
  let deps := RationalProofAudit.audit env names
  let forbidden := deps.filter fun n => let s := n.toString; s == "Real" || s.startsWith "Real." || s == "Complex" || s.startsWith "Complex." || s.startsWith "MeasureTheory." || s.startsWith "intervalIntegral"
  unless forbidden.isEmpty do throwError "Forbidden scalar/analysis dependencies: {forbidden}"
  for name in names do
    let axioms ← Lean.collectAxioms name
    unless axioms.all (fun n => n == `propext || n == `Classical.choice || n == `Quot.sound) do
      throwError "Untrusted axioms in {name}: {axioms}"
  logInfo m!"PASS: {names.length} checked rational geometry endpoints; {deps.size} transitive declaration dependencies; no Mathlib real/complex scalars, measure or integration"
