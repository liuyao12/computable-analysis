import ComputableAnalysis.PowerImproperDivergence

/-! Exact convergence classifications on fixed dyadic exhaustions. Internal
function-specific error schedules are hidden beneath the public statements. -/
namespace ComputableAnalysis.PowerIntegral
open Integral FormalPowerSeries BinomialPower BinomialPower.Global

theorem zeroDyadicEndpoint_shrinks : ShrinksToZero zeroDyadicEndpoint := by
  intro eps
  obtain ⟨N,hN⟩ := IntegerPowerIntegral.dyadic_cutoff_shrinks eps
  refine ⟨N,fun n hn => ?_⟩
  exact hN (2*n+1) (by omega)

theorem zeroDyadic_hasIntegralLimit (p : Real) (hp : BelowOne p) :
    HasIntegralLimit (zeroDyadicExhaustion p) (zeroIntegral p hp) := by
  refine ⟨endpointTotal_valid (parameter p) (parameter_aboveOne hp),fun n => ⟨_,zeroDyadic_compact p n⟩,?_⟩
  intro eps
  obtain ⟨j,hj⟩ := endpointError_shrinks (endpointQ (parameter p) (parameter_aboveOne hp)) (endpointM (parameter p)) eps
  let e : QPos := ⟨endpointCutoff (endpointM (parameter p)) j,(endpointCutoff_bounds _ _).1⟩
  obtain ⟨N,hN⟩ := zeroDyadicEndpoint_shrinks e
  refine ⟨N,fun n hn J hJ => ?_⟩
  have ht := endpointTotal_within_cutoff (parameter p) (parameter_aboveOne hp) j
    (zeroDyadicEndpoint_bounds n).1 (hN n hn)
  have hc := zeroDyadic_compact p n
  have hcanon : Within (zeroIntegral p hp)
      (compact p (zeroDyadicEndpoint n) 1 (zeroDyadicEndpoint_bounds n).1 (zeroDyadicEndpoint_bounds n).2 (Rat.le_refl))
      (endpointError (endpointQ (parameter p) (parameter_aboveOne hp)) (endpointM (parameter p)) j) := by
    simpa only [zeroIntegral,compact,show (1 : Rat)-1=0 by decide +kernel] using ht
  have h := (hcanon.symm.congr_left hJ.valid hc.valid (hJ.unique hc)).symm
  have he := hj j (Nat.le_refl _)
  intro i k
  have hh := h i k
  constructor <;> grind only

theorem infinityDyadic_hasIntegralLimit (p : Real) (hp : AboveOne p) :
    HasIntegralLimit (infinityDyadicExhaustion p) (infinityIntegral p hp) := by
  refine ⟨endpointTotal_valid p hp,fun n => ⟨_,infinityDyadic_compact p n⟩,?_⟩
  intro eps
  obtain ⟨j,hj⟩ := endpointError_shrinks (endpointQ p hp) (endpointM p) eps
  let e : QPos := ⟨endpointCutoff (endpointM p) j,(endpointCutoff_bounds _ _).1⟩
  obtain ⟨N,hN⟩ := zeroDyadicEndpoint_shrinks e
  refine ⟨N,fun n hn J hJ => ?_⟩
  have ht := endpointTotal_within_cutoff p hp j (zeroDyadicEndpoint_bounds n).1 (hN n hn)
  have hc := infinityDyadic_compact p n
  have hcanon : Within (infinityIntegral p hp)
      (infinityCompact p 1 (1*IntegerPowerIntegral.dyadic (2*n+1)) (Rat.le_refl) (by
        have h := IntegerPowerIntegral.dyadic_mono (Nat.zero_le (2*n+1)); change 1 ≤ IntegerPowerIntegral.dyadic (2*n+1) at h; grind))
      (endpointError (endpointQ p hp) (endpointM p) j) := by
    simpa only [infinityIntegral,infinityCompact,zeroDyadicEndpoint,Rat.one_mul,
      show (1 : Rat)⁻¹=1 by decide +kernel,show (1 : Rat)-1=0 by decide +kernel] using ht
  have h := (hcanon.symm.congr_left hJ.valid hc.valid (hJ.unique hc)).symm
  have he := hj j (Nat.le_refl _)
  intro i k
  have hh := h i k
  constructor <;> grind only

/-- The zero-end improper integral exists exactly for `p<1`. -/
theorem zero_converges_iff (p : Real) :
    (∃ I, HasIntegralLimit (zeroDyadicExhaustion p) I) ↔ BelowOne p := by
  constructor
  · intro ⟨I,hI⟩
    by_cases hp : BelowOne p
    · exact hp
    exfalso
    apply zero_diverges p (fun _ n => ?_) I hI
    change 1 ≤ (p.compute n).hi
    by_cases h : 1 ≤ (p.compute n).hi
    · exact h
    · exact False.elim (hp ⟨n,by grind⟩)
  · intro hp
    exact ⟨zeroIntegral p hp,zeroDyadic_hasIntegralLimit p hp⟩

/-- The infinite-end improper integral exists exactly for `p>1`. -/
theorem infinity_converges_iff (p : Real) :
    (∃ I, HasIntegralLimit (infinityDyadicExhaustion p) I) ↔ AboveOne p := by
  constructor
  · intro ⟨I,hI⟩
    by_cases hp : AboveOne p
    · exact hp
    exfalso
    apply infinity_diverges p (fun n _ => ?_) I hI
    change (p.compute n).lo ≤ 1
    by_cases h : (p.compute n).lo ≤ 1
    · exact h
    · exact False.elim (hp ⟨n,by grind⟩)
  · intro hp
    exact ⟨infinityIntegral p hp,infinityDyadic_hasIntegralLimit p hp⟩

/-- Any supplied improper-integral value equals the explicit reciprocal. -/
theorem zero_supplied_exact (p : Real) (hp : BelowOne p) {I : RealRaw}
    (hI : HasIntegralLimit (zeroDyadicExhaustion p) I) :
    I.Equiv (RealRaw.positiveInv (RealRaw.sub (RealRaw.ofRat 1) p.preferred)
      (separationStage (parameter p) (parameter_aboveOne hp))) := by
  have hc := zeroDyadic_hasIntegralLimit p hp
  have he := zero_closedForm p hp
  have hpos : 0 < ((RealRaw.sub (RealRaw.ofRat 1) p.preferred).compute
      (separationStage (parameter p) (parameter_aboveOne hp))).lo := by
    have h := separationStage_spec (parameter p) (parameter_aboveOne hp)
    change 1 < 2-(p.compute (separationStage (parameter p) (parameter_aboveOne hp))).hi at h
    change 0 < 1-(p.compute (separationStage (parameter p) (parameter_aboveOne hp))).hi
    grind only
  exact RealRaw.equiv_trans hI.valid hc.valid
    (RealRaw.positiveInv_valid (RealRaw.sub_valid (RealRaw.ofRat_valid 1) p.valid) hpos) (hI.unique hc) he

theorem infinity_supplied_exact (p : Real) (hp : AboveOne p) {I : RealRaw}
    (hI : HasIntegralLimit (infinityDyadicExhaustion p) I) :
    I.Equiv (RealRaw.positiveInv (RealRaw.sub p.preferred (RealRaw.ofRat 1)) (separationStage p hp)) :=
  hI.unique (infinityDyadic_hasIntegralLimit p hp)

/-- The integral test, with both existence statements referring to independent
computations and their proved semantic specifications. -/
theorem series_integral_test (p : Real) :
    (∃ I, SumsTo p I) ↔ ∃ J, HasIntegralLimit (infinityDyadicExhaustion p) J :=
  (series_converges_iff p).trans (infinity_converges_iff p).symm

end ComputableAnalysis.PowerIntegral
