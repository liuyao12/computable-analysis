import MathlibComparison.CartwrightQuadrature
import ComputableAnalysis.CartwrightTheorem

/-! The third route proves the same native statements. Its analysis is Mathlib's
integration by parts and an independent bridge for the actual native moment
program. The finite algebra and integer contradiction are shared verbatim with
the native routes. -/
namespace MathlibComparison.Cartwright
open ComputableAnalysis CartwrightIntegrationByParts CartwrightMoments
open Filter Topology RationalErrorCalculus

private lemma near_of_same_limit {x y : Nat→Rat} {r : ℝ}
    (hx : Tendsto (fun k=>(x k:ℝ)) atTop (𝓝 r))
    (hy : Tendsto (fun k=>(y k:ℝ)) atTop (𝓝 r)) : Near x y := by
  intro eps
  have he : (0:ℝ)<(eps.val:ℝ) := by exact_mod_cast eps.property
  have h : Tendsto (fun k=>(x k:ℝ)-(y k:ℝ)) atTop (𝓝 0) := by
    simpa only [sub_self] using hx.sub hy
  obtain ⟨N,hN⟩:=Metric.tendsto_atTop.1 h (eps.val:ℝ) he
  refine ⟨N,fun k hk=>?_⟩
  have hh:=le_of_lt (hN k hk)
  rw [Real.dist_eq,sub_zero] at hh
  have hc : ((qabs (x k-y k)):ℝ)=|(x k:ℝ)-(y k:ℝ)| := by rw [qabs_cast,Rat.cast_sub]
  rw [←hc] at hh
  exact_mod_cast hh

/-- The independent Mathlib argument supplies the common moment laws. -/
theorem laws : CartwrightMomentRecurrence.Laws where
  zero := by
    apply near_of_same_limit (r:=1)
    · have h:=CartwrightQuadrature.frequency_tendsto.mul (CartwrightQuadrature.sample_tendsto 0)
      simpa only [Rat.cast_mul,CartwrightAnalytic.base_zero] using h
    · simpa only [Rat.cast_one] using (tendsto_const_nhds : Tendsto (fun _:Nat=>(1:ℝ)) atTop (𝓝 (1:ℝ)))
  one := by
    apply near_of_same_limit (r:=2)
    · have h:=(CartwrightQuadrature.frequency_tendsto.pow 3).mul (CartwrightQuadrature.sample_tendsto 1)
      simpa only [Rat.cast_mul,Rat.cast_pow,CartwrightAnalytic.base_one] using h
    · simpa only [Rat.cast_ofNat] using (tendsto_const_nhds : Tendsto (fun _:Nat=>(2:ℝ)) atTop (𝓝 (2:ℝ)))
  recurrence := by
    intro n
    let A : Rat:=2*((n+2:Nat):Rat)*(2*(n:Rat)+3)
    let B : Rat:=4*((n+1:Nat):Rat)*((n+2:Nat):Rat)
    have hid : (A:ℝ)*CartwrightAnalytic.moment (n+1)-(B:ℝ)*CartwrightAnalytic.moment n=
        CartwrightAnalytic.frequency^2*CartwrightAnalytic.moment (n+2) := by
      dsimp [A,B]
      push_cast
      exact (CartwrightAnalytic.recurrence n).symm
    apply near_of_same_limit (r:=CartwrightAnalytic.frequency^2*CartwrightAnalytic.moment (n+2))
    · have h:=(CartwrightQuadrature.frequency_tendsto.pow 2).mul (CartwrightQuadrature.sample_tendsto (n+2))
      simpa only [Rat.cast_mul,Rat.cast_pow] using h
    · change Tendsto (fun k=>((A*CartwrightMoments.sample (n+1) k-B*CartwrightMoments.sample n k:Rat):ℝ)) atTop _
      simp only [Rat.cast_sub,Rat.cast_mul]
      rw [←hid]
      exact (tendsto_const_nhds.mul (CartwrightQuadrature.sample_tendsto (n+1))).sub
        (tendsto_const_nhds.mul (CartwrightQuadrature.sample_tendsto n))

theorem moment_viaMathlib (n : Nat) : CartwrightTheorem.MomentStatement n :=
  CartwrightTheorem.moment_of_laws laws n

theorem pi_squared_viaMathlib : CartwrightTheorem.PiSquaredStatement :=
  CartwrightTheorem.pi_squared_of_laws laws

end MathlibComparison.Cartwright
