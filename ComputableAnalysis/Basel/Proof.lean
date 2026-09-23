import ComputableAnalysis.Basel.ZetaEstimate
import ComputableAnalysis.Basel
import ComputableAnalysis.LeibnizPi

/-! Basel's identity for the independently defined geometric pi and
reciprocal-square interval computations. No completed real line is used. -/
namespace ComputableAnalysis.Basel
open DirichletSeries

 theorem leibniz_bounds (n : Nat) :
    0≤(leibnizRaw.compute n).lo ∧ (leibnizRaw.compute n).hi≤4 := by
  have hl := alternating_decreasing b (2*n) b_nonneg (fun k=>b_antitone (by omega))
  have hh := alternating_decreasing b (2*n+1) b_nonneg (fun k=>b_antitone (by omega))
  have hc : leibnizRaw.compute n = {lo:=4*B (2*n), hi:=4*B (2*n+1)} := by
    change {lo:=4*(Series.AlternatingRaw.leibnizAlternatingRaw.interval n).lo,
      hi:=4*(Series.AlternatingRaw.leibnizAlternatingRaw.interval n).hi} = _
    rw [Series.AlternatingRaw.interval_eq_endpoints]; rfl
  have hz : b 0=1 := by simp [b, Series.leibnizTerm, Rat.div_def]; grind only
  rw [hz] at hl hh
  rw [hc]; dsimp [B]; grind only

 theorem leibniz_square_lo (n : Nat) :
    ((piSquaredOverSixRaw leibnizRaw).compute n).lo = (8/3)*(B (2*n)*B (2*n)) := by
  have ho := RealRaw.interval_order_of_valid leibnizRaw leibnizRaw_valid n
  have hn := (leibniz_bounds n).1
  have hc : ((leibnizRaw*leibnizRaw).compute n) =
      {lo := (leibnizRaw.compute n).lo*(leibnizRaw.compute n).lo,
       hi := (leibnizRaw.compute n).hi*(leibnizRaw.compute n).hi} := by
    exact QBox.mulRealInterval_self_of_nonneg hn ho
  have hl : (leibnizRaw.compute n).lo=4*B (2*n) := by
    change 4*(Series.AlternatingRaw.leibnizAlternatingRaw.interval n).lo = _
    rw [Series.AlternatingRaw.interval_eq_endpoints]; rfl
  change (if (0:Rat)≤1/6 then (1/6)*((leibnizRaw*leibnizRaw).compute n).lo
    else (1/6)*((leibnizRaw*leibnizRaw).compute n).hi) = _
  rw [if_pos (by grind only [Rat.div_def]), hc]
  simp only []
  rw [hl]; grind only [Rat.div_def]

/-- The reciprocal-square series equals the square of the Leibniz
computation divided by six; the comparison has a finite rational modulus. -/
 theorem eulerBasel_leibniz : EulerBaselStatement leibnizRaw := by
  apply equiv_of_close_lower_refinements baselSeriesRaw_valid
    (piSquaredOverSixRaw_valid_of_nonneg_bounded leibnizRaw_valid (B:=4) (by decide) leibniz_bounds)
  intro stage eps
  have hs : ShrinksToZero (fun k=>16/((k+1:Nat):Rat)) :=
    shrinksToZero_of_natOverSuccBound (C:=16) (fun _=>Rat.le_refl)
  obtain ⟨N,hN⟩ := hs eps
  let m := N+stage+1
  have mp : 0<m := by dsimp [m]; omega
  have ml : stage≤m := by dsimp [m]; omega
  have ms : m≤m*m := by
    have h := Nat.mul_le_mul_left m (show 1≤m by omega)
    simpa using h
  refine ⟨2*(m*m),m*m,by omega,by omega,?_⟩
  rw [leibniz_square_lo]
  change qabs (zetaTwoPartial (2*(m*m))-(8/3)*(B (2*(m*m))*B (2*(m*m))))≤eps.val
  exact Rat.le_trans (zeta_leibniz_square_budget m mp) (hN (N+stage) (by omega))

/-- **Basel's theorem**, with geometric pi and the independently defined
reciprocal-square series. All bridges are proved, with no analytic premise. -/
 theorem eulerBasel : eulerBasel_geometricPi := by
  have hv := piSquaredOverSixRaw_valid_of_nonneg_bounded leibnizRaw_valid
    (B:=4) (by decide) leibniz_bounds
  exact RealRaw.equiv_trans baselSeriesRaw_valid hv geometricPiSquaredOverSixRaw_valid
    eulerBasel_leibniz
    (piSquaredOverSixRaw_equiv_of_nonneg leibnizRaw_valid
      PiProofs.AreaLoopValidity.areaValid (fun n=>(leibniz_bounds n).1)
      (fun n=>(piCircleArea_nonneg_bounded_by_four n).1) leibnizRaw_equiv_geom)

end ComputableAnalysis.Basel
