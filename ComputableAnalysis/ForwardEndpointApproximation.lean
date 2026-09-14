import ComputableAnalysis.Calculus

/-!
# Endpoint approximation through a represented input

A certified forward equation controls rational points in all sufficiently
late input intervals.  The input's native schedule is not changed.  An
adaptive application stage is used only as a witness inside this proof.
-/

namespace ComputableAnalysis
namespace ForwardEndpointApproximation

private theorem overlap_chain_bound
    (A M B : QInterval) (hAM : A.Overlaps M) (hMB : M.Overlaps B)
    {a b : Rat} (ha0 : A.lo <= a) (ha1 : a <= A.hi)
    (hb0 : B.lo <= b) (hb1 : b <= B.hi) :
    qabs (a-b) <= A.width+M.width+B.width := by
  apply qabs_le_of_neg_le_le
  all_goals
    unfold QInterval.Overlaps at hAM hMB
    unfold QInterval.width
    grind

/-- A pointwise equivalent rational-input evaluator, with a uniform output
width bound, approximates a represented forward target at every sufficiently
late input stage.  No derivative assumption appears here. -/
theorem eventually_close
    (F : ContinuousFunctionOnInterval)
    (G : RealRaw) (hG : G.Valid)
    (hsource : ∀ n, subintervalOf (G.compute n)
      F.function.lower F.function.upper)
    (Y : RealRaw) (hY : Y.Valid)
    (hforward : (F.applyRealRaw G hG hsource).Equiv Y)
    (A : Rat -> RealRaw)
    (hA : ∀ u, inDomainInterval F.function.lower F.function.upper u ->
      (A u).Valid)
    (hFA : ∀ u (hu : inDomainInterval F.function.lower F.function.upper u),
      ({ compute := F.function.compute u hu } : RealRaw).Equiv (A u))
    (hwidth : ∀ eps : QPos, ∃ N : Nat,
      ∀ u, inDomainInterval F.function.lower F.function.upper u ->
      ∀ n : Nat, N <= n -> ((A u).compute n).width <= eps.val)
    (eps : QPos) :
    ∃ N : Nat, ∀ n : Nat, N <= n -> ∀ u : Rat,
      (G.compute n).lo <= u -> u <= (G.compute n).hi ->
      ∀ a b : Rat,
        ((A u).compute n).lo <= a -> a <= ((A u).compute n).hi ->
        (Y.compute n).lo <= b -> b <= (Y.compute n).hi ->
        qabs (a-b) <= eps.val := by
  let eta : QPos :=
    { val := eps.val/3
      property := by
        rw [Rat.div_def]
        exact Rat.mul_pos eps.property ((Rat.inv_pos).2 (by decide)) }
  let V := F.applyRealRaw G hG hsource
  have hV : V.Valid := F.applyRealRaw_valid G hG hsource
  obtain ⟨K, hK⟩ := hV.2.2 eta
  obtain ⟨NY, hNY⟩ := hY.2.2 eta
  obtain ⟨NA, hNA⟩ := hwidth eta
  let s := F.inputStage G hG K
  refine ⟨max s (max NY NA), ?_⟩
  intro n hn u hu0 hu1 a b ha0 ha1 hb0 hb1
  have hsn : s <= n := by omega
  have hyn : NY <= n := by omega
  have han : NA <= n := by omega
  have hu : inDomainInterval F.function.lower F.function.upper u :=
    ⟨Rat.le_trans (hsource n).1 hu0,
      Rat.le_trans hu1 (hsource n).2.2⟩
  have hnest := hG.2.1 s n hsn
  have hus0 : (G.compute s).lo <= u := Rat.le_trans hnest.1 hu0
  have hus1 : u <= (G.compute s).hi := Rat.le_trans hu1 hnest.2.2
  have hcandidate := F.regular.contains_point_values
    (G.compute s) (hsource s) u hu K hus0 hus1
  have hstable := F.applyRealRaw_contains_candidate G hG hsource K
  have hcontains : (V.compute K).ContainsInterval (F.function.compute u hu K) :=
    ⟨Rat.le_trans hstable.1 hcandidate.1,
      Rat.le_trans hcandidate.2 hstable.2⟩
  let P : RealRaw := { compute := F.function.compute u hu }
  have hP : P.Valid := F.function.valid_on u (F.function.defined_on u hu)
  have hPA := (RealRaw.compareAt_overlap_iff P (A u) K n).1
    (RealRaw.allStagesOverlap_of_equiv hP (hA u hu) (hFA u hu) K n)
  have hAV : ((A u).compute n).Overlaps (V.compute K) :=
    ⟨Rat.le_trans hPA.2 hcontains.2, Rat.le_trans hcontains.1 hPA.1⟩
  have hVY := (RealRaw.compareAt_overlap_iff V Y K n).1
    (RealRaw.allStagesOverlap_of_equiv hV hY hforward K n)
  have hbound := overlap_chain_bound ((A u).compute n) (V.compute K)
    (Y.compute n) hAV hVY ha0 ha1 hb0 hb1
  have hwA := hNA u hu n han
  have hwV := hK K (Nat.le_refl K)
  have hwY := hNY n hyn
  have hsum : eta.val+eta.val+eta.val = eps.val := by
    dsimp [eta]
    simp only [Rat.div_def]
    grind
  grind

end ForwardEndpointApproximation
end ComputableAnalysis
