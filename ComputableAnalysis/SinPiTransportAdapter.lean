import ComputableAnalysis.SinPiIntegral

namespace ComputableAnalysis

namespace SinPiIntegral

/-! The route certificate already contains enough data to identify the actual
finite rectangle computation with the named nested-radical left sum.  This is
the missing bookkeeping adapter between the abstract `Integral.Construction`
and the explicit dyadic sum; no convergence or completed-real argument is
used. -/

theorem DyadicNestedRadicalRouteSearchData.integral_compute_eq_leftSum
    {S : ArctanSinPiConstruction}
    {pub : Integral.Construction S.onHalf.toRealFunRaw
      0 ((1 : Rat) / 2)}
    (d : DyadicNestedRadicalRouteSearchData S pub) (n : Nat) :
    (Integral.integral d.evaluator 0 ((1 : Rat) / 2) d.integral).compute n =
      dyadicNestedRadicalLeftSum n := by
  change riemannLeftInterval d.evaluator 0 ((1 : Rat) / 2)
      (d.integral.plan n).subdivisions (d.integral.plan n).evalPrecision =
    dyadicNestedRadicalLeftSum n
  rw [← d.same_plan, d.dyadic_plan]
  unfold Integral.staticDyadicPlan Integral.staticDyadicSubdivisions
    dyadicNestedRadicalLeftSum
  unfold riemannLeftInterval
  unfold QInterval.addInterval
  have hmesh : 0 <= mesh 0 ((1 : Rat) / 2) (2 ^ n) :=
    mesh_nonneg_of_le (Nat.pow_pos (by omega : 0 < 2)) (by native_decide)
  simp [QInterval.scaleByRat, hmesh]
  have hfold : forall (xs : List Nat),
      (forall k, k ∈ xs -> k < 2 ^ n) ->
      forall (acc : QInterval),
      (xs.foldl
        (fun acc k =>
          let I := d.evaluator.compute
            (leftPoint 0 ((1 : Rat) / 2) (2 ^ n) k) n
          { lo := acc.lo + mesh 0 ((1 : Rat) / 2) (2 ^ n) * I.lo,
            hi := acc.hi + mesh 0 ((1 : Rat) / 2) (2 ^ n) * I.hi }) acc) =
      (xs.foldl
        (fun acc k =>
          let I := dyadicNestedRadicalStageSinAt n k
          { lo := acc.lo + mesh 0 ((1 : Rat) / 2) (2 ^ n) * I.lo,
            hi := acc.hi + mesh 0 ((1 : Rat) / 2) (2 ^ n) * I.hi }) acc) := by
    intro xs
    induction xs with
    | nil =>
        intro _hmem acc
        rfl
    | cons k ks ih =>
        intro hmem acc
        dsimp
        have hkpub : k < (pub.plan n).subdivisions := by
          rw [d.dyadic_plan]
          simpa [Integral.staticDyadicPlan, Integral.staticDyadicSubdivisions]
            using hmem k (by simp)
        have hsample :
            d.evaluator.compute
                (leftPoint 0 ((1 : Rat) / 2) (2 ^ n) k) n =
              dyadicNestedRadicalStageSinAt n k := by
          simpa [d.dyadic_plan, Integral.staticDyadicPlan,
            Integral.staticDyadicSubdivisions] using
            d.evaluator_sample n k hkpub
        rw [hsample]
        exact ih (fun j hj => hmem j (by simp [hj])) _
  exact hfold (List.range (2 ^ n))
    (by intro k hk; exact List.mem_range.mp hk) { lo := 0, hi := 0 }

theorem DyadicNestedRadicalRouteSearchData.integral_equiv_reciprocalPi_of_stieltjes_overlap
    {S : ArctanSinPiConstruction}
    {pub : Integral.Construction S.onHalf.toRealFunRaw
      0 ((1 : Rat) / 2)}
    (d : DyadicNestedRadicalRouteSearchData S pub)
    (hoverlap : forall n,
      QInterval.Overlaps
        (dyadicNestedRadicalLeftSum n)
        (sinPiStieltjesIntegral.compute n)) :
    (Integral.integral d.evaluator 0 ((1 : Rat) / 2)
      d.integral).Equiv reciprocalPiRaw := by
  let candidate : RealRaw := dyadicNestedRadicalIntegralRaw
  let anchor : RealRaw := sinPiStieltjesIntegral
  let stabilized : RealRaw := dyadicNestedRadicalIntegralRaw_stabilized
  have hcandidate_anchor : candidate.Equiv anchor := by
    exact dyadicNestedRadicalIntegralRaw_equiv_of_overlap anchor hoverlap
  have hanchor : anchor.Valid := by
    exact sinPiStieltjesIntegral_valid
  have hstabilized : stabilized.Valid := by
    exact dyadicNestedRadicalIntegralRaw_stabilized_valid_of_overlap hoverlap
  have hcontains : forall n, (stabilized.compute n).ContainsInterval
      (anchor.compute n) := by
    intro n
    exact RealRaw.prefixStabilize_contains_anchor hanchor
      hcandidate_anchor (fun m => Rat.le_refl) n
  have hroute_stabilized :
      (Integral.integral d.evaluator 0 ((1 : Rat) / 2)
        d.integral).Equiv stabilized := by
    apply RealRaw.sameStageOverlap_equiv
    intro n
    apply (RealRaw.compareAt_overlap_iff _ _ n n).2
    have hroute := d.integral_compute_eq_leftSum n
    have hcand := (RealRaw.compareAt_overlap_iff candidate anchor n n).1
      (hcandidate_anchor n)
    have hstab := hcontains n
    rw [hroute]
    exact ⟨Rat.le_trans hcand.1 hstab.2,
      Rat.le_trans hstab.1 hcand.2⟩
  exact RealRaw.equiv_trans
    (FTC.integral_valid_of_construction d.integral)
    hstabilized reciprocalPiRaw_valid hroute_stabilized
    (dyadicNestedRadicalIntegralRaw_stabilized_equiv_reciprocalPi_of_overlap
      hoverlap)

/-! The endpoint and tangent-chart routes have the same computable value.  This
adapter packages the resulting transitivity step so a future static FTC proof
only has to identify its endpoint raw with `reciprocalPiRaw`; it does not need
to repeat the chart-value algebra. -/

theorem ArctanSinPiConstruction.tangentChartTransport_of_staticFTC_of_endpoint_equiv
    (S : ArctanSinPiConstruction)
    (F : RealFunRaw)
    (h : StaticDyadicEffectiveFTC F S.onHalf.toRealFunRaw
      0 ((1 : Rat) / 2))
    (c : Integral.Construction S.onHalf.toRealFunRaw
      0 ((1 : Rat) / 2))
    (hplan : c.plan = FTC.integralPlanOfStaticDyadicEffectiveFTC h)
    (endpoint : FTC.EndpointScheduleAgreement F 0 ((1 : Rat) / 2)
      (FTC.endpointRawOfEffectiveFTC h.toEffectiveFTC))
    (hendpoint :
      (endpointDifferenceRaw F 0 ((1 : Rat) / 2)
        endpoint.endpoint_valid).Equiv reciprocalPiRaw) :
    S.TangentChartTransport c := by
  have hendpointValid :
      (endpointDifferenceRaw F 0 ((1 : Rat) / 2)
        endpoint.endpoint_valid).Valid := by
    simpa [endpointDifferenceRaw, RealRaw.Valid] using endpoint.endpoint_valid
  have htoChart :
      (endpointDifferenceRaw F 0 ((1 : Rat) / 2)
        endpoint.endpoint_valid).Equiv tangentChartIntegral :=
    RealRaw.equiv_trans hendpointValid reciprocalPiRaw_valid
      tangentChartIntegral_valid hendpoint
      (RealRaw.equiv_symm tangentChartIntegral_equiv_reciprocalPi)
  exact S.tangentChartTransport_of_staticFTC F h c hplan endpoint htoChart

end SinPiIntegral

end ComputableAnalysis
