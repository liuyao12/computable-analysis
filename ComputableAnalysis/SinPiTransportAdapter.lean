import ComputableAnalysis.SinPiIntegral

namespace ComputableAnalysis

namespace SinPiIntegral

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
