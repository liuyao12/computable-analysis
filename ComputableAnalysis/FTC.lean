import ComputableAnalysis.Differential
import ComputableAnalysis.Basic

/-!
# Effective fundamental theorem of calculus

This file contains the project-facing FTC theorem shape.  The concrete
calculus examples have deliberately been removed: the point here is the
general bridge from an `EffectiveFTC` certificate to equality of computable
real algorithms.
-/

namespace ComputableAnalysis

namespace FTC

theorem one_div_den_succ_le_of_pos {q : Rat} (hq : 0 < q) :
    1 / (((q.den + 1 : Nat) : Rat)) <= q := by
  let d : Rat := ((q.den + 1 : Nat) : Rat)
  have hdpos : 0 < d := by
    dsimp [d]
    exact (Rat.natCast_pos).2 (Nat.succ_pos q.den)
  have hnumpos : 0 < q.num := rat_num_pos_of_pos hq
  have hnumgeInt : (1 : Int) <= q.num := by omega
  have hnumge : (1 : Rat) <= (q.num : Rat) := by
    exact_mod_cast hnumgeInt
  have hqd :
      q * d = (q.num : Rat) + q := by
    dsimp [d]
    have hden := rat_den_mul_self q
    grind [Rat.mul_add, Rat.mul_assoc, Rat.mul_comm]
  have hqd_ge_one : 1 <= q * d := by
    rw [hqd]
    grind [Rat.le_of_lt hq]
  apply Rat.le_of_mul_le_mul_right (c := d)
  · calc
      (1 / d) * d = 1 := by
        rw [Rat.div_def]
        have hdne : d ≠ 0 := Rat.ne_of_gt hdpos
        grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
      _ <= q * d := hqd_ge_one
  · exact hdpos

theorem one_div_nat_antitone {n m : Nat}
    (hn : 0 < n) (hm : 0 < m) (hnm : n <= m) :
    (1 / (m : Rat)) <= 1 / (n : Rat) := by
  apply Rat.le_of_mul_le_mul_right (c := (n : Rat) * (m : Rat))
  · calc
      (1 / (m : Rat)) * ((n : Rat) * (m : Rat)) = (n : Rat) := by
        have hmne : (m : Rat) ≠ 0 :=
          Rat.ne_of_gt ((Rat.natCast_pos).2 hm)
        grind [Rat.div_def, Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
      _ <= (m : Rat) := by
        exact_mod_cast hnm
      _ = (1 / (n : Rat)) * ((n : Rat) * (m : Rat)) := by
        have hnne : (n : Rat) ≠ 0 :=
          Rat.ne_of_gt ((Rat.natCast_pos).2 hn)
        grind [Rat.div_def, Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
  · exact Rat.mul_pos ((Rat.natCast_pos).2 hn) ((Rat.natCast_pos).2 hm)

def requestedPrecision (n : Nat) : QPos :=
  if hn : n = 0 then
    { val := 1, property := by native_decide }
  else
    { val := (1 / (n : Rat)), property := one_div_nat_pos (Nat.pos_of_ne_zero hn) }

def riemannComputeOfEffectiveFTC
    {F dF : RealFunRaw} {a b : Rat}
    (h : EffectiveFTC F dF a b) : Nat -> QInterval :=
  fun n =>
    let eps := requestedPrecision n
    riemannLeftInterval dF a b
      (h.chooseN eps)
      (h.chooseEvalPrecision eps)

def endpointComputeOfEffectiveFTC
    {F dF : RealFunRaw} {a b : Rat}
    (h : EffectiveFTC F dF a b) : Nat -> QInterval :=
  fun n =>
    let eps := requestedPrecision n
    endpointDifferenceInterval F a b (h.chooseEvalPrecision eps)

def riemannRawOfEffectiveFTC
    {F dF : RealFunRaw} {a b : Rat}
    (h : EffectiveFTC F dF a b) : RealRaw where
  compute := riemannComputeOfEffectiveFTC h

def endpointRawOfEffectiveFTC
    {F dF : RealFunRaw} {a b : Rat}
    (h : EffectiveFTC F dF a b) : RealRaw where
  compute := endpointComputeOfEffectiveFTC h

/-- Agreement between a scheduled endpoint-difference algorithm and the
canonical endpoint-difference raw real.

An `EffectiveFTC` chooses an endpoint evaluation precision as part of its
finite schedule.  To turn the scheduled FTC bridge into the canonical
endpoint formula `F(b)-F(a)`, we separately prove that the scheduled endpoint
raw real is a valid representative of the canonical endpoint-difference
algorithm. -/
structure EndpointScheduleAgreement
    (F : RealFunRaw) (a b : Rat) (scheduledEndpoint : RealRaw) where
  endpoint_valid :
    RealRaw.ValidCompute (endpointDifferenceCompute F a b)
  scheduled_valid : scheduledEndpoint.Valid
  equivalent :
    scheduledEndpoint.Equiv
      (endpointDifferenceRaw F a b endpoint_valid)

namespace EndpointScheduleAgreement

theorem endpoint_raw_valid
    {F : RealFunRaw} {a b : Rat} {scheduledEndpoint : RealRaw}
    (h : EndpointScheduleAgreement F a b scheduledEndpoint) :
    (endpointDifferenceRaw F a b h.endpoint_valid).Valid := by
  simpa [endpointDifferenceRaw, RealRaw.Valid] using h.endpoint_valid

end EndpointScheduleAgreement

/-- Build endpoint-schedule agreement for an `EffectiveFTC` when its endpoint
precision choices are a cofinal monotone stage schedule for the canonical
endpoint-difference raw real. -/
theorem endpointScheduleAgreement_of_effectiveFTC_stageSchedule
    {F dF : RealFunRaw} {a b : Rat}
    (h : EffectiveFTC F dF a b)
    (hendpoint : RealRaw.ValidCompute (endpointDifferenceCompute F a b))
    (sigma : RealRaw.StageSchedule)
    (hsigma :
      forall n, h.chooseEvalPrecision (requestedPrecision n) = sigma.stage n) :
    EndpointScheduleAgreement F a b (endpointRawOfEffectiveFTC h) := by
  let endpoint : RealRaw := endpointDifferenceRaw F a b hendpoint
  have hendpointValid : endpoint.Valid := by
    simpa [endpoint, endpointDifferenceRaw, RealRaw.Valid] using hendpoint
  refine
    { endpoint_valid := hendpoint
      scheduled_valid := ?_
      equivalent := ?_ }
  · have hsched := RealRaw.schedule_valid endpoint hendpointValid sigma
    have hcompute :
        endpointComputeOfEffectiveFTC h =
          fun n => endpointDifferenceCompute F a b (sigma.stage n) := by
      funext n
      simp [endpointComputeOfEffectiveFTC, endpointDifferenceCompute, hsigma]
    simpa [endpointRawOfEffectiveFTC, RealRaw.Valid, hcompute] using hsched
  · intro n
    have hall := RealRaw.allStagesOverlap_refl endpoint hendpointValid
      (sigma.stage n) n
    have hover := (RealRaw.compareAt_overlap_iff endpoint endpoint
      (sigma.stage n) n).1 hall
    apply (RealRaw.compareAt_overlap_iff
      (endpointRawOfEffectiveFTC h)
      (endpointDifferenceRaw F a b hendpoint) n n).2
    simpa [endpointRawOfEffectiveFTC, endpointComputeOfEffectiveFTC,
      endpoint, endpointDifferenceRaw, hsigma] using hover

/-- Static-dyadic endpoint-schedule agreement is the same endpoint schedule
agreement after forgetting to `EffectiveFTC`. -/
theorem endpointScheduleAgreement_of_staticDyadicEffectiveFTC_stageSchedule
    {F dF : RealFunRaw} {a b : Rat}
    (h : StaticDyadicEffectiveFTC F dF a b)
    (hendpoint : RealRaw.ValidCompute (endpointDifferenceCompute F a b))
    (sigma : RealRaw.StageSchedule)
    (hsigma :
      forall n, h.chooseEvalPrecision (requestedPrecision n) = sigma.stage n) :
    EndpointScheduleAgreement F a b
      (endpointRawOfEffectiveFTC h.toEffectiveFTC) :=
  endpointScheduleAgreement_of_effectiveFTC_stageSchedule
    h.toEffectiveFTC hendpoint sigma hsigma

/-- Build endpoint-schedule agreement for a derivative-bound FTC certificate
when its endpoint precision choices are a cofinal monotone stage schedule for
the canonical endpoint-difference raw real. -/
theorem endpointScheduleAgreement_of_derivativeBoundFTC_stageSchedule
    {F dF : RealFunRaw} {a b : Rat}
    (h : DerivativeBoundFTC F dF a b)
    (hendpoint : RealRaw.ValidCompute (endpointDifferenceCompute F a b))
    (sigma : RealRaw.StageSchedule)
    (hsigma :
      forall n, h.chooseEndpointPrecision (precisionAtStage n) = sigma.stage n) :
    EndpointScheduleAgreement F a b h.endpointRaw := by
  let endpoint : RealRaw := endpointDifferenceRaw F a b hendpoint
  have hendpointValid : endpoint.Valid := by
    simpa [endpoint, endpointDifferenceRaw, RealRaw.Valid] using hendpoint
  refine
    { endpoint_valid := hendpoint
      scheduled_valid := ?_
      equivalent := ?_ }
  · have hsched := RealRaw.schedule_valid endpoint hendpointValid sigma
    have hcompute :
        h.endpointCompute =
          fun n => endpointDifferenceCompute F a b (sigma.stage n) := by
      funext n
      simp [DerivativeBoundFTC.endpointCompute,
        DerivativeBoundFTC.endpointInterval, endpointDifferenceCompute, hsigma]
    simpa [DerivativeBoundFTC.endpointRaw, RealRaw.Valid, hcompute] using hsched
  · intro n
    have hall := RealRaw.allStagesOverlap_refl endpoint hendpointValid
      (sigma.stage n) n
    have hover := (RealRaw.compareAt_overlap_iff endpoint endpoint
      (sigma.stage n) n).1 hall
    apply (RealRaw.compareAt_overlap_iff
      h.endpointRaw
      (endpointDifferenceRaw F a b hendpoint) n n).2
    simpa [DerivativeBoundFTC.endpointRaw, DerivativeBoundFTC.endpointCompute,
      DerivativeBoundFTC.endpointInterval, endpoint, endpointDifferenceRaw,
      hsigma] using hover

/-- Candidate-derivative endpoint-schedule agreement, by conversion to the
derivative-bound FTC certificate. -/
theorem endpointScheduleAgreement_of_candidateDerivativeFTC_stageSchedule
    {F dF : RealFunRaw} {a b : Rat}
    (h : CandidateDerivativeFTC F dF a b)
    (hendpoint : RealRaw.ValidCompute (endpointDifferenceCompute F a b))
    (sigma : RealRaw.StageSchedule)
    (hsigma :
      forall n,
        h.toDerivativeBoundFTC.chooseEndpointPrecision (precisionAtStage n) =
          sigma.stage n) :
    EndpointScheduleAgreement F a b h.toDerivativeBoundFTC.endpointRaw :=
  endpointScheduleAgreement_of_derivativeBoundFTC_stageSchedule
    h.toDerivativeBoundFTC hendpoint sigma hsigma

/-- Curvature endpoint-schedule agreement, by conversion to the
derivative-bound FTC certificate. -/
theorem endpointScheduleAgreement_of_curvatureFTC_stageSchedule
    {F dF : RealFunRaw} {a b : Rat}
    (h : CurvatureFTCCertificate F dF a b)
    (hendpoint : RealRaw.ValidCompute (endpointDifferenceCompute F a b))
    (sigma : RealRaw.StageSchedule)
    (hsigma :
      forall n,
        h.toDerivativeBoundFTC.chooseEndpointPrecision (precisionAtStage n) =
          sigma.stage n) :
    EndpointScheduleAgreement F a b h.toDerivativeBoundFTC.endpointRaw :=
  endpointScheduleAgreement_of_derivativeBoundFTC_stageSchedule
    h.toDerivativeBoundFTC hendpoint sigma hsigma

/-- Convex endpoint-schedule agreement, by conversion to the derivative-bound
FTC certificate. -/
theorem endpointScheduleAgreement_of_convexFTC_stageSchedule
    {F dF : RealFunRaw} {a b : Rat}
    (h : ConvexFTCCertificate F dF a b)
    (hendpoint : RealRaw.ValidCompute (endpointDifferenceCompute F a b))
    (sigma : RealRaw.StageSchedule)
    (hsigma :
      forall n,
        h.toDerivativeBoundFTC.chooseEndpointPrecision (precisionAtStage n) =
          sigma.stage n) :
    EndpointScheduleAgreement F a b h.toDerivativeBoundFTC.endpointRaw :=
  endpointScheduleAgreement_of_derivativeBoundFTC_stageSchedule
    h.toDerivativeBoundFTC hendpoint sigma hsigma

/-- Concave endpoint-schedule agreement, by conversion to the derivative-bound
FTC certificate. -/
theorem endpointScheduleAgreement_of_concaveFTC_stageSchedule
    {F dF : RealFunRaw} {a b : Rat}
    (h : ConcaveFTCCertificate F dF a b)
    (hendpoint : RealRaw.ValidCompute (endpointDifferenceCompute F a b))
    (sigma : RealRaw.StageSchedule)
    (hsigma :
      forall n,
        h.toDerivativeBoundFTC.chooseEndpointPrecision (precisionAtStage n) =
          sigma.stage n) :
    EndpointScheduleAgreement F a b h.toDerivativeBoundFTC.endpointRaw :=
  endpointScheduleAgreement_of_derivativeBoundFTC_stageSchedule
    h.toDerivativeBoundFTC hendpoint sigma hsigma

def integralPlanOfEffectiveFTC
    {F dF : RealFunRaw} {a b : Rat}
    (h : EffectiveFTC F dF a b) : Nat -> Integral.Plan :=
  fun n =>
    let eps := requestedPrecision n
    { subdivisions := h.chooseN eps,
      evalPrecision := h.chooseEvalPrecision eps }

def integralPlanOfStaticDyadicEffectiveFTC
    {F dF : RealFunRaw} {a b : Rat}
    (h : StaticDyadicEffectiveFTC F dF a b) : Nat -> Integral.Plan :=
  fun n =>
    let eps := requestedPrecision n
    { subdivisions := Integral.staticDyadicSubdivisions (h.chooseStage eps),
      evalPrecision := h.chooseEvalPrecision eps }

theorem integralPlanOfStaticDyadicEffectiveFTC_eq_toEffectiveFTC
    {F dF : RealFunRaw} {a b : Rat}
    (h : StaticDyadicEffectiveFTC F dF a b) :
    integralPlanOfStaticDyadicEffectiveFTC h =
      integralPlanOfEffectiveFTC h.toEffectiveFTC := by
  funext n
  simp [integralPlanOfStaticDyadicEffectiveFTC, integralPlanOfEffectiveFTC,
    StaticDyadicEffectiveFTC.toEffectiveFTC]

theorem riemannComputeOfEffectiveFTC_eq_integralPlan
    {F dF : RealFunRaw} {a b : Rat}
    (h : EffectiveFTC F dF a b) (n : Nat) :
    riemannComputeOfEffectiveFTC h n =
      riemannLeftInterval dF a b
        ((integralPlanOfEffectiveFTC h n).subdivisions)
        ((integralPlanOfEffectiveFTC h n).evalPrecision) := by
  simp [riemannComputeOfEffectiveFTC, integralPlanOfEffectiveFTC]

theorem integral_compute_eq_riemannComputeOfEffectiveFTC
    {F dF : RealFunRaw} {a b : Rat}
    (h : EffectiveFTC F dF a b)
    (c : Integral.Construction dF a b)
    (hplan : c.plan = integralPlanOfEffectiveFTC h) :
    (Integral.integral dF a b c).compute =
      riemannComputeOfEffectiveFTC h := by
  funext n
  simp [Integral.integral, Integral.Certificate.realRaw,
    Integral.Raw.toRealRaw, Integral.Raw.compute, Integral.algorithm,
    riemannComputeOfEffectiveFTC, integralPlanOfEffectiveFTC, hplan]

theorem integral_valid_of_construction
    {f : RealFunRaw} {a b : Rat}
    (c : Integral.Construction f a b) :
    (Integral.integral f a b c).Valid := by
  simpa [RealRaw.Valid, Integral.integral, Integral.Certificate.realRaw,
    Integral.Raw.toRealRaw] using c.certificate.valid

/-- General effective FTC, in computable-real form.

An `EffectiveFTC` certificate already says that, for every rational precision,
some finite Riemann sum for `dF` is close to the endpoint difference
`F(b)-F(a)`.  This theorem packages that certificate as equivalence of two
raw real algorithms: the scheduled Riemann sums and the scheduled endpoint
differences overlap at every requested stage. -/
theorem effectiveFTC_equiv_endpoint
    {F dF : RealFunRaw} {a b : Rat}
    (h : EffectiveFTC F dF a b) :
    (riemannRawOfEffectiveFTC h).Equiv (endpointRawOfEffectiveFTC h) := by
  apply RealRaw.sameStageOverlap_equiv
  intro n
  have hgood := h.good (requestedPrecision n)
  exact (RealRaw.compareAt_overlap_iff
    (riemannRawOfEffectiveFTC h) (endpointRawOfEffectiveFTC h) n n).2 hgood.1

/-- FTC bridge for a chosen integral construction.

If the integral construction uses exactly the Riemann-sum plan supplied by an
`EffectiveFTC` certificate, then the constructed integral is equivalent to the
scheduled endpoint-difference raw algorithm from that certificate.  This is the
main reusable form for later equivalence proofs: the analytic work is isolated
in the `EffectiveFTC` certificate, while the integral side only has to expose
the same finite-stage schedule. -/
theorem effectiveFTC_integral_equiv_scheduledEndpoint
    {F dF : RealFunRaw} {a b : Rat}
    (h : EffectiveFTC F dF a b)
    (c : Integral.Construction dF a b)
    (hplan : c.plan = integralPlanOfEffectiveFTC h) :
    (Integral.integral dF a b c).Equiv (endpointRawOfEffectiveFTC h) := by
  apply RealRaw.sameStageOverlap_equiv
  intro n
  have hgood := h.good (requestedPrecision n)
  apply (RealRaw.compareAt_overlap_iff
    (Integral.integral dF a b c) (endpointRawOfEffectiveFTC h) n n).2
  rw [integral_compute_eq_riemannComputeOfEffectiveFTC h c hplan]
  exact hgood.1

/-- Static-dyadic effective FTC, in computable-real form. -/
theorem staticDyadicEffectiveFTC_equiv_endpoint
    {F dF : RealFunRaw} {a b : Rat}
    (h : StaticDyadicEffectiveFTC F dF a b) :
    (riemannRawOfEffectiveFTC h.toEffectiveFTC).Equiv
      (endpointRawOfEffectiveFTC h.toEffectiveFTC) :=
  effectiveFTC_equiv_endpoint h.toEffectiveFTC

/-- FTC bridge for a construction using the static dyadic schedule. -/
theorem staticDyadicEffectiveFTC_integral_equiv_scheduledEndpoint
    {F dF : RealFunRaw} {a b : Rat}
    (h : StaticDyadicEffectiveFTC F dF a b)
    (c : Integral.Construction dF a b)
    (hplan : c.plan = integralPlanOfStaticDyadicEffectiveFTC h) :
    (Integral.integral dF a b c).Equiv
      (endpointRawOfEffectiveFTC h.toEffectiveFTC) := by
  apply effectiveFTC_integral_equiv_scheduledEndpoint h.toEffectiveFTC c
  rw [← integralPlanOfStaticDyadicEffectiveFTC_eq_toEffectiveFTC h]
  exact hplan

/-- Transport the scheduled FTC bridge to the canonical endpoint-difference
algorithm when that endpoint schedule has separately been proved equivalent to
the canonical endpoint computation.

This theorem is intentionally split from `effectiveFTC_integral_equiv_scheduledEndpoint`:
cofinality or monotonicity of the endpoint precision schedule is representation
specific, so later files can prove it in the form most convenient for the
function `F`. -/
theorem effectiveFTC_definiteIntegralEqualsEndpoint
    {F dF : RealFunRaw} {a b : Rat}
    (h : EffectiveFTC F dF a b)
    (c : Integral.Construction dF a b)
    (hendpoint : RealRaw.ValidCompute (endpointDifferenceCompute F a b))
    (hplan : c.plan = integralPlanOfEffectiveFTC h)
    (hscheduledEndpoint : (endpointRawOfEffectiveFTC h).Valid)
    (hendpoint_equiv :
      (endpointRawOfEffectiveFTC h).Equiv
        (endpointDifferenceRaw F a b hendpoint)) :
    DefiniteIntegralEqualsEndpointDifference F dF a b c hendpoint := by
  exact RealRaw.equiv_trans
    (integral_valid_of_construction c)
    hscheduledEndpoint
    hendpoint
    (effectiveFTC_integral_equiv_scheduledEndpoint h c hplan)
    hendpoint_equiv

/-- Definite-integral FTC bridge using the packaged endpoint-schedule
agreement. -/
theorem effectiveFTC_definiteIntegralEqualsEndpoint_of_endpointAgreement
    {F dF : RealFunRaw} {a b : Rat}
    (h : EffectiveFTC F dF a b)
    (c : Integral.Construction dF a b)
    (hplan : c.plan = integralPlanOfEffectiveFTC h)
    (endpoint :
      EndpointScheduleAgreement F a b (endpointRawOfEffectiveFTC h)) :
    DefiniteIntegralEqualsEndpointDifference
      F dF a b c endpoint.endpoint_valid :=
  effectiveFTC_definiteIntegralEqualsEndpoint
    h c endpoint.endpoint_valid hplan
    endpoint.scheduled_valid endpoint.equivalent

/-- Static-dyadic specialization of the definite-integral FTC bridge. -/
theorem staticDyadicEffectiveFTC_definiteIntegralEqualsEndpoint
    {F dF : RealFunRaw} {a b : Rat}
    (h : StaticDyadicEffectiveFTC F dF a b)
    (c : Integral.Construction dF a b)
    (hendpoint : RealRaw.ValidCompute (endpointDifferenceCompute F a b))
    (hplan : c.plan = integralPlanOfStaticDyadicEffectiveFTC h)
    (hscheduledEndpoint : (endpointRawOfEffectiveFTC h.toEffectiveFTC).Valid)
    (hendpoint_equiv :
      (endpointRawOfEffectiveFTC h.toEffectiveFTC).Equiv
        (endpointDifferenceRaw F a b hendpoint)) :
    DefiniteIntegralEqualsEndpointDifference F dF a b c hendpoint := by
  exact RealRaw.equiv_trans
    (integral_valid_of_construction c)
    hscheduledEndpoint
    hendpoint
    (staticDyadicEffectiveFTC_integral_equiv_scheduledEndpoint h c hplan)
    hendpoint_equiv

/-- Static-dyadic specialization using the packaged endpoint-schedule
agreement. -/
theorem staticDyadicEffectiveFTC_definiteIntegralEqualsEndpoint_of_endpointAgreement
    {F dF : RealFunRaw} {a b : Rat}
    (h : StaticDyadicEffectiveFTC F dF a b)
    (c : Integral.Construction dF a b)
    (hplan : c.plan = integralPlanOfStaticDyadicEffectiveFTC h)
    (endpoint :
      EndpointScheduleAgreement F a b
        (endpointRawOfEffectiveFTC h.toEffectiveFTC)) :
    DefiniteIntegralEqualsEndpointDifference
      F dF a b c endpoint.endpoint_valid :=
  staticDyadicEffectiveFTC_definiteIntegralEqualsEndpoint
    h c endpoint.endpoint_valid hplan
    endpoint.scheduled_valid endpoint.equivalent

end FTC

end ComputableAnalysis
