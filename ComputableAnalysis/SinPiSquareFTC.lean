import ComputableAnalysis.SinPiIntegral
import ComputableAnalysis.FiniteSinePrefixFTC

/-!
# The squared-sine test function

This file records the first product-valued non-polynomial integrand.  The
pointwise square is built from the same arctangent/nested-radical sine
representation as the half-interval sine integral; no real-number product or
Lebesgue integral is introduced.
-/

namespace ComputableAnalysis

namespace SinPiIntegral

/-! The finite polynomial rung is already a complete effective-FTC theorem.
Expose it here as the algebraic shadow of the nested-radical target, so that
the later tail-transport proof has a fixed, checked predecessor. -/

def finiteSineSquarePrefixRaw : RealFunRaw :=
  FiniteSinePrefix.sineTaylorPrefixThreeSquareRaw

def finiteSineSquarePrefixPrimitiveRaw : RealFunRaw :=
  FiniteSinePrefix.sineTaylorPrefixThreeSquarePrimitiveRaw

theorem finiteSineSquarePrefix_effectiveFTC_equiv_endpoint :
    FiniteSinePrefix.sineTaylorPrefixThreeSquareEffectiveFTCData.toDerivativeBoundFTC.boundedIntegralRaw.Equiv
      FiniteSinePrefix.sineTaylorPrefixThreeSquareEffectiveFTCData.toDerivativeBoundFTC.endpointRaw := by
  exact FiniteSinePrefix.sineTaylorPrefixThreeSquareEffectiveFTC_equiv_endpoint

theorem finiteSineSquarePrefix_effectiveFTC_equiv_value :
    FiniteSinePrefix.sineTaylorPrefixThreeSquareEffectiveFTCData.toDerivativeBoundFTC.boundedIntegralRaw.Equiv
      (RealRaw.ofRat (6389 / 161280)) := by
  exact FiniteSinePrefix.sineTaylorPrefixThreeSquareEffectiveFTC_equiv_value

def sinPiOnHalfRaw (S : ArctanSinPiConstruction) : RealFunRaw where
  domain := fun x => 0 <= x /\ x <= (1 : Rat) / 2
  compute := fun x n =>
    if hx : 0 <= x /\ x <= (1 : Rat) / 2 then
      (sinPiRawOfArctan S.inverse x hx).compute n
    else
      { lo := 0, hi := 0 }

def sinPiSquareOnHalf (S : ArctanSinPiConstruction) : RealFunRaw :=
  RealFunRaw.mul (sinPiOnHalfRaw S) (sinPiOnHalfRaw S)

/- The finite rational-circle identity used by the future primitive proof.
   Keeping this as an algebraic theorem makes the intended `sin²` route
   explicit before any interval-level cosine transport is added. -/
theorem rationalCircleSin_sq_eq_one_sub_cos_sq (u : Rat) :
    rationalCircleSin u * rationalCircleSin u =
      1 - rationalCircleCos u * rationalCircleCos u := by
  have h := rationalCircleSin_sq_add_cos_sq u
  grind

/-! A box-level form of the circle identity.  It is intentionally stated for
rational witness values: the later nested-radical transport supplies such
witnesses through its tangent-box overlap certificates. -/

def rationalSquareInterval (I : QInterval) : QInterval :=
  { lo := I.lo * I.lo, hi := I.hi * I.hi }

def rationalOneMinusSquareInterval (I : QInterval) : QInterval :=
  { lo := 1 - I.hi * I.hi, hi := 1 - I.lo * I.lo }

theorem rationalSquareInterval_overlap_oneMinusSquareInterval_of_circle
    {S C : QInterval} {s c : Rat}
    (hS : subintervalOf S 0 1) (hC : subintervalOf C 0 1)
    (hs : S.lo <= s ∧ s <= S.hi) (hc : C.lo <= c ∧ c <= C.hi)
    (hcircle : s * s + c * c = 1) :
    QInterval.Overlaps (rationalSquareInterval S)
      (rationalOneMinusSquareInterval C) := by
  have hSlo : 0 <= S.lo := hS.1
  have hChi : C.hi <= 1 := hC.2.2
  have hs0 : 0 <= s := Rat.le_trans hSlo hs.1
  have hc0 : 0 <= c := Rat.le_trans hC.1 hc.1
  have Shi0 : 0 <= S.hi := Rat.le_trans hSlo hS.2.1
  have Clo0 : 0 <= C.lo := hC.1
  have Chi0 : 0 <= C.hi := Rat.le_trans Clo0 hC.2.1
  have hSsq_lo : S.lo * S.lo <= s * s := by
    have h := Rat.mul_le_mul_of_nonneg_right hs.1
      (Rat.add_nonneg hs0 hSlo)
    grind [Rat.mul_add, Rat.add_mul]
  have hSsq_hi : s * s <= S.hi * S.hi := by
    have h := Rat.mul_le_mul_of_nonneg_right hs.2
      (Rat.add_nonneg hs0 Shi0)
    grind [Rat.mul_add, Rat.add_mul]
  have hCsq_lo : C.lo * C.lo <= c * c := by
    have h := Rat.mul_le_mul_of_nonneg_right hc.1
      (Rat.add_nonneg hc0 Clo0)
    grind [Rat.mul_add, Rat.add_mul]
  have hCsq_hi : c * c <= C.hi * C.hi := by
    have h := Rat.mul_le_mul_of_nonneg_right hc.2
      (Rat.add_nonneg hc0 Chi0)
    grind [Rat.mul_add, Rat.add_mul]
  have hsquare_mem :
      S.lo * S.lo <= s * s ∧ s * s <= S.hi * S.hi :=
    ⟨hSsq_lo, hSsq_hi⟩
  have hcomplement_mem :
      1 - C.hi * C.hi <= 1 - c * c ∧
        1 - c * c <= 1 - C.lo * C.lo := by
    constructor <;> grind
  unfold rationalSquareInterval rationalOneMinusSquareInterval
    QInterval.Overlaps
  change S.lo * S.lo <= 1 - C.lo * C.lo ∧
    1 - C.hi * C.hi <= S.hi * S.hi
  constructor
  · calc
      S.lo * S.lo <= s * s := hsquare_mem.1
      _ = 1 - c * c := by grind
      _ <= 1 - C.lo * C.lo := hcomplement_mem.2
  · calc
      1 - C.hi * C.hi <= 1 - c * c := hcomplement_mem.1
      _ = s * s := by grind
      _ <= S.hi * S.hi := hsquare_mem.2

/-! A square-aware variant of the finite tangent search.  The existing search
checks only the sine box; this predicate checks both circle coordinates, so a
successful result can be consumed by the square/complement transport above. -/

def rationalTangentSquareWitnessAdmissibleBool
    (U S C : QInterval) (u : Rat) : Bool :=
  (U.lo <= u) && (u <= U.hi) &&
    (S.lo <= rationalCircleSin u) &&
    (rationalCircleSin u <= S.hi) &&
    (C.lo <= rationalCircleCos u) &&
    (rationalCircleCos u <= C.hi)

def rationalTangentSquareWitnessSearchList
    (U S C : QInterval) : List Rat -> Option Rat
  | [] => none
  | u :: us =>
      if rationalTangentSquareWitnessAdmissibleBool U S C u then some u
      else rationalTangentSquareWitnessSearchList U S C us

theorem rationalTangentSquareWitnessSearchList_sound
    {U S C : QInterval} {us : List Rat} {u : Rat}
    (h : rationalTangentSquareWitnessSearchList U S C us = some u) :
    rationalTangentSquareWitnessAdmissibleBool U S C u = true := by
  induction us with
  | nil => simp [rationalTangentSquareWitnessSearchList] at h
  | cons v vs ih =>
      simp only [rationalTangentSquareWitnessSearchList] at h
      split at h
      · cases h
        assumption
      · exact ih h

theorem rationalTangentSquareWitnessSearchList_complete
    {U S C : QInterval} {us : List Rat} {u : Rat}
    (hmem : u ∈ us)
    (hadm : rationalTangentSquareWitnessAdmissibleBool U S C u = true) :
    ∃ v, rationalTangentSquareWitnessSearchList U S C us = some v := by
  induction us with
  | nil => simp at hmem
  | cons q qs ih =>
      simp only [List.mem_cons] at hmem
      simp only [rationalTangentSquareWitnessSearchList]
      split
      · exact ⟨q, rfl⟩
      · rcases hmem with rfl | hmem
        · contradiction
        · exact ih hmem

def rationalTangentSquareWitnessSearch
    (U S C : QInterval) (m : Nat) : Option Rat :=
  rationalTangentSquareWitnessSearchList U S C
    (rationalTangentWitnessBoxGrid U m)

theorem rationalTangentSquareWitnessSearch_complete_of_grid_candidate
    {U S C : QInterval} (m k : Nat) (hk : k <= 2 ^ m)
    (hadm : rationalTangentSquareWitnessAdmissibleBool U S C
      (U.lo + U.width * ((k : Rat) / ((2 ^ m : Nat) : Rat))) = true) :
    ∃ v, rationalTangentSquareWitnessSearch U S C m = some v := by
  apply rationalTangentSquareWitnessSearchList_complete
    (u := U.lo + U.width * ((k : Rat) / ((2 ^ m : Nat) : Rat)))
  · unfold rationalTangentWitnessBoxGrid
    let N := 2 ^ m
    have hk' : k < N + 1 := by dsimp [N]; omega
    apply List.mem_map.mpr
    exact ⟨k, by simpa using hk', rfl⟩
  · exact hadm

theorem rationalTangentSquareWitnessSearch_sound
    {U S C : QInterval} {m : Nat} {u : Rat}
    (h : rationalTangentSquareWitnessSearch U S C m = some u) :
    U.lo <= u /\ u <= U.hi /\
      S.lo <= rationalCircleSin u /\ rationalCircleSin u <= S.hi /\
      C.lo <= rationalCircleCos u /\ rationalCircleCos u <= C.hi := by
  have hb := rationalTangentSquareWitnessSearchList_sound h
  simp only [rationalTangentSquareWitnessAdmissibleBool,
    Bool.and_eq_true] at hb
  refine ⟨of_decide_eq_true hb.1.1.1.1.1,
    of_decide_eq_true hb.1.1.1.1.2,
    of_decide_eq_true hb.1.1.1.2,
    of_decide_eq_true hb.1.1.2,
    of_decide_eq_true hb.1.2,
    of_decide_eq_true hb.2⟩

theorem CanonicalDyadicHalfAngleCertificateAt.to_square_complement_overlap
    {B : IntegralIdentities.ArctanInverseBisection}
    {precision depth k : Nat} {hk : k < 2 ^ depth}
    (h : CanonicalDyadicHalfAngleCertificateAt B precision depth k hk) :
    QInterval.Overlaps
      (rationalSquareInterval
        (dyadicNestedRadicalTableAt precision depth k).1)
      (rationalOneMinusSquareInterval h.cosineBox) := by
  exact rationalSquareInterval_overlap_oneMinusSquareInterval_of_circle
    (dyadicNestedRadicalTableAt_bounds precision depth k
      (Nat.le_of_lt hk)).1
    h.cosineBox_subinterval h.sine_contains h.cosine_contains
    h.circle_identity

theorem canonical_dyadic_certificate_at_of_rational_witness_square_overlap
    (B : IntegralIdentities.ArctanInverseBisection)
    {precision depth k : Nat} (hk : k < 2 ^ depth)
    (u : Rat) (hu0 : 0 <= u) (hu1 : u <= 1)
    (hsine : (dyadicNestedRadicalTableAt precision depth k).1.lo <=
        rationalCircleSin u /\
      rationalCircleSin u <=
        (dyadicNestedRadicalTableAt precision depth k).1.hi)
    (houter : (dyadicTangentBoxAt B precision depth k hk).ContainsInterval
      (rationalHalfAngleTangentInterval
        ((dyadicNestedRadicalTableAt precision depth k).1)
        { lo := rationalCircleCos u, hi := rationalCircleCos u })) :
    QInterval.Overlaps
      (rationalSquareInterval
        (dyadicNestedRadicalTableAt precision depth k).1)
      (rationalOneMinusSquareInterval
        ({ lo := rationalCircleCos u, hi := rationalCircleCos u } : QInterval)) := by
  let h := canonical_dyadic_certificate_at_of_rational_witness
    B hk u hu0 hu1 hsine houter
  exact h.to_square_complement_overlap

/-! The same transport target, named at a dyadic nested-radical sample.  The
remaining witness-search proof only has to supply the two interval-membership
facts and the rational circle equation. -/

def dyadicNestedRadicalStageCosAt (n k : Nat) : QInterval :=
  (dyadicNestedRadicalStageTable n k).2

theorem dyadicNestedRadicalStage_square_complement_overlap
    {n k : Nat} (_hk : k <= 2 ^ n) (s c : Rat)
    (hS : subintervalOf (dyadicNestedRadicalStageSinAt n k) 0 1)
    (hC : subintervalOf (dyadicNestedRadicalStageCosAt n k) 0 1)
    (hs : (dyadicNestedRadicalStageSinAt n k).lo <= s ∧
      s <= (dyadicNestedRadicalStageSinAt n k).hi)
    (hc : (dyadicNestedRadicalStageCosAt n k).lo <= c ∧
      c <= (dyadicNestedRadicalStageCosAt n k).hi)
    (hcircle : s * s + c * c = 1) :
    QInterval.Overlaps
      (rationalSquareInterval (dyadicNestedRadicalStageSinAt n k))
      (rationalOneMinusSquareInterval
        (dyadicNestedRadicalStageCosAt n k)) := by
  exact rationalSquareInterval_overlap_oneMinusSquareInterval_of_circle
    hS hC hs hc hcircle

theorem sinPiSquareOnHalf_valid (S : ArctanSinPiConstruction) :
    (sinPiSquareOnHalf S).Valid := by
  have hvalid : (sinPiOnHalfRaw S).Valid := by
    intro x hx
    change RealRaw.ValidCompute
      (fun n => if h : 0 <= x /\ x <= (1 : Rat) / 2 then
        (sinPiRawOfArctan S.inverse x h).compute n else { lo := 0, hi := 0 })
    split
    · exact S.sin_valid x hx
    · rename_i hfalse
      exact False.elim (hfalse hx)
  apply RealFunRaw.mul_valid_of_nonneg_bounded
    hvalid hvalid
  · intro x hx
    refine ⟨1, by native_decide, ?_⟩
    intro n
    change 0 <= (if h : 0 <= x /\ x <= (1 : Rat) / 2 then
      (sinPiRawOfArctan S.inverse x h).compute n else { lo := 0, hi := 0 }).lo /\
      (if h : 0 <= x /\ x <= (1 : Rat) / 2 then
        (sinPiRawOfArctan S.inverse x h).compute n else { lo := 0, hi := 0 }).hi <= 1
    split
    · exact S.sinPiRawOfArctan_bounds hx n
    · rename_i hfalse
      exact False.elim (hfalse hx)
  · intro x hx
    refine ⟨1, by native_decide, ?_⟩
    intro n
    change 0 <= (if h : 0 <= x /\ x <= (1 : Rat) / 2 then
      (sinPiRawOfArctan S.inverse x h).compute n else { lo := 0, hi := 0 }).lo /\
      (if h : 0 <= x /\ x <= (1 : Rat) / 2 then
        (sinPiRawOfArctan S.inverse x h).compute n else { lo := 0, hi := 0 }).hi <= 1
    split
    · exact S.sinPiRawOfArctan_bounds hx n
    · rename_i hfalse
      exact False.elim (hfalse hx)

/-!
## The effective-FTC acceptance interface

The structure below is deliberately the concrete subgoal for the squared-sine
application.  It does not postulate an analytic primitive: an inhabitant must
provide a computable primitive and the finite local endpoint controls required
by `EffectiveDerivativeBoundFTC`.  Once those data exist, the generic closure
theorem supplies the FTC equivalence.
-/

structure SinPiSquareEffectiveFTCData
    (S : ArctanSinPiConstruction) where
  primitive : RealFunRaw
  certificate :
    EffectiveDerivativeBoundFTC primitive (sinPiSquareOnHalf S) 0 ((1 : Rat) / 2)
  integral_valid :
    certificate.toDerivativeBoundFTC.boundedIntegralRaw.Valid
  endpoint_valid :
    certificate.toDerivativeBoundFTC.endpointRaw.Valid

def SinPiSquareEffectiveFTCData.integralRaw
    {S : ArctanSinPiConstruction}
    (D : SinPiSquareEffectiveFTCData S) : RealRaw :=
  D.certificate.toDerivativeBoundFTC.boundedIntegralRaw

def SinPiSquareEffectiveFTCData.endpointRaw
    {S : ArctanSinPiConstruction}
    (D : SinPiSquareEffectiveFTCData S) : RealRaw :=
  D.certificate.toDerivativeBoundFTC.endpointRaw

theorem SinPiSquareEffectiveFTCData.integral_equiv_endpoint
    {S : ArctanSinPiConstruction}
    (D : SinPiSquareEffectiveFTCData S) :
    D.integralRaw.Equiv D.endpointRaw := by
  exact effectiveDerivativeBoundFTC D.certificate

theorem SinPiSquareEffectiveFTCData.endpoint_equiv_of_value
    {S : ArctanSinPiConstruction}
    (D : SinPiSquareEffectiveFTCData S)
    (hvalue : D.endpointRaw.Equiv (RealRaw.ofRat (1 / 4))) :
    D.integralRaw.Equiv (RealRaw.ofRat (1 / 4)) := by
  exact RealRaw.equiv_trans
    D.integral_valid D.endpoint_valid (RealRaw.ofRat_valid _)
    D.integral_equiv_endpoint hvalue

end SinPiIntegral

end ComputableAnalysis
