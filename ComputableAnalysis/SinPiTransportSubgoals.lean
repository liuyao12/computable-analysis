import ComputableAnalysis.SinPiIntegral

namespace ComputableAnalysis

namespace SinPiIntegral

/-! The first finite transport checkpoint for the nested-radical sine route.
At stage zero the public left sum has one degenerate cell at the left endpoint;
the chart interval still contains the same rational anchor `0`. -/

theorem dyadicNestedRadicalStieltjes_base_witness :
    QInterval.Overlaps
      (dyadicNestedRadicalLeftSum 0)
      (sinPiStieltjesIntegral.compute 0) := by
  unfold QInterval.Overlaps
  constructor
  · rw [dyadicNestedRadicalLeftSum_zero]
    change 0 <= (sinPiStieltjesIntegral.compute 0).hi
    native_decide
  · rw [dyadicNestedRadicalLeftSum_zero]
    change (sinPiStieltjesIntegral.compute 0).lo <= 0
    native_decide

theorem dyadicNestedRadicalStieltjes_stage_one_overlap :
    QInterval.Overlaps
      (dyadicNestedRadicalLeftSum 1)
      (sinPiStieltjesIntegral.compute 1) := by
  unfold QInterval.Overlaps
  native_decide

theorem dyadicNestedRadicalStieltjes_stage_two_overlap :
    QInterval.Overlaps
      (dyadicNestedRadicalLeftSum 2)
      (sinPiStieltjesIntegral.compute 2) := by
  unfold QInterval.Overlaps
  native_decide

theorem dyadicNestedRadicalStieltjes_stage_three_overlap :
    QInterval.Overlaps
      (dyadicNestedRadicalLeftSum 3)
      (sinPiStieltjesIntegral.compute 3) := by
  unfold QInterval.Overlaps
  native_decide

/-! Packaging lemma for the final search-family assembly.  The search itself
is executable; this proof-level constructor only packages the already-proved
existence of a successful finite search at every requested precision. -/

noncomputable def DyadicTangentWitnessFamily.of_search_family
    (B : IntegralIdentities.ArctanInverseBisection)
    (hsearch : forall (depth k : Nat)
      (hk : k < 2 ^ depth),
      forall precision, ∃ m u, rationalTangentWitnessBoxSearch
        (dyadicTangentBoxAt B precision depth k hk)
        (dyadicNestedRadicalTableAt precision depth k).1 m = some u) :
    DyadicTangentWitnessFamily B := by
  classical
  refine { schedule := ?_ }
  intro depth k hk
  refine {
    witness := fun precision =>
      Classical.choose (Classical.choose_spec (hsearch depth k hk precision))
    searchPrecision := fun precision =>
      Classical.choose (hsearch depth k hk precision)
    search := fun precision =>
      Classical.choose_spec (Classical.choose_spec
        (hsearch depth k hk precision)) }

/-! The only exceptional dyadic cell is the zero endpoint.  All positive
cells use the canonical half-angle certificate; the endpoint uses the exact
zero tangent law.  This is the concrete assembly theorem that turns the
geometric certificate family into the executable witness family consumed by
the public nested-radical integral theorem. -/

noncomputable def DyadicTangentWitnessFamily.of_halfAngle_certificate_family
    (B : IntegralIdentities.ArctanInverseBisection)
    (ht0 : (B.tangentAt 0
      RationalCircle.GeometricTrig.firstQuadrantBranch_zero).Equiv
      RealRaw.zero)
    (hcertificate : forall (precision depth k : Nat) (hk : k < 2 ^ depth),
      0 < k -> CanonicalDyadicHalfAngleCertificateAt B precision depth k hk) :
    DyadicTangentWitnessFamily B := by
  apply DyadicTangentWitnessFamily.of_search_family B
  intro depth k hk precision
  by_cases hzero : k = 0
  · subst k
    obtain ⟨u, hu⟩ := canonical_dyadic_zero_search_at B ht0 precision depth hk
    exact ⟨0, u, by simpa [dyadicNestedRadicalTableAt_zero_sin] using hu⟩
  · have hpos : 0 < k := by omega
    exact canonical_dyadic_search_of_halfAngle_certificate_at B hpos
      (hcertificate precision depth k hk hpos)

noncomputable def DyadicTangentWitnessFamily.of_overlap_family
    (B : IntegralIdentities.ArctanInverseBisection)
    (ht0 : (B.tangentAt 0
      RationalCircle.GeometricTrig.firstQuadrantBranch_zero).Equiv
      RealRaw.zero)
    (hover : forall (depth k : Nat) (hk : k < 2 ^ depth), 0 < k ->
      forall precision, QInterval.Overlaps
        (rationalCircleSinInterval
          (dyadicTangentBoxAt B precision depth k hk))
        ((dyadicNestedRadicalTableAt precision depth k).1)) :
    DyadicTangentWitnessFamily B := by
  apply DyadicTangentWitnessFamily.of_search_family B
  intro depth k hk precision
  by_cases hzero : k = 0
  · subst k
    obtain ⟨u, hu⟩ := canonical_dyadic_zero_search_at B ht0 precision depth hk
    exact ⟨0, u, by simpa [dyadicNestedRadicalTableAt_zero_sin] using hu⟩
  · have hpos : 0 < k := by omega
    exact canonical_dyadic_search_of_overlap_at B hk hpos
      (hover depth k hk hpos precision)

/-! Final assembly adapter for the three finite refinement branches.  Once
the even, lower-odd, and reflected-upper-odd certificates are supplied, the
existing overlap assembly gives precisely the overlap family consumed above.
This leaves no hidden classical continuity premise in the transport step. -/

noncomputable def DyadicTangentWitnessFamily.of_branch_certificate_families
    (B : IntegralIdentities.ArctanInverseBisection)
    (ht0 : (B.tangentAt 0
      RationalCircle.GeometricTrig.firstQuadrantBranch_zero).Equiv
      RealRaw.zero)
    (even_certificate : forall (precision n j : Nat) (hj : j < 2 ^ n),
      DyadicEvenStepCertificate B precision n j hj)
    (lower_certificate : forall (precision n j : Nat)
      (hbound : 2 * j + 1 <= 2 ^ n),
      DyadicHalfAngleChildCertificate B precision n j hbound)
    (upper_certificate : forall (precision n k : Nat)
      (hupper : 2 ^ n < k) (hk : k < 2 ^ (n + 1)),
      DyadicReflectedHalfAngleCertificate B precision n k hupper hk) :
    DyadicTangentWitnessFamily B := by
  apply DyadicTangentWitnessFamily.of_overlap_family B ht0
  intro depth k hk hpos precision
  have hover := dyadicNestedRadical_sample_overlap_of_branch_certificates_of_endpoint
    B ht0 even_certificate lower_certificate upper_certificate
    precision depth k hk
  simpa [sinPiRawOfArctan, dyadicTangentBoxAt] using hover

end SinPiIntegral

end ComputableAnalysis
