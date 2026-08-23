import ComputableAnalysis.SinPiIntegral

namespace ComputableAnalysis

namespace SinPiIntegral

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

/-! A finite candidate list is the executable interface to the geometric
certificate.  The soundness theorem for the Boolean search turns a proof that
each list has a hit into the certificate family above.  Thus the remaining
analytic obligation can be stated entirely as a family of finite search
success theorems. -/

noncomputable def DyadicTangentWitnessFamily.of_canonical_search_family
    (B : IntegralIdentities.ArctanInverseBisection)
    (ht0 : (B.tangentAt 0
      RationalCircle.GeometricTrig.firstQuadrantBranch_zero).Equiv
      RealRaw.zero)
    (candidates : forall (precision depth k : Nat) (hk : k < 2 ^ depth),
      List Rat)
    (hsearch : forall (precision depth k : Nat) (hk : k < 2 ^ depth),
      ∃ u, canonicalDyadicCertificateSearchAt B precision depth k hk
        (candidates precision depth k hk) = some u) :
    DyadicTangentWitnessFamily B := by
  apply DyadicTangentWitnessFamily.of_halfAngle_certificate_family B ht0
  intro precision depth k hk hpos
  let hit := hsearch precision depth k hk
  exact canonicalDyadicCertificateSearchAt_sound B
    (Classical.choose_spec hit)

/-! Constructors that reduce the two geometric branch obligations to one
explicit rational interval identity.  The parent box is taken directly from
the nested-radical table, so its containment and self-overlap are automatic;
the caller only has to prove that the public circle box is the corresponding
clipped half-angle square-root box. -/

def DyadicHalfAngleChildCertificate.of_table_parent
    (B : IntegralIdentities.ArctanInverseBisection)
    (precision n j : Nat) (hbound : 2 * j + 1 <= 2 ^ n)
    (hpublic :
      sqrtOnUnitEvalIntervalClipped
          (dyadicHalfAngleSinInput
            (dyadicNestedRadicalTableAt
              (dyadicNestedRadicalParentPrecision precision) n (2 * j + 1)).2)
          precision =
        rationalCircleSinInterval
          (dyadicTangentBoxAt B precision (n + 1) (2 * j + 1) (by
            have hpow : 2 ^ (n + 1) = 2 * 2 ^ n := by
              rw [Nat.pow_succ]
              omega
            rw [hpow]
            omega))) :
    DyadicHalfAngleChildCertificate B precision n j hbound where
  parentRawCos :=
    (dyadicNestedRadicalTableAt
      (dyadicNestedRadicalParentPrecision precision) n (2 * j + 1)).2
  parentRawCos_subinterval := by
    exact (dyadicNestedRadicalTableAt_bounds
      (dyadicNestedRadicalParentPrecision precision) n (2 * j + 1)
      (by omega)).2
  parent_overlap := by
    have hbounds := dyadicNestedRadicalTableAt_bounds
      (dyadicNestedRadicalParentPrecision precision) n (2 * j + 1)
      (by omega)
    unfold QInterval.Overlaps
    exact ⟨hbounds.2.2.1, hbounds.2.2.1⟩
  childRawSin := sqrtOnUnitEvalIntervalClipped
    (dyadicHalfAngleSinInput
      (dyadicNestedRadicalTableAt
        (dyadicNestedRadicalParentPrecision precision) n (2 * j + 1)).2)
    precision
  childRawSin_eq := rfl
  public_child_eq := hpublic

def DyadicReflectedHalfAngleCertificate.of_table_parent
    (B : IntegralIdentities.ArctanInverseBisection)
    (precision n k : Nat) (hupper : 2 ^ n < k) (hk : k < 2 ^ (n + 1))
    (hpublic :
      sqrtOnUnitEvalIntervalClipped
          (dyadicHalfAngleSinInput
            (dyadicNestedRadicalNeg
              (dyadicNestedRadicalTableAt
                (dyadicNestedRadicalParentPrecision precision) n
                (2 * 2 ^ n - k)).2))
          precision =
        rationalCircleSinInterval
          (dyadicTangentBoxAt B precision (n + 1) k (by
            have hpow : 2 ^ (n + 1) = 2 * 2 ^ n := by
              rw [Nat.pow_succ]
              omega
            rw [hpow]
            omega))) :
    DyadicReflectedHalfAngleCertificate B precision n k hupper hk where
  parentRawCos := dyadicNestedRadicalNeg
    (dyadicNestedRadicalTableAt
      (dyadicNestedRadicalParentPrecision precision) n (2 * 2 ^ n - k)).2
  parentRawCos_subinterval := by
    exact dyadicNestedRadicalNeg_unit_subinterval _
      (dyadicNestedRadicalTableAt_bounds
        (dyadicNestedRadicalParentPrecision precision) n
        (2 * 2 ^ n - k) (by omega)).2
  parentRawCos_eq := rfl
  parent_overlap := by
    have hbounds := dyadicNestedRadicalNeg_unit_subinterval _
      (dyadicNestedRadicalTableAt_bounds
        (dyadicNestedRadicalParentPrecision precision) n
        (2 * 2 ^ n - k) (by omega)).2
    unfold QInterval.Overlaps
    exact ⟨hbounds.2.1, hbounds.2.1⟩
  childRawSin := sqrtOnUnitEvalIntervalClipped
    (dyadicHalfAngleSinInput
      (dyadicNestedRadicalNeg
        (dyadicNestedRadicalTableAt
          (dyadicNestedRadicalParentPrecision precision) n
          (2 * 2 ^ n - k)).2))
    precision
  childRawSin_eq := rfl
  public_child_eq := hpublic

noncomputable def DyadicTangentWitnessFamily.of_overlap_family_core
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

/-! The direct-overlap variant is weaker than the exact branch certificates.
It is useful when interval arithmetic proves containment/overlap without
proving literal equality of the two computed boxes. -/

noncomputable def DyadicTangentWitnessFamily.of_branch_overlap_families
    (B : IntegralIdentities.ArctanInverseBisection)
    (ht0 : (B.tangentAt 0
      RationalCircle.GeometricTrig.firstQuadrantBranch_zero).Equiv
      RealRaw.zero)
    (even_overlap : forall (precision n j : Nat) (hj : j < 2 ^ n),
      QInterval.Overlaps
        (rationalCircleSinInterval
          (dyadicTangentBoxAt B precision (n + 1) (2 * j)
            (by
              have hpow : 2 ^ (n + 1) = 2 * 2 ^ n := by
                rw [Nat.pow_succ]
                omega
              rw [hpow]
              omega)))
        ((dyadicNestedRadicalTableAt precision (n + 1) (2 * j)).1))
    (lower_overlap : forall (precision n j : Nat)
      (hbound : 2 * j + 1 <= 2 ^ n),
      QInterval.Overlaps
        (rationalCircleSinInterval
          (dyadicTangentBoxAt B precision (n + 1) (2 * j + 1)
            (by
              have hpow : 2 ^ (n + 1) = 2 * 2 ^ n := by
                rw [Nat.pow_succ]
                omega
              rw [hpow]
              omega)))
        ((dyadicNestedRadicalTableAt precision (n + 1) (2 * j + 1)).1))
    (upper_overlap : forall (precision n k : Nat)
      (hupper : 2 ^ n < k) (hk : k < 2 ^ (n + 1)),
      QInterval.Overlaps
        (rationalCircleSinInterval
          (dyadicTangentBoxAt B precision (n + 1) k (by
            have hpow : 2 ^ (n + 1) = 2 * 2 ^ n := by
              rw [Nat.pow_succ]
              omega
            rw [hpow]
            omega)))
        ((dyadicNestedRadicalTableAt precision (n + 1) k).1)) :
    DyadicTangentWitnessFamily B := by
  apply DyadicTangentWitnessFamily.of_overlap_family_core B ht0
  intro depth k hk hpos precision
  cases depth with
  | zero => omega
  | succ n =>
      by_cases hzero : k = 0
      · subst k
        simpa [sinPiRawOfArctan, dyadicTangentBoxAt] using
          (dyadicNestedRadical_zero_sample_overlap_of_endpoint B ht0
            precision (n + 1) (by omega))
      · by_cases heven : k % 2 = 0
        · obtain ⟨j, rfl⟩ : ∃ j, k = 2 * j := by
            exact ⟨k / 2, by omega⟩
          have hj : j < 2 ^ n := by
            rw [Nat.pow_succ] at hk
            omega
          simpa [sinPiRawOfArctan, dyadicTangentBoxAt] using
            (even_overlap precision n j hj)
        · have hodd : k % 2 = 1 := by omega
          by_cases hlower : k <= 2 ^ n
          · obtain ⟨j, rfl⟩ : ∃ j, k = 2 * j + 1 := by
              exact ⟨k / 2, by omega⟩
            have hbound : 2 * j + 1 <= 2 ^ n := by omega
            simpa [sinPiRawOfArctan, dyadicTangentBoxAt] using
              (lower_overlap precision n j hbound)
          · have hupper : 2 ^ n < k := by omega
            simpa [sinPiRawOfArctan, dyadicTangentBoxAt] using
              (upper_overlap precision n k hupper hk)

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
