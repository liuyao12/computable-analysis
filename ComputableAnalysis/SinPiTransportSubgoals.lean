import ComputableAnalysis.SinPiIntegral

namespace ComputableAnalysis

namespace SinPiIntegral

/-! The even branch can be generated from the certificate at its parent
precision.  The dyadic table reuses the parent entry, while the inverse box
at the requested precision is the outer box in the nesting chain. -/
def CanonicalDyadicHalfAngleCertificateAt.of_even_parent
    (B : IntegralIdentities.ArctanInverseBisection)
    (precision n k : Nat) (hk : k < 2 ^ n)
    (h : CanonicalDyadicHalfAngleCertificateAt B
      (dyadicNestedRadicalParentPrecision precision) n k hk) :
    CanonicalDyadicHalfAngleCertificateAt B precision (n + 1) (2 * k) (by
      have hpow : 2 ^ (n + 1) = 2 * 2 ^ n := by
        rw [Nat.pow_succ]
        omega
      rw [hpow]
      omega) := by
  let childhk : 2 * k < 2 ^ (n + 1) := by
    have hpow : 2 ^ (n + 1) = 2 * 2 ^ n := by
      rw [Nat.pow_succ]
      omega
    rw [hpow]
    omega
  have hprecision : precision <= dyadicNestedRadicalParentPrecision precision := by
    unfold dyadicNestedRadicalParentPrecision
    have hsq : precision + 1 <= (precision + 1) * (precision + 1) :=
      Nat.le_mul_of_pos_right (precision + 1) (Nat.succ_pos _)
    have hscaled : precision + 1 <=
        16 * ((precision + 1) * (precision + 1)) :=
      Nat.le_trans hsq (Nat.le_mul_of_pos_left _ (by omega))
    have hp : precision <= precision + 1 := Nat.le_succ _
    simpa [Nat.mul_assoc] using Nat.le_trans hp hscaled
  have hbox := dyadicTangentBoxAt_contains_of_precision_le B
    precision (dyadicNestedRadicalParentPrecision precision) n k hk hprecision
  have houter :
      (dyadicTangentBoxAt B precision (n + 1) (2 * k) childhk).ContainsInterval
        (rationalHalfAngleTangentInterval
          ((dyadicNestedRadicalTableAt precision (n + 1) (2 * k)).1)
          h.cosineBox) := by
    have hbox' :
        (dyadicTangentBoxAt B precision n k hk).ContainsInterval
          (dyadicTangentBoxAt B
            (dyadicNestedRadicalParentPrecision precision) n k hk) := hbox
    have htrans := QInterval.ContainsInterval.trans hbox' h.outer_tangent_contains
    simpa [dyadicNestedRadicalTableAt_succ_even,
      dyadicTangentBoxAt, childhk,
      dyadicTangentBoxAt_even_input precision n k hk] using htrans
  refine {
    cosineBox := h.cosineBox
    cosineBox_subinterval := h.cosineBox_subinterval
    sineWitness := h.sineWitness
    cosineWitness := h.cosineWitness
    sine_nonneg := h.sine_nonneg
    cosine_nonneg := h.cosine_nonneg
    circle_identity := h.circle_identity
    sine_contains := ?_
    cosine_contains := h.cosine_contains
    outer_tangent_contains := houter }
  simpa [dyadicNestedRadicalTableAt_succ_even] using h.sine_contains

/-! A named proof object for the finite data supplied by a rational
half-angle search.  It is independent of any completed real number: the
witness, its sine-box location, and the three rational margin checks are
explicit fields. -/
structure RationalHalfAngleMarginCertificate
    (B : IntegralIdentities.ArctanInverseBisection)
    (precision depth k : Nat) (hk : k < 2 ^ depth) where
  witness : Rat
  witness_nonneg : 0 <= witness
  witness_le_one : witness <= 1
  sine_contains :
    (dyadicNestedRadicalTableAt precision depth k).1.lo <=
        rationalCircleSin witness /\
      rationalCircleSin witness <=
        (dyadicNestedRadicalTableAt precision depth k).1.hi
  epsilon : Rat
  tangent_width :
    (rationalHalfAngleTangentInterval
      (dyadicNestedRadicalTableAt precision depth k).1
      ({ lo := rationalCircleCos witness, hi := rationalCircleCos witness } : QInterval)).width
      <= epsilon
  left_margin :
    (dyadicTangentBoxAt B precision depth k hk).lo + epsilon <=
      rationalCircleSin witness / (1 + rationalCircleCos witness)
  right_margin :
    rationalCircleSin witness / (1 + rationalCircleCos witness) + epsilon <=
      (dyadicTangentBoxAt B precision depth k hk).hi

def RationalHalfAngleMarginCertificate.toCanonical
    {B : IntegralIdentities.ArctanInverseBisection}
    {precision depth k : Nat} {hk : k < 2 ^ depth}
    (h : RationalHalfAngleMarginCertificate B precision depth k hk) :
    CanonicalDyadicHalfAngleCertificateAt B precision depth k hk :=
  canonical_dyadic_certificate_at_of_rational_witness_with_margin
    B hk h.witness h.witness_nonneg h.witness_le_one h.sine_contains
    h.epsilon h.tangent_width h.left_margin h.right_margin

/-! An overlap-facing constructor for the even branch.  This is the natural
finite interface when the geometric proof establishes the public/table
overlap directly rather than exposing the successful grid witness. -/

noncomputable def DyadicEvenStepCertificate.of_overlap
    (B : IntegralIdentities.ArctanInverseBisection)
    (precision n k : Nat) (hk : k < 2 ^ n) (hpos : 0 < k)
    (hover : QInterval.Overlaps
      (rationalCircleSinInterval
        (dyadicTangentBoxAt B precision (n + 1) (2 * k) (by
          have hpow : 2 ^ (n + 1) = 2 * 2 ^ n := by
            rw [Nat.pow_succ]
            omega
          rw [hpow]
          omega)))
      ((dyadicNestedRadicalTableAt
        (dyadicNestedRadicalParentPrecision precision) n k).1)) :
    DyadicEvenStepCertificate B precision n k hk := by
  classical
  let hex :=
    exists_rationalTangentWitnessBoxSearch_of_overlap_of_positive_width
      (dyadicTangentBoxAt_bounds B precision (n + 1) (2 * k) (by
        have hpow : 2 ^ (n + 1) = 2 * 2 ^ n := by
          rw [Nat.pow_succ]
          omega
        rw [hpow]
        omega))
      (dyadicNestedRadicalTableAt_bounds
        (dyadicNestedRadicalParentPrecision precision) n k (by omega)).1
      hover
      (dyadicNestedRadicalTableAt_sin_width_pos
        (dyadicNestedRadicalParentPrecision precision) n k (by omega) hpos)
  let m := Classical.choose hex
  let u := Classical.choose (Classical.choose_spec hex)
  exact DyadicEvenStepCertificate.ofWitnessSearch B precision n k hk m
    ⟨u, Classical.choose_spec (Classical.choose_spec hex)⟩

/-! Canonical half-angle certificates naturally prove overlap, rather than
literal equality of the two interval implementations.  These adapters expose
the lower and reflected-upper branch facts in precisely the form accepted by
`DyadicTangentWitnessFamily.of_branch_overlap_families`. -/

theorem lower_overlap_of_canonical_halfAngle_certificate
    (B : IntegralIdentities.ArctanInverseBisection)
    (precision n j : Nat) (hbound : 2 * j + 1 <= 2 ^ n)
    (h : CanonicalDyadicHalfAngleCertificateAt B precision (n + 1)
      (2 * j + 1) (by
        have hpow : 2 ^ (n + 1) = 2 * 2 ^ n := by
          rw [Nat.pow_succ]
          omega
        rw [hpow]
        omega)) :
    QInterval.Overlaps
      (rationalCircleSinInterval
        (dyadicTangentBoxAt B precision (n + 1) (2 * j + 1) (by
          have hpow : 2 ^ (n + 1) = 2 * 2 ^ n := by
            rw [Nat.pow_succ]
            omega
          rw [hpow]
          omega)))
      ((dyadicNestedRadicalTableAt precision (n + 1) (2 * j + 1)).1) := by
  exact canonical_dyadic_overlap_of_halfAngle_outer_tangent_at B _
    h.cosineBox_subinterval h.outer_tangent_contains
    h.sine_nonneg h.cosine_nonneg h.circle_identity
    h.sine_contains h.cosine_contains

theorem upper_overlap_of_canonical_halfAngle_certificate
    (B : IntegralIdentities.ArctanInverseBisection)
    (precision n k : Nat) (hupper : 2 ^ n < k)
    (hk : k < 2 ^ (n + 1))
    (h : CanonicalDyadicHalfAngleCertificateAt B precision (n + 1) k hk) :
    QInterval.Overlaps
      (rationalCircleSinInterval
        (dyadicTangentBoxAt B precision (n + 1) k hk))
      ((dyadicNestedRadicalTableAt precision (n + 1) k).1) := by
  exact canonical_dyadic_overlap_of_halfAngle_outer_tangent_at B hk
    h.cosineBox_subinterval h.outer_tangent_contains
    h.sine_nonneg h.cosine_nonneg h.circle_identity
    h.sine_contains h.cosine_contains

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

noncomputable def DyadicTangentWitnessFamily.of_canonical_candidate_family
    (B : IntegralIdentities.ArctanInverseBisection)
    (ht0 : (B.tangentAt 0
      RationalCircle.GeometricTrig.firstQuadrantBranch_zero).Equiv
      RealRaw.zero)
    (candidates : forall (precision depth k : Nat) (hk : k < 2 ^ depth),
      List Rat)
    (witness : forall (precision depth k : Nat) (hk : k < 2 ^ depth),
      Rat)
    (hmem : forall (precision depth k : Nat) (hk : k < 2 ^ depth),
      witness precision depth k hk ∈ candidates precision depth k hk)
    (hadm : forall (precision depth k : Nat) (hk : k < 2 ^ depth),
      canonicalDyadicCertificateAdmissibleBool B precision depth k hk
        (witness precision depth k hk) = true) :
    DyadicTangentWitnessFamily B := by
  apply DyadicTangentWitnessFamily.of_canonical_search_family B ht0 candidates
  intro precision depth k hk
  exact canonicalDyadicCertificateSearchAt_some_of_mem_of_admissible
    B (hmem precision depth k hk) (hadm precision depth k hk)

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

theorem exists_dyadic_tangent_witness_search_of_overlap_family
    (B : IntegralIdentities.ArctanInverseBisection)
    (hover : forall (depth k : Nat) (hk : k < 2 ^ depth), 0 < k ->
      forall precision, QInterval.Overlaps
        (rationalCircleSinInterval
          (dyadicTangentBoxAt B precision depth k hk))
        ((dyadicNestedRadicalTableAt precision depth k).1)) :
    forall (depth k : Nat) (hk : k < 2 ^ depth), 0 < k ->
      forall precision, ∃ m u, rationalTangentWitnessBoxSearch
        (dyadicTangentBoxAt B precision depth k hk)
        (dyadicNestedRadicalTableAt precision depth k).1 m = some u := by
  intro depth k hk hpos precision
  apply exists_rationalTangentWitnessBoxSearch_of_overlap_of_positive_width
    (dyadicTangentBoxAt_bounds B precision depth k hk)
    (dyadicNestedRadicalTableAt_bounds precision depth k (by omega)).1
    (hover depth k hk hpos precision)
  exact dyadicNestedRadicalTableAt_sin_width_pos precision depth k hk hpos

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

/-! A canonical-witness variant of the overlap assembly.  All three parity
branches are supplied by rational unit-circle certificates; the zero endpoint
is still handled separately by the exact endpoint law. -/

noncomputable def DyadicTangentWitnessFamily.of_canonical_halfAngle_families
    (B : IntegralIdentities.ArctanInverseBisection)
    (ht0 : (B.tangentAt 0
      RationalCircle.GeometricTrig.firstQuadrantBranch_zero).Equiv
      RealRaw.zero)
    (even_certificate : forall (precision n j : Nat) (hj : j < 2 ^ n),
      CanonicalDyadicHalfAngleCertificateAt B precision (n + 1) (2 * j)
        (by
          have hpow : 2 ^ (n + 1) = 2 * 2 ^ n := by
            rw [Nat.pow_succ]
            omega
          rw [hpow]
          omega))
    (lower_certificate : forall (precision n j : Nat)
      (hbound : 2 * j + 1 <= 2 ^ n),
      CanonicalDyadicHalfAngleCertificateAt B precision (n + 1)
        (2 * j + 1) (by
          have hpow : 2 ^ (n + 1) = 2 * 2 ^ n := by
            rw [Nat.pow_succ]
            omega
          rw [hpow]
          omega))
    (upper_certificate : forall (precision n k : Nat)
      (hupper : 2 ^ n < k) (hk : k < 2 ^ (n + 1)),
      CanonicalDyadicHalfAngleCertificateAt B precision (n + 1) k hk) :
    DyadicTangentWitnessFamily B := by
  apply DyadicTangentWitnessFamily.of_branch_overlap_families B ht0
  · intro precision n j hj
    exact canonical_dyadic_overlap_of_halfAngle_outer_tangent_at B _
      (even_certificate precision n j hj).cosineBox_subinterval
      (even_certificate precision n j hj).outer_tangent_contains
      (even_certificate precision n j hj).sine_nonneg
      (even_certificate precision n j hj).cosine_nonneg
      (even_certificate precision n j hj).circle_identity
      (even_certificate precision n j hj).sine_contains
      (even_certificate precision n j hj).cosine_contains
  · intro precision n j hbound
    exact lower_overlap_of_canonical_halfAngle_certificate B precision n j
      hbound (lower_certificate precision n j hbound)
  · intro precision n k hupper hk
    exact upper_overlap_of_canonical_halfAngle_certificate B precision n k
      hupper hk (upper_certificate precision n k hupper hk)

/-! The theorem-facing form of the canonical route.  Once the evaluator
identifies its sampled values with the nested-radical stages, the branch
certificates can be supplied directly; users do not need to manually unpack
the intermediate witness family. -/

theorem ArctanSinPiConstruction.halfIntegral_equiv_of_canonical_halfAngle_families
    (S : ArctanSinPiConstruction)
    (pub : Integral.Construction S.onHalf.toRealFunRaw
      0 ((1 : Rat) / 2))
    (g : RealFunRaw)
    (cg : Integral.Construction g 0 ((1 : Rat) / 2))
    (hdyadic : pub.plan = Integral.staticDyadicPlan)
    (hplan : pub.plan = cg.plan)
    (hevaluator : forall n k,
      k < (pub.plan n).subdivisions ->
      g.compute
        (leftPoint 0 ((1 : Rat) / 2)
          (pub.plan n).subdivisions k)
        (pub.plan n).evalPrecision =
        dyadicNestedRadicalStageSinAt n k)
    (ht0 : (S.inverse.tangentAt 0
      RationalCircle.GeometricTrig.firstQuadrantBranch_zero).Equiv
      RealRaw.zero)
    (even_certificate : forall (precision n j : Nat) (hj : j < 2 ^ n),
      CanonicalDyadicHalfAngleCertificateAt S.inverse precision (n + 1) (2 * j)
        (by
          have hpow : 2 ^ (n + 1) = 2 * 2 ^ n := by
            rw [Nat.pow_succ]
            omega
          rw [hpow]
          omega))
    (lower_certificate : forall (precision n j : Nat)
      (hbound : 2 * j + 1 <= 2 ^ n),
      CanonicalDyadicHalfAngleCertificateAt S.inverse precision (n + 1)
        (2 * j + 1) (by
          have hpow : 2 ^ (n + 1) = 2 * 2 ^ n := by
            rw [Nat.pow_succ]
            omega
          rw [hpow]
          omega))
    (upper_certificate : forall (precision n k : Nat)
      (hupper : 2 ^ n < k) (hk : k < 2 ^ (n + 1)),
      CanonicalDyadicHalfAngleCertificateAt S.inverse precision (n + 1) k hk) :
    (S.halfIntegral pub).Equiv
      (Integral.integral g 0 ((1 : Rat) / 2) cg) := by
  exact S.halfIntegral_equiv_of_witness_family
    pub g cg hdyadic hplan hevaluator
    (DyadicTangentWitnessFamily.of_canonical_halfAngle_families
      S.inverse ht0 even_certificate lower_certificate upper_certificate)

theorem ArctanSinPiConstruction.halfIntegral_equiv_reciprocalPi_of_canonical_halfAngle_families
    (S : ArctanSinPiConstruction)
    (pub : Integral.Construction S.onHalf.toRealFunRaw
      0 ((1 : Rat) / 2))
    (g : RealFunRaw)
    (cg : Integral.Construction g 0 ((1 : Rat) / 2))
    (hdyadic : pub.plan = Integral.staticDyadicPlan)
    (hplan : pub.plan = cg.plan)
    (hevaluator : forall n k,
      k < (pub.plan n).subdivisions ->
      g.compute
        (leftPoint 0 ((1 : Rat) / 2)
          (pub.plan n).subdivisions k)
        (pub.plan n).evalPrecision =
        dyadicNestedRadicalStageSinAt n k)
    (ht0 : (S.inverse.tangentAt 0
      RationalCircle.GeometricTrig.firstQuadrantBranch_zero).Equiv
      RealRaw.zero)
    (even_certificate : forall (precision n j : Nat) (hj : j < 2 ^ n),
      CanonicalDyadicHalfAngleCertificateAt S.inverse precision (n + 1) (2 * j)
        (by
          have hpow : 2 ^ (n + 1) = 2 * 2 ^ n := by
            rw [Nat.pow_succ]
            omega
          rw [hpow]
          omega))
    (lower_certificate : forall (precision n j : Nat)
      (hbound : 2 * j + 1 <= 2 ^ n),
      CanonicalDyadicHalfAngleCertificateAt S.inverse precision (n + 1)
        (2 * j + 1) (by
          have hpow : 2 ^ (n + 1) = 2 * 2 ^ n := by
            rw [Nat.pow_succ]
            omega
          rw [hpow]
          omega))
    (upper_certificate : forall (precision n k : Nat)
      (hupper : 2 ^ n < k) (hk : k < 2 ^ (n + 1)),
      CanonicalDyadicHalfAngleCertificateAt S.inverse precision (n + 1) k hk)
    (hintegral :
      (Integral.integral g 0 ((1 : Rat) / 2) cg).Equiv reciprocalPiRaw) :
    (S.halfIntegral pub).Equiv reciprocalPiRaw := by
  have hpub := S.halfIntegral_equiv_of_canonical_halfAngle_families
    pub g cg hdyadic hplan hevaluator ht0 even_certificate
    lower_certificate upper_certificate
  exact RealRaw.equiv_trans
    (S.halfIntegral_valid pub)
    (FTC.integral_valid_of_construction cg)
    reciprocalPiRaw_valid hpub hintegral

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

/-! The packaged certificate family is the proof-facing representation; this
adapter turns it into the executable witness family consumed by the public
integral transport theorem.  It adds one representation edge without
introducing pairwise equalities between all evaluators. -/

noncomputable def DyadicNestedRadicalBranchCertificateFamily.toWitnessFamily
    {B : IntegralIdentities.ArctanInverseBisection}
    (H : DyadicNestedRadicalBranchCertificateFamily B) :
    DyadicTangentWitnessFamily B :=
  DyadicTangentWitnessFamily.of_branch_certificate_families
    B H.endpoint_zero H.even H.lower H.upper

/-! The equality-shaped child certificates are useful when two interval
implementations are definitionally synchronized, but the geometric proof
only needs overlap.  This direct adapter keeps that weaker contract and
avoids asking the half-angle argument to prove an unnecessary evaluator
equality. -/

theorem dyadicNestedRadical_sample_overlap_of_direct_branch_overlaps
    (B : IntegralIdentities.ArctanInverseBisection)
    (zero_overlap : forall (precision depth : Nat) (hk : 0 < 2 ^ depth),
      QInterval.Overlaps
        ((sinPiRawOfArctan B
          (leftPoint 0 ((1 : Rat) / 2) (2 ^ depth) 0)
          (dyadicHalfDomain (by omega))).compute precision)
        (dyadicNestedRadicalTableAt precision depth 0).1)
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
        (dyadicNestedRadicalTableAt precision (n + 1) (2 * j)).1)
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
        (dyadicNestedRadicalTableAt precision (n + 1) (2 * j + 1)).1)
    (upper_overlap : forall (precision n k : Nat)
      (hupper : 2 ^ n < k) (hk : k < 2 ^ (n + 1)),
      QInterval.Overlaps
        (rationalCircleSinInterval
          (dyadicTangentBoxAt B precision (n + 1) k
            (by
              have hpow : 2 ^ (n + 1) = 2 * 2 ^ n := by
                rw [Nat.pow_succ]
                omega
              rw [hpow]
              omega)))
        (dyadicNestedRadicalTableAt precision (n + 1) k).1) :
    forall (precision depth k : Nat) (hk : k < 2 ^ depth),
      QInterval.Overlaps
        ((sinPiRawOfArctan B
          (leftPoint 0 ((1 : Rat) / 2) (2 ^ depth) k)
          (dyadicHalfDomain hk)).compute precision)
        (dyadicNestedRadicalTableAt precision depth k).1 := by
  intro precision depth k hk
  cases depth with
  | zero =>
      have hk' : k = 0 := by omega
      subst k
      exact zero_overlap precision 0 (by native_decide)
  | succ n =>
      by_cases hzero : k = 0
      · subst k
        exact zero_overlap precision (n + 1) (by omega)
      by_cases heven : k % 2 = 0
      · obtain ⟨j, rfl⟩ : ∃ j, k = 2 * j := by
          exact ⟨k / 2, by omega⟩
        have hj : j < 2 ^ n := by
          rw [Nat.pow_succ] at hk
          omega
        have hbox := even_overlap precision n j hj
        simpa [sinPiRawOfArctan, dyadicTangentBoxAt] using hbox
      · have hodd : k % 2 = 1 := by omega
        by_cases hlower : k <= 2 ^ n
        · obtain ⟨j, rfl⟩ : ∃ j, k = 2 * j + 1 := by
            exact ⟨k / 2, by omega⟩
          have hbound : 2 * j + 1 <= 2 ^ n := by omega
          have hbox := lower_overlap precision n j hbound
          simpa [sinPiRawOfArctan, dyadicTangentBoxAt] using hbox
        · have hupper : 2 ^ n < k := by omega
          have hbox := upper_overlap precision n k hupper hk
          simpa [sinPiRawOfArctan, dyadicTangentBoxAt] using hbox

theorem dyadicNestedRadical_sample_overlap_of_canonical_halfAngle_certificate_family
    (B : IntegralIdentities.ArctanInverseBisection)
    (ht0 : (B.tangentAt 0
      RationalCircle.GeometricTrig.firstQuadrantBranch_zero).Equiv
      RealRaw.zero)
    (hcertificate : forall (precision depth k : Nat) (hk : k < 2 ^ depth),
      0 < k -> CanonicalDyadicHalfAngleCertificateAt B precision depth k hk) :
    forall (precision depth k : Nat) (hk : k < 2 ^ depth),
      QInterval.Overlaps
        ((sinPiRawOfArctan B
          (leftPoint 0 ((1 : Rat) / 2) (2 ^ depth) k)
          (dyadicHalfDomain hk)).compute precision)
        (dyadicNestedRadicalTableAt precision depth k).1 := by
  apply dyadicNestedRadical_sample_overlap_of_direct_branch_overlaps B
  · intro precision depth hk
    exact dyadicNestedRadical_zero_sample_overlap_of_endpoint B ht0
      precision depth hk
  · intro precision n j hj
    by_cases hj0 : j = 0
    · subst j
      have hzero := dyadicNestedRadical_zero_sample_overlap_of_endpoint B ht0
        precision (n + 1) (by omega)
      simpa [sinPiRawOfArctan, dyadicTangentBoxAt,
        dyadicNestedRadicalTableAt_zero_sin] using hzero
    have hpow : 2 ^ (n + 1) = 2 * 2 ^ n := by
      rw [Nat.pow_succ]
      omega
    have hk2 : 2 * j < 2 ^ (n + 1) := by
      rw [hpow]
      omega
    have h := hcertificate precision (n + 1) (2 * j) hk2 (by omega)
    exact canonical_dyadic_overlap_of_halfAngle_outer_tangent_at B hk2
      h.cosineBox_subinterval h.outer_tangent_contains h.sine_nonneg h.cosine_nonneg
      h.circle_identity h.sine_contains h.cosine_contains
  · intro precision n j hbound
    exact lower_overlap_of_canonical_halfAngle_certificate B precision n j
      hbound (hcertificate precision (n + 1) (2 * j + 1) (by omega) (by omega))
  · intro precision n k hupper hk
    exact upper_overlap_of_canonical_halfAngle_certificate B precision n k
      hupper hk (hcertificate precision (n + 1) k hk (by omega))

noncomputable def DyadicTangentWitnessFamily.of_canonical_halfAngle_certificate_family
    (B : IntegralIdentities.ArctanInverseBisection)
    (ht0 : (B.tangentAt 0
      RationalCircle.GeometricTrig.firstQuadrantBranch_zero).Equiv
      RealRaw.zero)
    (hcertificate : forall (precision depth k : Nat) (hk : k < 2 ^ depth),
      0 < k -> CanonicalDyadicHalfAngleCertificateAt B precision depth k hk) :
    DyadicTangentWitnessFamily B := by
  apply DyadicTangentWitnessFamily.of_overlap_family B ht0
  intro depth k hk hpos precision
  have h := dyadicNestedRadical_sample_overlap_of_canonical_halfAngle_certificate_family
    B ht0 hcertificate precision depth k hk
  simpa [sinPiRawOfArctan, dyadicTangentBoxAt] using h

/-! The parity induction can now be exposed with only the genuinely new
geometric cases as input.  A positive even index is reduced to its parent
index; a positive odd index is supplied by the caller. -/
noncomputable def DyadicTangentWitnessFamily.of_odd_canonical_halfAngle_certificate_family
    (B : IntegralIdentities.ArctanInverseBisection)
    (ht0 : (B.tangentAt 0
      RationalCircle.GeometricTrig.firstQuadrantBranch_zero).Equiv
      RealRaw.zero)
    (hodd : forall (precision depth k : Nat) (hk : k < 2 ^ depth),
      0 < k -> k % 2 = 1 ->
        CanonicalDyadicHalfAngleCertificateAt B precision depth k hk) :
    DyadicTangentWitnessFamily B := by
  let rec build (precision depth k : Nat) (hk : k < 2 ^ depth) :
      0 < k -> CanonicalDyadicHalfAngleCertificateAt B precision depth k hk := by
    intro hpos
    cases depth with
    | zero => omega
    | succ n =>
        by_cases heven : k % 2 = 0
        · let j := k / 2
          have hkj : k = 2 * j := by
            dsimp [j]
            omega
          have hj : j < 2 ^ n := by
            rw [Nat.pow_succ] at hk
            omega
          have hjpos : 0 < j := by omega
          have hcert := CanonicalDyadicHalfAngleCertificateAt.of_even_parent B
            precision n j hj
            (build (dyadicNestedRadicalParentPrecision precision) n j hj hjpos)
          simpa [hkj] using hcert
        · have hodd' : k % 2 = 1 := by omega
          exact hodd precision (n + 1) k hk hpos hodd'
  apply DyadicTangentWitnessFamily.of_canonical_halfAngle_certificate_family B ht0
  intro precision depth k hk hpos
  exact build precision depth k hk hpos

/-! Separate the two genuinely odd geometric branches.  This is the
user-facing induction interface: lower odd cells use the positive
half-angle certificate, while upper odd cells use the reflected cosine
certificate. -/
noncomputable def DyadicTangentWitnessFamily.of_lower_upper_odd_canonical_halfAngle_certificate_families
    (B : IntegralIdentities.ArctanInverseBisection)
    (ht0 : (B.tangentAt 0
      RationalCircle.GeometricTrig.firstQuadrantBranch_zero).Equiv
      RealRaw.zero)
    (lower : forall (precision n j : Nat)
      (hbound : 2 * j + 1 <= 2 ^ n),
      CanonicalDyadicHalfAngleCertificateAt B precision (n + 1) (2 * j + 1) (by
        have hpow : 2 ^ (n + 1) = 2 * 2 ^ n := by
          rw [Nat.pow_succ]
          omega
        rw [hpow]
        omega))
    (upper : forall (precision n k : Nat)
      (hupper : 2 ^ n < k) (hk : k < 2 ^ (n + 1)),
      CanonicalDyadicHalfAngleCertificateAt B precision (n + 1) k hk) :
    DyadicTangentWitnessFamily B := by
  apply DyadicTangentWitnessFamily.of_odd_canonical_halfAngle_certificate_family
    B ht0
  intro precision depth k hk hpos hodd
  cases depth with
  | zero => omega
  | succ n =>
      by_cases hlower : k <= 2 ^ n
      · let j := k / 2
        have hkj : k = 2 * j + 1 := by
          dsimp [j]
          omega
        have hbound : 2 * j + 1 <= 2 ^ n := by omega
        have hcert := lower precision n j hbound
        simpa [hkj] using hcert
      · have hupper : 2 ^ n < k := by omega
        exact upper precision n k hupper hk

theorem ArctanSinPiConstruction.halfIntegral_equiv_of_canonical_halfAngle_certificate_family
    (S : ArctanSinPiConstruction)
    (pub : Integral.Construction S.onHalf.toRealFunRaw
      0 ((1 : Rat) / 2))
    (g : RealFunRaw)
    (cg : Integral.Construction g 0 ((1 : Rat) / 2))
    (hdyadic : pub.plan = Integral.staticDyadicPlan)
    (hplan : pub.plan = cg.plan)
    (hevaluator : forall n k,
      k < (pub.plan n).subdivisions ->
      g.compute
        (leftPoint 0 ((1 : Rat) / 2)
          (pub.plan n).subdivisions k)
        (pub.plan n).evalPrecision =
        dyadicNestedRadicalStageSinAt n k)
    (ht0 : (S.inverse.tangentAt 0
      RationalCircle.GeometricTrig.firstQuadrantBranch_zero).Equiv
      RealRaw.zero)
    (hcertificate : forall (precision depth k : Nat) (hk : k < 2 ^ depth),
      0 < k -> CanonicalDyadicHalfAngleCertificateAt S.inverse precision depth k hk) :
    (S.halfIntegral pub).Equiv
      (Integral.integral g 0 ((1 : Rat) / 2) cg) := by
  exact S.halfIntegral_equiv_of_witness_family
    pub g cg hdyadic hplan hevaluator
    (DyadicTangentWitnessFamily.of_canonical_halfAngle_certificate_family
      S.inverse ht0 hcertificate)

theorem ArctanSinPiConstruction.halfIntegral_equiv_reciprocalPi_of_canonical_halfAngle_certificate_family
    (S : ArctanSinPiConstruction)
    (pub : Integral.Construction S.onHalf.toRealFunRaw
      0 ((1 : Rat) / 2))
    (g : RealFunRaw)
    (cg : Integral.Construction g 0 ((1 : Rat) / 2))
    (hdyadic : pub.plan = Integral.staticDyadicPlan)
    (hplan : pub.plan = cg.plan)
    (hevaluator : forall n k,
      k < (pub.plan n).subdivisions ->
      g.compute
        (leftPoint 0 ((1 : Rat) / 2)
          (pub.plan n).subdivisions k)
        (pub.plan n).evalPrecision =
        dyadicNestedRadicalStageSinAt n k)
    (ht0 : (S.inverse.tangentAt 0
      RationalCircle.GeometricTrig.firstQuadrantBranch_zero).Equiv
      RealRaw.zero)
    (hcertificate : forall (precision depth k : Nat) (hk : k < 2 ^ depth),
      0 < k -> CanonicalDyadicHalfAngleCertificateAt S.inverse precision depth k hk)
    (hintegral : (Integral.integral g 0 ((1 : Rat) / 2) cg).Equiv
      reciprocalPiRaw) :
    (S.halfIntegral pub).Equiv reciprocalPiRaw := by
  have htransport :=
    S.halfIntegral_equiv_of_canonical_halfAngle_certificate_family
      pub g cg hdyadic hplan hevaluator ht0 hcertificate
  exact RealRaw.equiv_trans
    (S.halfIntegral_valid pub)
    (FTC.integral_valid_of_construction cg)
    reciprocalPiRaw_valid htransport hintegral

end SinPiIntegral

end ComputableAnalysis
