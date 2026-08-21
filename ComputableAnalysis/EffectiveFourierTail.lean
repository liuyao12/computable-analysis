import ComputableAnalysis.EffectiveFourierSeries

/-!
# Generic effective Fourier tails

This module separates the reusable convergence step from any particular
coefficient formula.  A Fourier stage is supplied together with coordinate
tail bounds; the bounds are then packaged as the project's effective complex
series.  No completed complex or real limit is introduced.
-/

namespace ComputableAnalysis

structure EffectiveFourierTailCertificate where
  root : QComplex
  mode : Nat
  stage : Nat -> QComplex
  radius : Nat -> Rat
  radius_nonneg : forall n, 0 <= radius n
  future_coordinate_tail : forall k n, k <= n ->
    qabs ((stage n).re - (stage k).re) <= radius k /\
    qabs ((stage n).im - (stage k).im) <= radius k
  radius_shrinks : ShrinksToZero radius

def EffectiveFourierTailCertificate.toSeries
    (certificate : EffectiveFourierTailCertificate) : EffectiveFourierSeries where
  root := certificate.root
  mode := certificate.mode
  stage := fun n => [certificate.stage n]
  candidate := {
    compute := fun n =>
      QBox.point (certificate.stage n)
  }
  radius := certificate.radius
  candidate_stage := by
    intro n
    change (QBox.point
      (finiteFourierSum certificate.root certificate.mode
        [certificate.stage n])).NestedIn _
    simp [finiteFourierSum_singleton, QComplex.natPow,
      QComplex.mul_one_cert]
    exact ⟨QComplex.le_refl _, QComplex.le_refl _⟩
  candidate_ordered := by
    intro n
    exact QComplex.le_refl _
  candidate_shrinks := by
    intro eps
    refine ⟨0, ?_⟩
    intro n hn
    simp [QBox.width, QBox.height, QBox.point]
    constructor <;> grind [eps.property]
  future_containment := by
    intro k n hkn
    have htail := certificate.future_coordinate_tail k n hkn
    change (QBox.point (certificate.stage n)).NestedIn
      (QBox.expand (QBox.point (certificate.stage k))
        (certificate.radius k))
    unfold QBox.NestedIn QBox.expand QBox.point
    simp only [QComplex.le_def]
    constructor
    · constructor
      · have hlow := neg_qabs_le_self
          ((certificate.stage n).re - (certificate.stage k).re)
        grind [Rat.sub_eq_add_neg]
      · have hlow := neg_qabs_le_self
          ((certificate.stage n).im - (certificate.stage k).im)
        grind [Rat.sub_eq_add_neg]
    · constructor
      · have hupp := self_le_qabs
          ((certificate.stage n).re - (certificate.stage k).re)
        grind [Rat.sub_eq_add_neg]
      · have hupp := self_le_qabs
          ((certificate.stage n).im - (certificate.stage k).im)
        grind [Rat.sub_eq_add_neg]
  radius_shrinks := certificate.radius_shrinks

theorem EffectiveFourierTailCertificate.toSeries_stage_contained
    (certificate : EffectiveFourierTailCertificate) (n : Nat) :
    (QBox.point
      (finiteFourierSum certificate.root certificate.mode
        [certificate.stage n])).NestedIn
      ((certificate.toSeries).candidate.compute n) := by
  exact (certificate.toSeries).candidate_stage n

theorem EffectiveFourierTailCertificate.toSeries_valid
    (certificate : EffectiveFourierTailCertificate) :
    certificate.toSeries.stabilized.Valid := by
  exact EffectiveFourierSeries.stabilized_valid certificate.toSeries

/-! A generic tail certificate therefore exposes an actual finite Fourier
stage as its precision witness.  The witness is the computed rational-
complex value itself, while the stabilized box supplies the certified error
bar. -/
theorem EffectiveFourierTailCertificate.precision_witness
    (certificate : EffectiveFourierTailCertificate) (eps : QPos) :
    ∃ N : Nat, ∃ q : QComplex,
      q = certificate.stage N /\
      (certificate.toSeries.stabilized.compute N).width <= eps.val /\
      (certificate.toSeries.stabilized.compute N).height <= eps.val := by
  obtain ⟨N, q, hq, hwidth, hheight⟩ :=
    (certificate.toSeries).precision_witness eps
  refine ⟨N, certificate.stage N, ?_, hwidth, hheight⟩
  simpa [EffectiveFourierTailCertificate.toSeries,
    finiteFourierSum_singleton, QComplex.natPow,
    QComplex.mul_one_cert, QComplex.add, QComplex.zero] using hq

/-! The raw tail hypothesis is also exposed as an explicit coordinate box.
This is the error-bar statement used by downstream Fourier computations: at
stage `n`, every later stage lies within the radius attached to stage `k`.
It is stated over rationals, before any complex completion is introduced. -/
theorem EffectiveFourierTailCertificate.future_stage_coordinate_enclosure
    (certificate : EffectiveFourierTailCertificate)
    (k n : Nat) (hkn : k <= n) :
    (-certificate.radius k <=
        (certificate.stage n).re - (certificate.stage k).re /\
      (certificate.stage n).re - (certificate.stage k).re <=
        certificate.radius k) /\
    (-certificate.radius k <=
        (certificate.stage n).im - (certificate.stage k).im /\
      (certificate.stage n).im - (certificate.stage k).im <=
        certificate.radius k) := by
  have htail := certificate.future_coordinate_tail k n hkn
  constructor
  · exact ⟨by
      exact Rat.le_trans (Rat.neg_le_neg htail.1)
        (neg_qabs_le_self _), by
      exact Rat.le_trans (self_le_qabs _) htail.1⟩
  · exact ⟨by
      exact Rat.le_trans (Rat.neg_le_neg htail.2)
        (neg_qabs_le_self _), by
      exact Rat.le_trans (self_le_qabs _) htail.2⟩

/-! The geometric quarter-turn family is now an instance of the generic
tail interface.  The certificate is stated independently of the particular
`EffectiveFourierSeries` constructor, so other coefficient algorithms can
reuse the same bridge. -/
def quarterTurnGeometricTailCertificate
    (r : Rat) (hr0 : 0 <= r) (hrhalf : r <= (1 : Rat) / 2)
    (hr1 : r < 1) : EffectiveFourierTailCertificate where
  root := RotationSeries.imaginaryUnit
  mode := 1
  stage := quarterTurnGeometricStage r
  radius := fun n => 2 * r ^ n
  radius_nonneg := by
    intro n
    exact Rat.mul_nonneg (by native_decide) (Rat.pow_nonneg hr0)
  future_coordinate_tail := by
    intro k n hkn
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkn
    have hfactor : 1 / (1 - r) <= 2 := by
      have hden : 0 < 1 - r := by grind
      apply Rat.le_of_mul_le_mul_right (c := 1 - r)
      · calc
          1 / (1 - r) * (1 - r) = 1 := by
            rw [Rat.div_def, Rat.one_mul,
              Rat.inv_mul_cancel (1 - r) (Rat.ne_of_gt hden)]
          _ <= 2 * (1 - r) := by grind
      · exact hden
    have htail :=
      quarterTurnGeometricStage_block_coord_abs_le_inv_one_sub hr0 hr1 k d
    have hpow : 0 <= r ^ k := Rat.pow_nonneg hr0
    have hscaled : r ^ k * (1 / (1 - r)) <= 2 * r ^ k := by
      simpa [Rat.mul_comm] using
        (Rat.mul_le_mul_of_nonneg_left hfactor hpow)
    exact ⟨Rat.le_trans htail.1 hscaled, Rat.le_trans htail.2 hscaled⟩
  radius_shrinks := by
    apply shrinksToZero_of_natOverSuccBound (C := 2)
    intro n
    have hpow := Series.pow_le_half_pow hr0 hrhalf n
    have hhalf := Series.half_pow_le_one_div_succ n
    have hbound := Rat.le_trans hpow hhalf
    have hscaled := Rat.mul_le_mul_of_nonneg_left hbound (by native_decide : (0 : Rat) <= 2)
    simpa [Rat.mul_comm, Rat.div_def] using hscaled

theorem quarterTurnGeometricTailCertificate_valid
    (r : Rat) (hr0 : 0 <= r) (hrhalf : r <= (1 : Rat) / 2)
    (hr1 : r < 1) :
    (quarterTurnGeometricTailCertificate r hr0 hrhalf hr1).toSeries.stabilized.Valid := by
  exact EffectiveFourierTailCertificate.toSeries_valid _

end ComputableAnalysis
