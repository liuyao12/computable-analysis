import ComputableAnalysis.FiniteFourierFoundation
import ComputableAnalysis.FiniteFourierGeometric
import ComputableAnalysis.Series
import ComputableAnalysis.ComplexPathIntegral

/-!
# Effective Fourier-stage interface

An infinite Fourier object is exposed here as a certified family of finite
rational-complex stages.  The limit is obtained by the existing finite-prefix
complex-box stabilization theorem; no completed `Real`, topology, or rate of
convergence is built into the interface.
-/

namespace ComputableAnalysis

structure EffectiveFourierSeries where
  root : QComplex
  mode : Nat
  stage : Nat -> List QComplex
  candidate : ComplexRaw
  radius : Nat -> Rat
  candidate_stage : forall n,
    (QBox.point (finiteFourierSum root mode (stage n))).NestedIn
      (candidate.compute n)
  candidate_ordered : forall n, (candidate.compute n).Ordered
  candidate_shrinks : ComplexRaw.WidthsShrinkToZero candidate.compute
  future_containment : forall k n, k <= n ->
    (candidate.compute n).NestedIn
      (QBox.expand (candidate.compute k) (radius k))
  radius_shrinks : ShrinksToZero radius

def EffectiveFourierSeries.stabilized
    (F : EffectiveFourierSeries) : ComplexRaw :=
  ComplexRaw.cauchyStabilize F.candidate F.radius

theorem EffectiveFourierSeries.stabilized_valid
    (F : EffectiveFourierSeries) : F.stabilized.Valid := by
  exact ComplexRaw.cauchyStabilize_valid
    F.candidate_ordered F.candidate_shrinks
    F.future_containment F.radius_shrinks

theorem EffectiveFourierSeries.stage_contained
    (F : EffectiveFourierSeries) (n : Nat) :
    (QBox.point (finiteFourierSum F.root F.mode (F.stage n))).NestedIn
      (F.stabilized.compute n) := by
  exact QBox.nested_trans (F.candidate_stage n)
    (ComplexRaw.cauchyStabilize_contains_current F.future_containment n)

/-! A precision witness is the actual finite rational-complex Fourier stage,
not merely an abstract point in the stabilized box. -/
theorem EffectiveFourierSeries.precision_witness
    (F : EffectiveFourierSeries) (eps : QPos) :
    ∃ N : Nat, ∃ q : QComplex,
      (QBox.point q).NestedIn (F.stabilized.compute N) /\
      (F.stabilized.compute N).width <= eps.val /\
      (F.stabilized.compute N).height <= eps.val := by
  obtain ⟨N, hN⟩ := (F.stabilized_valid).2.2 eps
  refine ⟨N, finiteFourierSum F.root F.mode (F.stage N),
    F.stage_contained N, ?_⟩
  exact hN N (Nat.le_refl N)

/-! Every finite Fourier computation is an effective series with finite
support: the stage is already stable, so its radius and all box widths are
zero.  This is a useful sanity-check instance before adding genuinely
infinite coefficient tails. -/
def finiteSupportFourierSeries
    (root : QComplex) (mode : Nat) (samples : List QComplex) :
    EffectiveFourierSeries where
  root := root
  mode := mode
  stage := fun _ => samples
  candidate := ComplexRaw.ofQComplex (finiteFourierSum root mode samples)
  radius := fun _ => 0
  candidate_stage := by
    intro n
    unfold ComplexRaw.ofQComplex QBox.point QBox.NestedIn
    exact ⟨⟨Rat.le_refl, Rat.le_refl⟩, ⟨Rat.le_refl, Rat.le_refl⟩⟩
  candidate_ordered := by
    intro n
    change (QBox.point (finiteFourierSum root mode samples)).Ordered
    unfold QBox.point QBox.Ordered
    exact ⟨Rat.le_refl, Rat.le_refl⟩
  candidate_shrinks := by
    intro eps
    refine ⟨0, ?_⟩
    intro n hn
    simp [ComplexRaw.ofQComplex, QBox.point, QBox.width, QBox.height]
    constructor <;> grind
  future_containment := by
    intro k n hkn
    change (QBox.point (finiteFourierSum root mode samples)).NestedIn
      (QBox.expand (QBox.point (finiteFourierSum root mode samples)) 0)
    simp [QBox.point, QBox.expand, QBox.NestedIn]
    constructor <;> grind
  radius_shrinks := by
    intro eps
    refine ⟨0, ?_⟩
    intro n hn
    exact Rat.le_of_lt eps.property

theorem finiteSupportFourierSeries_stabilized_equiv
    (root : QComplex) (mode : Nat) (samples : List QComplex) :
    (finiteSupportFourierSeries root mode samples).stabilized.Equiv
      (ComplexRaw.ofQComplex (finiteFourierSum root mode samples)) := by
  let F := finiteSupportFourierSeries root mode samples
  let q : QComplex := finiteFourierSum root mode samples
  intro n
  apply (ComplexRaw.compareAt_overlap_iff
    F.stabilized (ComplexRaw.ofQComplex q) n n).2
  have hcontains := ComplexRaw.cauchyStabilize_contains_current
    (candidate := F.candidate) (radius := F.radius)
    F.future_containment n
  change QBox.Overlaps (F.stabilized.compute n) (QBox.point q)
  change QBox.Overlaps (F.stabilized.compute n)
    (QBox.point (finiteFourierSum root mode samples))
  unfold QBox.Overlaps
  exact ⟨⟨hcontains.1.1, hcontains.1.2⟩,
    ⟨hcontains.2.1, hcontains.2.2⟩⟩

/-! A finite sample table is the first bridge from the project’s complex
function layer to its Fourier layer. Each value is rational-complex, while
the enclosure obligation records that the value is contained in the
function’s own interval computation on its domain. No integral is hidden in
this certificate; it is the exact finite input consumed by a Fourier stage. -/
structure EffectiveFourierSampleCertificate where
  function : FunctionRaw
  samples : List (QComplex × QComplex)
  sample_domain : ∀ p, p ∈ samples -> function.domain p.1
  sample_value : ∀ p (hp : p ∈ samples),
    (QBox.point p.2).NestedIn
      ((function.evalRaw p.1 (sample_domain p hp)).compute 0)

def EffectiveFourierSampleCertificate.values
    (certificate : EffectiveFourierSampleCertificate) : List QComplex :=
  certificate.samples.map Prod.snd

def EffectiveFourierSampleCertificate.toSeries
    (certificate : EffectiveFourierSampleCertificate)
    (root : QComplex) (mode : Nat) : EffectiveFourierSeries :=
  finiteSupportFourierSeries root mode certificate.values

theorem EffectiveFourierSampleCertificate.toSeries_valid
    (certificate : EffectiveFourierSampleCertificate)
    (root : QComplex) (mode : Nat) :
    (certificate.toSeries root mode).stabilized.Valid := by
  exact EffectiveFourierSeries.stabilized_valid
    (certificate.toSeries root mode)

theorem EffectiveFourierSampleCertificate.sample_interval_witness
    (certificate : EffectiveFourierSampleCertificate)
    {p : QComplex × QComplex} (hp : p ∈ certificate.samples) :
    (QBox.point p.2).NestedIn
      ((certificate.function.evalRaw p.1
        (certificate.sample_domain p hp)).compute 0) := by
  exact certificate.sample_value p hp

def constantFunctionSampleCertificate
    (c : QComplex) (points : List QComplex) :
    EffectiveFourierSampleCertificate where
  function := FunctionRaw.exact (fun _ => c)
  samples := points.map (fun z => (z, c))
  sample_domain := by
    intro p hp
    trivial
  sample_value := by
    intro p hp
    rcases List.mem_map.1 hp with ⟨z, hz, rfl⟩
    simp [FunctionRaw.exact, FunctionRaw.evalRaw, QBox.point,
      QBox.NestedIn]

/-! The next concrete instance is an affine complex function.  It is still
entirely finite: at every rational-complex input the function returns an
exact rational-complex value, and the sample certificate records that exact
value as its zero-width enclosure. -/
def affineFunctionSampleCertificate
    (a b : QComplex) (points : List QComplex) :
    EffectiveFourierSampleCertificate where
  function := FunctionRaw.exact (fun z => QComplex.add (QComplex.mul a z) b)
  samples := points.map (fun z => (z, QComplex.add (QComplex.mul a z) b))
  sample_domain := by
    intro p hp
    trivial
  sample_value := by
    intro p hp
    rcases List.mem_map.1 hp with ⟨z, hz, rfl⟩
    simp [FunctionRaw.exact, FunctionRaw.evalRaw, QBox.point,
      QBox.NestedIn]

/-! A coefficient certificate separates the analytic integrand from the
Fourier bookkeeping.  An eventual Fourier instance supplies an integrand such
as `f * phase`; this structure only records the computable complex path
integral and its finite validity certificate. -/
structure EffectiveFourierCoefficientCertificate where
  frequency : Nat
  integrand : ComplexPathIntegral.EntireBoxFunctionRaw
  path : List QComplex
  integralCertificate :
    ComplexPathIntegral.PolygonalIntegralCertificate integrand path

def EffectiveFourierCoefficientCertificate.coefficientRaw
    (certificate : EffectiveFourierCoefficientCertificate) : ComplexRaw :=
  ComplexPathIntegral.polygonalIntegralRawEntire
    certificate.integrand certificate.path

theorem EffectiveFourierCoefficientCertificate.coefficient_valid
    (certificate : EffectiveFourierCoefficientCertificate) :
    certificate.coefficientRaw.Valid := by
  exact ComplexPathIntegral.polygonalIntegralRawEntire_valid
    certificate.integralCertificate

/-! A first genuinely infinite instance: the zero-frequency partial sums of
the geometric coefficient family `1, r, r^2, ...`.  The candidate boxes use
the exact rational prefix and the exact geometric-series upper endpoint.
Their widths shrink by the existing effective geometric-series theorem. -/
def geometricFourierZeroModeSeries
    (r : Rat) (hr0 : 0 <= r) (hrhalf : r <= (1 : Rat) / 2)
    (hr1 : r < 1) : EffectiveFourierSeries where
  root := QComplex.one
  mode := 0
  stage := fun n =>
    [QComplex.ofRat (Series.geometricSum r n)]
  candidate := {
    compute := fun n =>
      { lo := { re := Series.geometricSum r n, im := 0 },
        hi := { re := 1 / (1 - r), im := 0 } }
  }
  radius := fun _ => 0
  candidate_stage := by
    intro n
    dsimp
    change (QBox.point
      (finiteFourierSum QComplex.one 0
        [QComplex.ofRat (Series.geometricSum r n)])).NestedIn _
    simp [finiteFourierSum_singleton, QComplex.natPow,
      QComplex.mul, QComplex.one, QComplex.ofRat,
      QBox.point, QBox.NestedIn]
    constructor
    · exact ⟨by grind [Rat.add_zero], by native_decide⟩
    · exact ⟨by simpa [Rat.add_zero, Rat.sub_eq_add_neg] using
          Series.geometricSum_le_inv_one_sub hr0 hr1 n,
        by native_decide⟩
  candidate_ordered := by
    intro n
    dsimp
    unfold QBox.Ordered
    simp only [QComplex.le_def]
    exact ⟨Series.geometricSum_le_inv_one_sub hr0 hr1 n,
      by native_decide⟩
  candidate_shrinks := by
    dsimp
    intro eps
    obtain ⟨N, hN⟩ :=
      (Series.geometricRaw_valid_of_le_half hr0 hrhalf hr1).2.2 eps
    refine ⟨N, ?_⟩
    intro n hn
    have h := hN n hn
    simp only [QBox.width, QBox.height]
    change 1 / (1 - r) - Series.geometricSum r n <= eps.val /\
      0 - 0 <= eps.val
    exact ⟨h, by grind [Rat.sub_self]⟩
  future_containment := by
    dsimp
    intro k n hkn
    change
      ({ lo := { re := Series.geometricSum r n, im := 0 },
          hi := { re := 1 / (1 - r), im := 0 } } : QBox).NestedIn
        (QBox.expand
          { lo := { re := Series.geometricSum r k, im := 0 },
            hi := { re := 1 / (1 - r), im := 0 } } 0)
    simp [QBox.expand, QBox.NestedIn]
    constructor
    · exact ⟨by simpa [Rat.add_zero, Rat.sub_eq_add_neg] using
        Series.geometricSum_le_of_le hr0 hkn, by grind⟩
    · exact ⟨by grind, by grind⟩
  radius_shrinks := by
    intro eps
    refine ⟨0, ?_⟩
    intro n hn
    exact Rat.le_of_lt eps.property

theorem geometricFourierZeroModeSeries_candidate_contains_limit
    (r : Rat) (hr0 : 0 <= r) (hrhalf : r <= (1 : Rat) / 2)
    (hr1 : r < 1) (n : Nat) :
    (QBox.point ({ re := 1 / (1 - r), im := 0 } : QComplex)).NestedIn
      ((geometricFourierZeroModeSeries r hr0 hrhalf hr1).candidate.compute n) := by
  dsimp [geometricFourierZeroModeSeries]
  simp [QBox.point, QBox.NestedIn, QComplex.le_def]
  exact Series.geometricSum_le_inv_one_sub hr0 hr1 n

theorem geometricFourierZeroModeSeries_stabilized_equiv_limit
    (r : Rat) (hr0 : 0 <= r) (hrhalf : r <= (1 : Rat) / 2)
    (hr1 : r < 1) :
    (geometricFourierZeroModeSeries r hr0 hrhalf hr1).stabilized.Equiv
      (ComplexRaw.ofQComplex { re := 1 / (1 - r), im := 0 }) := by
  let F := geometricFourierZeroModeSeries r hr0 hrhalf hr1
  let q : QComplex := { re := 1 / (1 - r), im := 0 }
  have hexternal : forall k n, k <= n ->
      (QBox.point q).NestedIn
        (QBox.expand (F.candidate.compute k) (F.radius k)) := by
    intro k n hkn
    have hbox := geometricFourierZeroModeSeries_candidate_contains_limit
      r hr0 hrhalf hr1 k
    have hradius : F.radius k = 0 := by
      rfl
    change (QBox.point q).NestedIn
      (QBox.expand (F.candidate.compute k) (F.radius k))
    rw [hradius]
    simpa [F, geometricFourierZeroModeSeries, QBox.expand, q,
      Rat.sub_eq_add_neg, Rat.add_zero, Rat.zero_add] using hbox
  apply ComplexRaw.sameStageOverlap_equiv
  intro n
  have hcontains := ComplexRaw.cauchyStabilize_contains_external
    (candidate := F.candidate) (radius := F.radius)
    (external := fun _ => QBox.point q) hexternal n n (Nat.le_refl n)
  apply (ComplexRaw.compareAt_overlap_iff
    F.stabilized (ComplexRaw.ofQComplex q) n n).2
  change QBox.Overlaps
    (F.stabilized.compute n) (QBox.point q)
  unfold QBox.Overlaps
  exact ⟨⟨hcontains.1.1, hcontains.1.2⟩,
    ⟨hcontains.2.1, hcontains.2.2⟩⟩

/-! A nonzero quarter-turn Fourier instance.  Its candidates are the exact
finite coefficient stages; the stabilization radius is the rational bound
`2 * r^n`.  The factor two is valid for `r <= 1/2`, while the tail proof
itself only uses finite rational inequalities. -/
set_option maxHeartbeats 800000 in
def quarterTurnGeometricFourierSeries
    (r : Rat) (hr0 : 0 <= r) (hrhalf : r <= (1 : Rat) / 2)
    (hr1 : r < 1) : EffectiveFourierSeries where
  root := RotationSeries.imaginaryUnit
  mode := 1
  stage := geometricCoefficientStage r
  candidate := {
    compute := fun n => QBox.point (quarterTurnGeometricStage r n)
  }
  radius := fun n => 2 * r ^ n
  candidate_stage := by
    intro n
    unfold QBox.NestedIn
    exact ⟨⟨Rat.le_refl, Rat.le_refl⟩, ⟨Rat.le_refl, Rat.le_refl⟩⟩
  candidate_ordered := by
    intro n
    unfold QBox.Ordered QBox.point
    exact ⟨Rat.le_refl, Rat.le_refl⟩
  candidate_shrinks := by
    intro eps
    refine ⟨0, ?_⟩
    intro n hn
    change (QBox.point (quarterTurnGeometricStage r n)).width <= eps.val /\
      (QBox.point (quarterTurnGeometricStage r n)).height <= eps.val
    simp only [QBox.point, QBox.width, QBox.height]
    constructor <;> simpa [Rat.sub_self] using (Rat.le_of_lt eps.property)
  future_containment := by
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
      quarterTurnGeometricStage_block_coord_abs_le_inv_one_sub
        hr0 hr1 k d
    have hpow : 0 <= r ^ k := Rat.pow_nonneg hr0
    have hscaled : r ^ k * (1 / (1 - r)) <= 2 * r ^ k := by
      simpa [Rat.mul_comm] using
        (Rat.mul_le_mul_of_nonneg_left hfactor hpow)
    change (QBox.point (quarterTurnGeometricStage r (k + d))).NestedIn
      (QBox.expand (QBox.point (quarterTurnGeometricStage r k)) (2 * r ^ k))
    unfold QBox.NestedIn QBox.expand QBox.point
    simp only [QComplex.le_def]
    constructor
    · constructor
      · have h := htail.1
        have hlow : -(2 * r ^ k) <=
            (quarterTurnGeometricStage r (k + d)).re -
              (quarterTurnGeometricStage r k).re :=
          Rat.le_trans (Rat.neg_le_neg hscaled)
            (Rat.le_trans (Rat.neg_le_neg h)
              (neg_qabs_le_self
                ((quarterTurnGeometricStage r (k + d)).re -
                (quarterTurnGeometricStage r k).re)))
        grind [Rat.sub_eq_add_neg]
      · have h := htail.2
        have hlow : -(2 * r ^ k) <=
            (quarterTurnGeometricStage r (k + d)).im -
              (quarterTurnGeometricStage r k).im :=
          Rat.le_trans (Rat.neg_le_neg hscaled)
            (Rat.le_trans (Rat.neg_le_neg h)
              (neg_qabs_le_self
                ((quarterTurnGeometricStage r (k + d)).im -
                  (quarterTurnGeometricStage r k).im)))
        grind [Rat.sub_eq_add_neg]
    · constructor
      · have h := htail.1
        have hupp :
            (quarterTurnGeometricStage r (k + d)).re -
              (quarterTurnGeometricStage r k).re <= 2 * r ^ k :=
          Rat.le_trans
            (self_le_qabs
              ((quarterTurnGeometricStage r (k + d)).re -
                (quarterTurnGeometricStage r k).re))
            (Rat.le_trans h hscaled)
        grind [Rat.sub_eq_add_neg]
      · have h := htail.2
        have hupp :
            (quarterTurnGeometricStage r (k + d)).im -
              (quarterTurnGeometricStage r k).im <= 2 * r ^ k :=
          Rat.le_trans
            (self_le_qabs
              ((quarterTurnGeometricStage r (k + d)).im -
                (quarterTurnGeometricStage r k).im))
            (Rat.le_trans h hscaled)
        grind [Rat.sub_eq_add_neg]
  radius_shrinks := by
    have hbound : forall n : Nat,
        2 * r ^ n <= (2 : Rat) / (((n + 1 : Nat) : Rat)) := by
      intro n
      have hpow := Series.pow_le_half_pow hr0 hrhalf n
      have hhalf := Series.half_pow_le_one_div_succ n
      have hle := Rat.le_trans hpow hhalf
      exact Rat.le_trans
        (Rat.mul_le_mul_of_nonneg_left hle (by native_decide)) (by
          rw [Rat.div_def]
          grind [Rat.mul_assoc, Rat.mul_comm])
    exact shrinksToZero_of_natOverSuccBound hbound

theorem quarterTurnGeometricFourierSeries_future_stage_enclosure
    (r : Rat) (hr0 : 0 <= r) (hrhalf : r <= (1 : Rat) / 2)
    (hr1 : r < 1) (k n : Nat) (hkn : k <= n) :
    (QBox.point (quarterTurnGeometricStage r n)).NestedIn
      (QBox.expand (QBox.point (quarterTurnGeometricStage r k))
        (2 * r ^ k)) := by
  exact (quarterTurnGeometricFourierSeries r hr0 hrhalf hr1).future_containment
    k n hkn

end ComputableAnalysis
