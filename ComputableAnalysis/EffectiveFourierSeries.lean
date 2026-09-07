import ComputableAnalysis.FiniteFourierFoundation
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

theorem EffectiveFourierSeries.candidate_equiv_stabilized
    (F : EffectiveFourierSeries) :
    F.candidate.Equiv F.stabilized := by
  exact ComplexRaw.candidate_equiv_cauchyStabilize_of_future
    F.candidate_ordered F.future_containment

theorem EffectiveFourierSeries.stabilized_width_le_of_candidate
    (F : EffectiveFourierSeries) (n : Nat) :
    (F.stabilized.compute n).width <=
      (F.candidate.compute n).width + 2 * F.radius n := by
  exact ComplexRaw.cauchyStabilize_width_le_current_expand n

theorem EffectiveFourierSeries.stabilized_height_le_of_candidate
    (F : EffectiveFourierSeries) (n : Nat) :
    (F.stabilized.compute n).height <=
      (F.candidate.compute n).height + 2 * F.radius n := by
  exact ComplexRaw.cauchyStabilize_height_le_current_expand n

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
zero.  This is the base sanity-check instance; genuinely infinite
coefficient tails belong in `EffectiveFourierTail`. -/
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

end ComputableAnalysis
