import ComputableAnalysis.RiemannHilbert.BoundaryCauchyInteriorReconstruction
import ComputableAnalysis.RiemannHilbert.HolomorphicBoundaryDataExistence

/-! Genuine holomorphicity of supplied bounded represented limits.
Actual Cauchy moment computations construct the local derivative series;
finite errors prove its agreement with the supplied limit. Numerical bound
selection stays only inside the Prop existence proof. -/
namespace ComputableAnalysis.RiemannHilbert.BoundedHolomorphicSequenceLimit
open ComplexRaw FunctionTheory DomainFunctions RectangularContour BoundaryCauchyPowers
set_option autoImplicit false

/-- A represented shrinking limit of genuinely holomorphic prefixes is
holomorphic. Only validity, actual source bounds and quantitative convergence
are supplied; no derivative, Cauchy identity or holomorphic limit is assumed. -/
theorem exists_holomorphic (f : DomainFunctions.Map) (g : Nat → DomainFunctions.Map)
    (hD : ∀ K, (g K).domain=f.domain) (hg : ∀ K, Holomorphic (g K))
    (B : QPos) (hB : ∀ K z hz, Small ((g K).eval z hz).val B.val)
    (r e : Nat → Rat) (hr : ShrinksToZero r) (he : ShrinksToZero e)
    (hr0 : ∀ K, 0≤r K)
    (hfuture : ∀ K L, K≤L → ∀ z hL hK,
      Small (sub ((g L).eval z hL).val ((g K).eval z hK).val) (r K))
    (hclose : ∀ K z hf hg, Small (sub (f.eval z hf).val ((g K).eval z hg).val) (e K)) :
    Nonempty (Holomorphic f) := by
  classical
  have localWitnesses : ∀ a (ha : f.domain a), ∃ q : DomainFunctions.Map,
      Nonempty (Holomorphic q) ∧ q.domain a ∧
      (∀ z, q.domain z → f.domain z) ∧
      (∀ z hz hf, q.eval z hz≈f.eval z hf) := by
    intro a ha
    let ha0 : (g 0).domain a := (hD 0).symm ▸ ha
    let J := effectiveLocalRectangle (g 0) (hg 0) a ha0
    have hp : RectanglePoleInterior J a := effectiveLocalRectangle_pole_inside (g 0) (hg 0) a ha0
    have hord := rectanglePoleInterior_ordered J a hp
    have inside : ∀ K z, representedRectangleContains J z → (g K).domain z := by
      intro K z hz
      exact (hD K).symm ▸ ((hD 0) ▸ (effectiveLocalRectangle_domain (g 0) (hg 0) a ha0 z hz))
    let hd := fun K => rectangleBoundaryDomains_of_rectangle (g K) J hord.1 hord.2 (inside K)
    have hder : ∀ K, ∃ D : QPos, RectangleBoundaryDerivativeBound (g K) (hg K) J (hd K) D :=
      fun K => HolomorphicBoundaryDataExistence.derivative_bound_exists (g K) (hg K) J hord.1 hord.2 (hd K)
    let D : Nat → QPos := fun K => (hder K).choose
    have hderBound : ∀ K, RectangleBoundaryDerivativeBound (g K) (hg K) J (hd K) (D K) :=
      fun K => (hder K).choose_spec
    let rd := RectangularPoleReciprocal.boundaryDomains true J a hp hord.1 hord.2
    let U := RectangularPoleReciprocal.bound true J a hp
    let hu := RectangularPoleReciprocal.boundary_bound true J a hp hord.1 hord.2 rd
    let data : Nat → Data := fun K => {
      source := g K, holomorphic := hg K, rectangle := J, xOrder := hord.1, yOrder := hord.2,
      center := a, sourceDomains := hd K, reciprocalDomains := rd,
      valueBound := B, derivativeBound := D K, reciprocalBound := U,
      values := ⟨fun z hz => hB K z ((hd K).bottom z hz),fun z hz => hB K z ((hd K).top z hz),
        fun z hz => hB K z ((hd K).left z hz),fun z hz => hB K z ((hd K).right z hz)⟩,
      derivatives := hderBound K, reciprocals := hu }
    have hj : ∀ K, (data K).rectangle=(data 0).rectangle := fun _ => rfl
    have hc : ∀ K, (data K).center≈(data 0).center := fun _ => Setoid.refl a
    have hU : ∀ K, (data K).reciprocalBound=(data 0).reciprocalBound := fun _ => rfl
    have hV : ∀ K, (data K).valueBound=(data 0).valueBound := fun _ => rfl
    have hs : ∀ K L, K≤L → ∀ q, rationalRectangleBoundaryContains (data 0).rectangle q →
        ∀ hL hK, Small (sub ((data L).source.eval (rationalRectangleScalar q) hL).val
          ((data K).source.eval (rationalRectangleScalar q) hK).val) (r K) :=
      fun K L hKL _q _hq hL hK => hfuture K L hKL _ hL hK
    let F := BoundaryCauchySequenceLimits.function data hj hc hU hV r hr hr0 hs
    let H := BoundaryCauchySequenceLimits.holomorphic data hj hc hU hV r hr hr0 hs
    let O := (ScalarTopology.ofDomain F H.openDomain).inter (RectangularPoleSearch.openData true J)
    let q := onDomain F O.invariant (fun _ hz => hz.1)
    let Hq := H.onDomain O (fun _ hz => hz.1)
    have includeQ : ∀ z, q.domain z → f.domain z :=
      fun z hz => (hD 0) ▸ (inside 0 z (rectanglePoleInterior_mem J z hz.2))
    refine ⟨q,⟨Hq⟩,⟨Centered.center_mem a _,hp⟩,includeQ,?_⟩
    intro z hz hf
    apply SeriesLimitLaws.equiv_of_small_sub_zero
    let C := BoundaryCauchySequenceLimits.constant data
    have hC := BoundaryCauchySequenceLimits.constant_nonneg data
    have hshrinks := RepresentedCauchySum.sum_shrinks _ _
      (SeriesLimitLaws.shrinks_scale r hr (4*C) (Rat.mul_nonneg (by decide +kernel) hC)) he
    apply SeriesLimitLaws.small_closed _ 0 (fun K => 4*C*r K+e K) hshrinks
    intro K
    let hzK := BoundaryCauchySequenceAgreement.prefix_domain data hc hU K z hz.1
    let gmem := inside K z (rectanglePoleInterior_mem J z hz.2)
    have hproj := BoundaryCauchyInteriorReconstruction.projection (data K) (inside K) z hzK hz.2
    have hleft := Small.congr
      (sub_valid (F.eval z hz.1).property ((BoundaryCauchySeries.function (data K)).eval z hzK).property)
      (sub_valid (F.eval z hz.1).property ((g K).eval z gmem).property)
      (FunctionTheory.sub_congr (equiv_refl _ (F.eval z hz.1).property) hproj)
      (BoundaryCauchySequenceAgreement.projection_close data hj hc hU hV r hr hr0 hs K z hz.1)
    have hright := RepresentedCauchySum.small_sub_symm _ _ _ (hclose K z hf gmem)
    have hb := LocalODE.small_add hleft hright
    have heq := representedDifference_split (F.eval z hz.1) ((g K).eval z gmem) (f.eval z hf)
    exact (Small.congr (add_valid (sub_valid (F.eval z hz.1).property ((g K).eval z gmem).property)
      (sub_valid ((g K).eval z gmem).property (f.eval z hf).property))
      (sub_valid (q.eval z hz).property (f.eval z hf).property) heq hb).mono (by change 4*C*r K+e K≤0+(4*C*r K+e K); grind only)
  let q := fun a ha => (localWitnesses a ha).choose
  let cert := fun a ha => (localWitnesses a ha).choose_spec
  let H := fun a ha => Classical.choice (cert a ha).1
  let mem := fun a ha => (cert a ha).2.1
  let inside := fun a ha => (cert a ha).2.2.1
  let agree := fun a ha => (cert a ha).2.2.2
  exact ⟨holomorphic_of_local f q H mem inside (fun a ha z hz => agree a ha z hz (inside a ha z hz))⟩

end ComputableAnalysis.RiemannHilbert.BoundedHolomorphicSequenceLimit
