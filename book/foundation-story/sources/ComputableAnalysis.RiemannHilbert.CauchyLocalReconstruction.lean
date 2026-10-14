import ComputableAnalysis.RiemannHilbert.CauchyFixedSeries
import ComputableAnalysis.RiemannHilbert.RationalDensity
import ComputableAnalysis.RiemannHilbert.DomainHolomorphicValueLaws

/-! A certified Cauchy representation on rational points and pointwise
continuity reconstruct the actual represented function on a smaller open
disk. Its holomorphic witness and uniform error estimates are consequences,
not fields of the Cauchy certificate. -/
namespace ComputableAnalysis.RiemannHilbert.CauchyLocalReconstruction
open ComplexRaw FunctionTheory LocalODE DomainFunctions CauchyTaylor
set_option autoImplicit false
variable {F : QComplex → ComplexRaw} (c : SeriesCertificate F)
    (R : Rat) (hR : 0 ≤ R) (hl : 8*R ≤ (1 : Rat)/2)

def series : DomainFunctions.Map := ofCertified
  (BoundedSeries.seriesMap c.coefficient c.moments.coefficient_valid
    (2*c.cauchy.massBound) 1 R (Rat.mul_nonneg (by decide) c.cauchy.mass_nonneg)
    (by decide) hR (CauchyMoments.certificate_bound c) (by simpa only [Rat.mul_one] using hl))

def seriesHolomorphic : Holomorphic (series c R hR hl) := ofCertifiedHolomorphic
  (BoundedSeries.seriesMap_holomorphic c.coefficient c.moments.coefficient_valid
    (2*c.cauchy.massBound) 1 R (Rat.mul_nonneg (by decide) c.cauchy.mass_nonneg)
    (by decide) hR (CauchyMoments.certificate_bound c) (by simpa only [Rat.mul_one] using hl))

def openData : ScalarTopology.OpenData (interior R) :=
  ⟨(series c R hR hl).domain_congr,(seriesHolomorphic c R hR hl).openDomain.radius,
    (seriesHolomorphic c R hR hl).openDomain.inside⟩

theorem represented_agreement (f : DomainFunctions.Map)
    (hf : ContinuousOn f.domain f.eval) (hi : ∀ z, interior R z → f.domain z)
    (ha : ∀ (q : QComplex) (hq : interior R (ScalarTopology.rationalScalar q)),
      (f.eval (ScalarTopology.rationalScalar q) (hi _ hq)).val.Equiv (F q))
    (z : Scalar) (hz : interior R z) :
    f.eval z (hi z hz) ≈ (series c R hR hl).eval z hz := by
  let g := series c R hR hl
  have hg : ContinuousOn (interior R) g.eval := (seriesHolomorphic c R hR hl).continuous
  have hrat : ∀ (q : QComplex) (hq : interior R (ScalarTopology.rationalScalar q)),
      f.eval (ScalarTopology.rationalScalar q) (hi _ hq) ≈ g.eval (ScalarTopology.rationalScalar q) hq := by
    intro q hq
    let a := ScalarTopology.rationalScalar q
    have hsmall := interior_bound R a hq
    have hdisk := CauchyFixedSeries.rational_disk q R hR hsmall
    have hrad : 0 ≤ 2*R := by grind only
    have hrad1 : 2*R < 1 := by grind only
    have hvalid := c.cauchy.valid q (2*R) hrad hrad1 hdisk
    have hs := CauchyFixedSeries.rational_agreement c q R hR hl hsmall
    exact equiv_trans (f.eval a (hi a hq)).property hvalid (g.eval a hq).property (ha q hq) hs
  exact RationalDensity.continuous_agreement (openData c R hR hl)
    (fun z hz => f.eval z (hi z hz)) g.eval (restrictContinuous f.eval hf hi) hg hrat z hz

def function (f : DomainFunctions.Map) (hi : ∀ z, interior R z → f.domain z) : DomainFunctions.Map :=
  onDomain f (openData c R hR hl).invariant hi

def holomorphic (f : DomainFunctions.Map) (hf : ContinuousOn f.domain f.eval)
    (hi : ∀ z, interior R z → f.domain z)
    (ha : ∀ (q : QComplex) (hq : interior R (ScalarTopology.rationalScalar q)),
      (f.eval (ScalarTopology.rationalScalar q) (hi _ hq)).val.Equiv (F q)) :
    Holomorphic (function c R hR hl f hi) :=
  (seriesHolomorphic c R hR hl).transfer (function c R hR hl f hi) (fun _ hz => hz)
    ⟨(openData c R hR hl).radius,(openData c R hR hl).inside⟩
    (fun z hz => equiv_symm (represented_agreement c R hR hl f hf hi ha z hz))

theorem actual_derivative (f : DomainFunctions.Map) (hf : ContinuousOn f.domain f.eval)
    (hi : ∀ z, interior R z → f.domain z)
    (ha : ∀ (q : QComplex) (hq : interior R (ScalarTopology.rationalScalar q)),
      (f.eval (ScalarTopology.rationalScalar q) (hi _ hq)).val.Equiv (F q))
    (z : Scalar) (hz : interior R z) :
    ((holomorphic c R hR hl f hf hi ha).derivative z hz).val.Equiv
      (BoundedSeries.sumDerivative c.coefficient z.val c.moments.coefficient_valid z.property
        (2*c.cauchy.massBound) 1 R) :=
  equiv_refl _ ((holomorphic c R hR hl f hf hi ha).derivative z hz).property

include hR hl in
theorem value_bound (f : DomainFunctions.Map) (hf : ContinuousOn f.domain f.eval)
    (hi : ∀ z, interior R z → f.domain z)
    (ha : ∀ (q : QComplex) (hq : interior R (ScalarTopology.rationalScalar q)),
      (f.eval (ScalarTopology.rationalScalar q) (hi _ hq)).val.Equiv (F q))
    (z : Scalar) (hz : interior R z) : Small (f.eval z (hi z hz)).val (8*c.cauchy.massBound) := by
  have hs := coefficientSum_bound c.coefficient z.val c.moments.coefficient_valid z.property
    (2*c.cauchy.massBound) 1 R (Rat.mul_nonneg (by decide) c.cauchy.mass_nonneg)
    (by decide) hR (CauchyMoments.certificate_bound c) (interior_bound R _ hz) (by grind only)
  have he := represented_agreement c R hR hl f hf hi ha z hz
  exact (Small.congr ((series c R hR hl).eval z hz).property (f.eval z (hi z hz)).property
    (equiv_symm he) hs).mono (by grind only)

theorem uniform_remainder (f : DomainFunctions.Map) (hf : ContinuousOn f.domain f.eval)
    (hi : ∀ z, interior R z → f.domain z)
    (ha : ∀ (q : QComplex) (hq : interior R (ScalarTopology.rationalScalar q)),
      (f.eval (ScalarTopology.rationalScalar q) (hi _ hq)).val.Equiv (F q))
    (eps H : QPos) (w z : Scalar) (hw : interior R w) (hz : interior R z)
    (hH : H.val ≤ (derivativeDelta (2*c.cauchy.massBound) 1
      (Rat.mul_nonneg (by decide) c.cauchy.mass_nonneg) (by decide) eps).val)
    (hzw : Small (sub z.val w.val) H.val) :
    Small (remainder (function c R hR hl f hi) w hw
      ((holomorphic c R hR hl f hf hi ha).derivative w hw) z hz) (eps.val*H.val) :=
  ((holomorphic c R hR hl f hf hi ha).atPoint w hw).estimate eps H z hz hH hzw

end ComputableAnalysis.RiemannHilbert.CauchyLocalReconstruction
