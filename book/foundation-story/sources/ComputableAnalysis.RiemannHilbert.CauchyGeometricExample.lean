import ComputableAnalysis.RiemannHilbert.FixedCauchyRules
import ComputableAnalysis.RiemannHilbert.ReciprocalHolomorphic
import ComputableAnalysis.RiemannHilbert.DomainAffineFunction

/-! A complete represented-input instance: the independently constructed
reciprocal of one minus the input equals its fixed Cauchy-moment series and
the geometric series. Its Cauchy data use one literal finite rule. -/
namespace ComputableAnalysis.RiemannHilbert.CauchyGeometricExample
open ComplexRaw FunctionTheory LocalODE DomainFunctions CauchyTaylor
set_option autoImplicit false

def radius : Rat := 1/32

def denominator (z : Scalar) : Scalar := ⟨sub one z.val,sub_valid (ofQComplex_valid _) z.property⟩

def denominatorMap : DomainFunctions.Map where
  domain _ := True
  eval z _ := denominator z
  domain_congr _ _ _ := Iff.rfl
  eval_congr _ _ _ _ he := FunctionTheory.sub_congr (equiv_refl _ (ofQComplex_valid _)) he

theorem denominator_affine (z : Scalar) :
    (DomainFunctions.affine oneScalar (scalarNeg oneScalar)).eval z trivial ≈ denominator z := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := ((DomainFunctions.affine oneScalar (scalarNeg oneScalar)).eval z trivial).property)
    (hright := (denominator z).property)
  let Z := ComplexRawQuotient.ofRaw z.val z.property
  change 1+(-1)*Z=1-Z
  grind

def denominatorHolomorphic : Holomorphic denominatorMap :=
  (DomainFunctions.affine_holomorphic oneScalar (scalarNeg oneScalar)).transfer denominatorMap
    (fun _ _ => trivial) ⟨fun _ _ => unitError,fun _ _ _ _ => trivial⟩
    (fun z _ => denominator_affine z)

theorem denominator_nonzero (z : Scalar) (hz : interior radius z) :
    NonzeroBoxSearch.Nonzero (denominator z) := by
  intro he
  have heq := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := (denominator z).property) (hright := ofQComplex_valid _) he
  have hone : z.val.Equiv one := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq (hleft := z.property) (hright := ofQComplex_valid _)
    let Z := ComplexRawQuotient.ofRaw z.val z.property
    change 1-Z=0 at heq
    change Z=1
    grind
  have hs := Small.congr z.property (ofQComplex_valid _) hone (interior_bound radius z hz)
  have h := hs.2.1 0 0
  change (1 : Rat) ≤ 1/32 at h
  exact (by decide +kernel : ¬(1 : Rat) ≤ 1/32) h

def analyticFunction : DomainFunctions.Map := compose ReciprocalHolomorphic.function denominatorMap

def analyticHolomorphic : Holomorphic analyticFunction :=
  ReciprocalHolomorphic.holomorphic.compose denominatorHolomorphic

theorem included (z : Scalar) (hz : interior radius z) : analyticFunction.domain z :=
  ⟨trivial,denominator_nonzero z hz⟩

theorem rational_agreement (q : QComplex) (hq : interior radius (ScalarTopology.rationalScalar q)) :
    (analyticFunction.eval (ScalarTopology.rationalScalar q) (included _ hq)).val.Equiv
      (ofQComplex (cauchySample FixedCauchyRules.reciprocalRule q)) := by
  let z := ScalarTopology.rationalScalar q
  have hs := interior_bound radius z hq
  have hdisk := CauchyFixedSeries.rational_disk q radius (by decide +kernel) hs
  have hnorm := denominator_ne_zero (r := 2*radius) (by decide +kernel) (by decide +kernel) hdisk
  let a := QComplex.sub QComplex.one q
  have hprod := RationalReciprocal.raw_mul_constants a (QComplex.inverse a)
  rw [QComplex.mul_inverse_of_normSq_ne_zero a hnorm] at hprod
  have hden : (denominator z).val.Equiv (ofQComplex a) := equiv_refl _ (denominator z).property
  have hp := equiv_trans (mul_valid (denominator z).property (ofQComplex_valid _))
    (mul_valid (ofQComplex_valid _) (ofQComplex_valid _)) (ofQComplex_valid _)
    (mul_equiv (denominator z).property (ofQComplex_valid _) (ofQComplex_valid _) (ofQComplex_valid _)
      hden (equiv_refl _ (ofQComplex_valid _))) hprod
  have he := RepresentedReciprocal.inverse_unique (denominator z) (denominator_nonzero z hq)
    ⟨ofQComplex (QComplex.inverse a),ofQComplex_valid _⟩ hp
  rw [FixedCauchyRules.reciprocal_sample]
  exact he

def certificate : SeriesCertificate (fun q => ofQComplex (cauchySample FixedCauchyRules.reciprocalRule q)) :=
  FixedCauchyRules.certificate FixedCauchyRules.reciprocalRule

def function : DomainFunctions.Map :=
  CauchyLocalReconstruction.function certificate radius (by decide +kernel) (by decide +kernel)
    analyticFunction included

def holomorphic : Holomorphic function :=
  CauchyLocalReconstruction.holomorphic certificate radius (by decide +kernel) (by decide +kernel)
    analyticFunction analyticHolomorphic.continuous included rational_agreement

theorem fixed_moment_identity (z : Scalar) (hz : interior radius z) :
    function.eval z hz ≈
      (CauchyLocalReconstruction.series certificate radius (by decide +kernel) (by decide +kernel)).eval z hz :=
  CauchyLocalReconstruction.represented_agreement certificate radius (by decide +kernel) (by decide +kernel)
    analyticFunction analyticHolomorphic.continuous included rational_agreement z hz

theorem coefficient_one (k : Nat) : (certificate.coefficient k).Equiv one := by
  have he := FixedCauchyRules.coefficient_agreement FixedCauchyRules.reciprocalRule k
  rw [FixedCauchyRules.reciprocal_coefficient] at he
  exact he

theorem one_bound (k : Nat) : Small one (1*(1 : Rat)^k) := by
  rw [CauchyMoments.one_power,Rat.mul_one]
  exact ⟨fun _ _ => by change (-1 : Rat) ≤ 1; decide,
    fun _ _ => by change (1 : Rat) ≤ 1; decide,
    fun _ _ => by change (-1 : Rat) ≤ 0; decide,
    fun _ _ => by change (0 : Rat) ≤ 1; decide⟩

theorem geometric_identity (z : Scalar) (hz : interior radius z) :
    (function.eval z hz).val.Equiv
      (BoundedSeries.sumValue (fun _ => one) z.val (fun _ => ofQComplex_valid _) z.property 1 1 radius) := by
  have he := fixed_moment_identity z hz
  have hs := coefficientSum_congr_of_bounds certificate.coefficient (fun _ => one) z.val z.val
    certificate.moments.coefficient_valid (fun _ => ofQComplex_valid _) z.property z.property
    coefficient_one (equiv_refl _ z.property) (2*certificate.cauchy.massBound) 1 radius 1 1 radius
    (Rat.mul_nonneg (by decide) certificate.cauchy.mass_nonneg) (by decide) (by decide +kernel)
    (by decide) (by decide) (by decide +kernel) (CauchyMoments.certificate_bound certificate) one_bound
    (interior_bound radius z hz) (interior_bound radius z hz) (by decide +kernel) (by decide +kernel)
  exact equiv_trans (function.eval z hz).property
    ((CauchyLocalReconstruction.series certificate radius (by decide +kernel) (by decide +kernel)).eval z hz).property
    (BoundedSeries.sumValue_valid (fun _ => one) z.val (fun _ => ofQComplex_valid _) z.property 1 1 radius
      (by decide) (by decide) (by decide +kernel) one_bound (interior_bound radius z hz) (by decide +kernel)) he hs

end ComputableAnalysis.RiemannHilbert.CauchyGeometricExample
