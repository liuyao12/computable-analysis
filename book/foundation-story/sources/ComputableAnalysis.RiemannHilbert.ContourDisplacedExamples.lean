import ComputableAnalysis.RiemannHilbert.ContourDisplacedInvariance
import ComputableAnalysis.RiemannHilbert.CauchyGeometricExample

/-! Actual affine and nonpolynomial clients, plus an asymmetric interval name
whose finite rational centers differ from its exact rational value. -/
namespace ComputableAnalysis.RiemannHilbert.RectangularContour.DisplacedExamples
open ComplexRaw FunctionTheory DomainFunctions LocalODE
set_option autoImplicit false

def affineContour (a b c : Scalar) : Nat → Scalar :=
  normalizedDisplacedLocalCauchyContour (DomainFunctions.affine a b) (DomainFunctions.affine_holomorphic a b) c trivial

theorem affineContour_converges (a b c : Scalar) :
    Converges (affineContour a b c) (scalarSum a (scalarProduct b c)) :=
  normalizedDisplacedLocalCauchyContour_converges _ (DomainFunctions.affine_holomorphic a b) c trivial

theorem affineContour_limit_identity (a b c u : Scalar)
    (hu : Converges (affineContour a b c) u) : u≈scalarSum a (scalarProduct b c) :=
  normalizedDisplacedLocalCauchyContour_limit_identity _ (DomainFunctions.affine_holomorphic a b) c trivial u hu

def geometricContour (a : Scalar) (ha : interior CauchyGeometricExample.radius a) : Nat → Scalar :=
  normalizedDisplacedLocalCauchyContour CauchyGeometricExample.analyticFunction
    CauchyGeometricExample.analyticHolomorphic a (CauchyGeometricExample.included a ha)

theorem geometricContour_converges (a : Scalar) (ha : interior CauchyGeometricExample.radius a) :
    Converges (geometricContour a ha)
      (RepresentedReciprocal.inverse (CauchyGeometricExample.denominator a)
        (CauchyGeometricExample.denominator_nonzero a ha)) :=
  normalizedDisplacedLocalCauchyContour_converges _ CauchyGeometricExample.analyticHolomorphic a
    (CauchyGeometricExample.included a ha)

theorem geometricContour_limit_identity (a : Scalar) (ha : interior CauchyGeometricExample.radius a)
    (u : Scalar) (hu : Converges (geometricContour a ha) u) :
    u≈RepresentedReciprocal.inverse (CauchyGeometricExample.denominator a)
      (CauchyGeometricExample.denominator_nonzero a ha) :=
  normalizedDisplacedLocalCauchyContour_limit_identity _ CauchyGeometricExample.analyticHolomorphic a
    (CauchyGeometricExample.included a ha) u hu

def asymmetricRaw (q : QComplex) : ComplexRaw where
  compute n := ⟨q,⟨q.re+((1:Rat)/2)^n,q.im+((1:Rat)/2)^n⟩⟩

theorem asymmetricRaw_valid (q : QComplex) : (asymmetricRaw q).Valid := by
  refine ⟨?_,?_,?_⟩
  · intro n
    have hp : 0≤((1:Rat)/2)^n := Rat.pow_nonneg (by decide +kernel)
    change 0≤(q.re+((1:Rat)/2)^n)-q.re ∧ 0≤(q.im+((1:Rat)/2)^n)-q.im
    constructor <;> grind only
  · intro n m hnm
    obtain ⟨t,rfl⟩ := Nat.exists_eq_add_of_le hnm
    have hp : 0≤((1:Rat)/2)^n := Rat.pow_nonneg (by decide +kernel)
    have h := Rat.mul_le_mul_of_nonneg_left (half_power_le_one t) hp
    change q.re≤q.re ∧ q.re+((1:Rat)/2)^(n+t)≤q.re+((1:Rat)/2)^n ∧
      q.im≤q.im ∧ q.im+((1:Rat)/2)^(n+t)≤q.im+((1:Rat)/2)^n
    rw [rational_pow_add]
    constructor
    · exact Rat.le_refl
    · constructor
      · grind only
      · exact ⟨Rat.le_refl,by grind only⟩
  · intro eps
    refine ⟨RationalMajorant.natRateStage 1 eps, ?_⟩
    intro n hn
    have h := contour_half_rate 1 (by decide +kernel) eps n hn
    change (q.re+((1:Rat)/2)^n)-q.re≤eps.val ∧ (q.im+((1:Rat)/2)^n)-q.im≤eps.val
    constructor <;> grind only

def asymmetricName (q : QComplex) : Scalar := ⟨asymmetricRaw q,asymmetricRaw_valid q⟩

theorem asymmetricName_agreement (q : QComplex) : asymmetricName q≈rationalRectangleScalar q := by
  intro n
  apply (compareAt_overlap_iff (asymmetricRaw q) (ofQComplex q) n n).2
  have hp : 0≤((1:Rat)/2)^n := Rat.pow_nonneg (by decide +kernel)
  change (q.re≤q.re ∧ q.im≤q.im) ∧
    (q.re≤q.re+((1:Rat)/2)^n ∧ q.im≤q.im+((1:Rat)/2)^n)
  constructor <;> constructor <;> grind only

end ComputableAnalysis.RiemannHilbert.RectangularContour.DisplacedExamples
