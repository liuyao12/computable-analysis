import ComputableAnalysis.RiemannHilbert.ContourDisplacedCauchy
import ComputableAnalysis.RiemannHilbert.ContourNormalizedCauchy

/-! The independent geometric-period inverse normalizes the actual displaced
rational-square quadrature. Error schedules and exact limit agreement are proved. -/
namespace ComputableAnalysis.RiemannHilbert.RectangularContour
open ComplexRaw FunctionTheory DomainFunctions
set_option autoImplicit false

def normalizedDisplacedLocalCauchyContour (f : DomainFunctions.Map) (hf : Holomorphic f)
    (a : Scalar) (ha : f.domain a) (n : Nat) : Scalar :=
  scalarProduct inverseGeometricPeriod (displacedLocalCauchyContour f hf a ha n)

theorem normalizedDisplacedLocalCauchyContour_converges (f : DomainFunctions.Map) (hf : Holomorphic f)
    (a : Scalar) (ha : f.domain a) :
    Converges (normalizedDisplacedLocalCauchyContour f hf a ha) (f.eval a ha) :=
  converge_limit_congr _ _ _
    (converge_product_left inverseGeometricPeriod _ _ (displacedLocalCauchyContour_converges f hf a ha))
    (normalizedCauchyValue f a ha)

theorem normalizedDisplacedLocalCauchyContour_limit_identity (f : DomainFunctions.Map) (hf : Holomorphic f)
    (a : Scalar) (ha : f.domain a) (u : Scalar)
    (hu : Converges (normalizedDisplacedLocalCauchyContour f hf a ha) u) : u ≈ f.eval a ha :=
  converge_unique _ _ _ hu (normalizedDisplacedLocalCauchyContour_converges f hf a ha)

theorem normalizedDisplacedLocalCauchy_center_limits_agree (f : DomainFunctions.Map) (hf hg : Holomorphic f)
    (a b : Scalar) (ha : f.domain a) (hb : f.domain b) (he : a ≈ b) (u v : Scalar)
    (hu : Converges (normalizedDisplacedLocalCauchyContour f hf a ha) u)
    (hv : Converges (normalizedDisplacedLocalCauchyContour f hg b hb) v) : u ≈ v :=
  Setoid.trans (normalizedDisplacedLocalCauchyContour_limit_identity f hf a ha u hu)
    (Setoid.trans (f.eval_congr a b ha hb he)
      (Setoid.symm (normalizedDisplacedLocalCauchyContour_limit_identity f hg b hb v hv)))

def normalizedDisplacedLocalCauchyStage (f : DomainFunctions.Map) (hf : Holomorphic f)
    (a : Scalar) (ha : f.domain a) (eps : QPos) : Nat :=
  displacedLocalCauchyStage f hf a ha (divideRadius eps
    ⟨2*scalarBound inverseGeometricPeriod,
      Rat.mul_pos (by decide +kernel) (scalarBound_pos inverseGeometricPeriod)⟩)

theorem normalizedDisplacedLocalCauchyStage_spec (f : DomainFunctions.Map) (hf : Holomorphic f)
    (a : Scalar) (ha : f.domain a) (eps : QPos) (n : Nat)
    (hn : normalizedDisplacedLocalCauchyStage f hf a ha eps≤n) :
    Small (sub (normalizedDisplacedLocalCauchyContour f hf a ha n).val (f.eval a ha).val) eps.val := by
  let C : QPos := ⟨2*scalarBound inverseGeometricPeriod,
    Rat.mul_pos (by decide +kernel) (scalarBound_pos inverseGeometricPeriod)⟩
  let eta := divideRadius eps C
  have hc := displacedLocalCauchyStage_spec f hf a ha eta n hn
  have hb := Small.mul inverseGeometricPeriod.property
    (sub_valid (displacedLocalCauchyContour f hf a ha n).property (localCauchyValue f a ha).property)
    (Rat.le_of_lt (scalarBound_pos inverseGeometricPeriod)) (Rat.le_of_lt eta.property)
    (scalar_small inverseGeometricPeriod) hc
  have he : 2*scalarBound inverseGeometricPeriod*eta.val=eps.val := divideRadius_identity eps C
  rw [he] at hb
  have hs := Small.congr
    (mul_valid inverseGeometricPeriod.property
      (sub_valid (displacedLocalCauchyContour f hf a ha n).property (localCauchyValue f a ha).property))
    (sub_valid (normalizedDisplacedLocalCauchyContour f hf a ha n).property
      (scalarProduct inverseGeometricPeriod (localCauchyValue f a ha)).property)
    (equiv_symm (product_difference_left inverseGeometricPeriod _ _)) hb
  exact Small.congr
    (sub_valid (normalizedDisplacedLocalCauchyContour f hf a ha n).property
      (scalarProduct inverseGeometricPeriod (localCauchyValue f a ha)).property)
    (sub_valid (normalizedDisplacedLocalCauchyContour f hf a ha n).property (f.eval a ha).property)
    (FunctionTheory.sub_congr (equiv_refl _ (normalizedDisplacedLocalCauchyContour f hf a ha n).property)
      (normalizedCauchyValue f a ha)) hs

end ComputableAnalysis.RiemannHilbert.RectangularContour
