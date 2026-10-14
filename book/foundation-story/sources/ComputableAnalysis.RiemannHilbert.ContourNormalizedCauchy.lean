import ComputableAnalysis.RiemannHilbert.ContourLocalCauchyRate

/-! Normalization by the independently computed nonzero geometric period
recovers the actual represented center value. -/
namespace ComputableAnalysis.RiemannHilbert.RectangularContour
open ComplexRaw FunctionTheory DomainFunctions
set_option autoImplicit false

theorem geometricPeriod_nonzero : NonzeroBoxSearch.Nonzero geometricPeriod :=
  PDE.CauchyContour.twoPiI_not_equiv_zero

def inverseGeometricPeriod : Scalar :=
  RepresentedReciprocal.inverse geometricPeriod geometricPeriod_nonzero

theorem inverseGeometricPeriod_mul :
    scalarProduct inverseGeometricPeriod geometricPeriod ≈ oneScalar :=
  RepresentedReciprocal.inverse_mul geometricPeriod geometricPeriod_nonzero

theorem normalizedCauchyValue (f : DomainFunctions.Map) (a : Scalar) (ha : f.domain a) :
    scalarProduct inverseGeometricPeriod (localCauchyValue f a ha) ≈ f.eval a ha := by
  have hp := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := (scalarProduct inverseGeometricPeriod geometricPeriod).property)
    (hright := oneScalar.property) inverseGeometricPeriod_mul
  change gridScalarValue inverseGeometricPeriod*gridScalarValue geometricPeriod=1 at hp
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (scalarProduct inverseGeometricPeriod (localCauchyValue f a ha)).property)
    (hright := (f.eval a ha).property)
  change gridScalarValue inverseGeometricPeriod*
    (gridScalarValue (f.eval a ha)*gridScalarValue geometricPeriod)=gridScalarValue (f.eval a ha)
  grind only

def normalizedLocalCauchyContour (f : DomainFunctions.Map) (hf : Holomorphic f)
    (a : Scalar) (ha : f.domain a) (n : Nat) : Scalar :=
  scalarProduct inverseGeometricPeriod (localCauchyContour f hf a ha n)

theorem normalizedLocalCauchyContour_converges (f : DomainFunctions.Map) (hf : Holomorphic f)
    (a : Scalar) (ha : f.domain a) :
    Converges (normalizedLocalCauchyContour f hf a ha) (f.eval a ha) :=
  converge_limit_congr _ _ _
    (converge_product_left inverseGeometricPeriod _ _ (localCauchyContour_converges f hf a ha))
    (normalizedCauchyValue f a ha)

theorem normalizedLocalCauchyContour_limit_identity (f : DomainFunctions.Map) (hf : Holomorphic f)
    (a : Scalar) (ha : f.domain a) (u : Scalar)
    (hu : Converges (normalizedLocalCauchyContour f hf a ha) u) : u ≈ f.eval a ha :=
  converge_unique _ _ _ hu (normalizedLocalCauchyContour_converges f hf a ha)

theorem normalizedLocalCauchy_center_limits_agree (f : DomainFunctions.Map) (hf hg : Holomorphic f)
    (a b : Scalar) (ha : f.domain a) (hb : f.domain b) (he : a ≈ b) (u v : Scalar)
    (hu : Converges (normalizedLocalCauchyContour f hf a ha) u)
    (hv : Converges (normalizedLocalCauchyContour f hg b hb) v) : u ≈ v :=
  Setoid.trans (normalizedLocalCauchyContour_limit_identity f hf a ha u hu)
    (Setoid.trans (f.eval_congr a b ha hb he)
      (Setoid.symm (normalizedLocalCauchyContour_limit_identity f hg b hb v hv)))

def normalizedLocalCauchyStage (f : DomainFunctions.Map) (hf : Holomorphic f)
    (a : Scalar) (ha : f.domain a) (eps : QPos) : Nat :=
  localCauchyStage f hf a ha (divideRadius eps
    ⟨2*scalarBound inverseGeometricPeriod,
      Rat.mul_pos (by decide +kernel) (scalarBound_pos inverseGeometricPeriod)⟩)

theorem normalizedLocalCauchyStage_spec (f : DomainFunctions.Map) (hf : Holomorphic f)
    (a : Scalar) (ha : f.domain a) (eps : QPos) (n : Nat)
    (hn : normalizedLocalCauchyStage f hf a ha eps≤n) :
    Small (sub (normalizedLocalCauchyContour f hf a ha n).val (f.eval a ha).val) eps.val := by
  let C : QPos := ⟨2*scalarBound inverseGeometricPeriod,
    Rat.mul_pos (by decide +kernel) (scalarBound_pos inverseGeometricPeriod)⟩
  let eta := divideRadius eps C
  have hc := localCauchyStage_spec f hf a ha eta n hn
  have hb := Small.mul inverseGeometricPeriod.property
    (sub_valid (localCauchyContour f hf a ha n).property (localCauchyValue f a ha).property)
    (Rat.le_of_lt (scalarBound_pos inverseGeometricPeriod)) (Rat.le_of_lt eta.property)
    (scalar_small inverseGeometricPeriod) hc
  have he : 2*scalarBound inverseGeometricPeriod*eta.val=eps.val := divideRadius_identity eps C
  rw [he] at hb
  have hs := Small.congr
    (mul_valid inverseGeometricPeriod.property
      (sub_valid (localCauchyContour f hf a ha n).property (localCauchyValue f a ha).property))
    (sub_valid (normalizedLocalCauchyContour f hf a ha n).property
      (scalarProduct inverseGeometricPeriod (localCauchyValue f a ha)).property)
    (equiv_symm (product_difference_left inverseGeometricPeriod _ _)) hb
  exact Small.congr
    (sub_valid (normalizedLocalCauchyContour f hf a ha n).property
      (scalarProduct inverseGeometricPeriod (localCauchyValue f a ha)).property)
    (sub_valid (normalizedLocalCauchyContour f hf a ha n).property (f.eval a ha).property)
    (FunctionTheory.sub_congr (equiv_refl _ (normalizedLocalCauchyContour f hf a ha n).property)
      (normalizedCauchyValue f a ha)) hs

end ComputableAnalysis.RiemannHilbert.RectangularContour
