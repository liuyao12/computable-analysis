import ComputableAnalysis.RiemannHilbert.ContourDyadicPeriod

/-! The shrinking inner Cauchy contour is constructed at every represented
point of an actual holomorphic function, with no supplied period limit. -/
namespace ComputableAnalysis.RiemannHilbert.RectangularContour
open ComplexRaw FunctionTheory DomainFunctions
set_option autoImplicit false

def localCauchyContour (f : DomainFunctions.Map) (hf : Holomorphic f)
    (a : Scalar) (ha : f.domain a) (n : Nat) : Scalar :=
  shrinkingCauchyPrefix f hf a ha n (2^n)

def localCauchyValue (f : DomainFunctions.Map) (a : Scalar) (ha : f.domain a) : Scalar :=
  scalarProduct (f.eval a ha) geometricPeriod

theorem converge_limit_congr (p : Nat → Scalar) (a b : Scalar)
    (hp : Converges p a) (he : a ≈ b) : Converges p b := by
  intro eps
  obtain ⟨N,hN⟩ := hp eps
  refine ⟨N,fun n hn => ?_⟩
  exact Small.congr (sub_valid (p n).property a.property) (sub_valid (p n).property b.property)
    (FunctionTheory.sub_congr (equiv_refl _ (p n).property) he) (hN n hn)

/-- The actual shrinking-square computation has the center-times-period limit. -/
theorem localCauchyContour_converges (f : DomainFunctions.Map) (hf : Holomorphic f)
    (a : Scalar) (ha : f.domain a) :
    Converges (localCauchyContour f hf a ha) (localCauchyValue f a ha) := by
  have hp := reciprocalInnerPrefix_converges (shrinkingContourRadius f hf a ha)
  have hc := shrinking_inner_converges f hf a ha (fun n => 2^n) (Nat.two_pow_pos)
    rectangularPeriod hp
  apply converge_limit_congr _ _ _ hc
  exact mul_equiv (f.eval a ha).property (f.eval a ha).property
    rectangularPeriod.property geometricPeriod.property
    (equiv_refl _ (f.eval a ha).property) rectangularPeriod_geometric

/-- Every supplied limit of this actual contour has the exact geometric value. -/
theorem localCauchyContour_limit_identity (f : DomainFunctions.Map) (hf : Holomorphic f)
    (a : Scalar) (ha : f.domain a) (u : Scalar)
    (hu : Converges (localCauchyContour f hf a ha) u) : u ≈ localCauchyValue f a ha :=
  converge_unique _ _ _ hu (localCauchyContour_converges f hf a ha)

theorem localCauchyValue_congr (f : DomainFunctions.Map) (a b : Scalar)
    (ha : f.domain a) (hb : f.domain b) (he : a ≈ b) :
    localCauchyValue f a ha ≈ localCauchyValue f b hb :=
  mul_equiv (f.eval a ha).property (f.eval b hb).property geometricPeriod.property
    geometricPeriod.property (f.eval_congr a b ha hb he) (equiv_refl _ geometricPeriod.property)

theorem localCauchy_center_limits_agree (f : DomainFunctions.Map) (hf hg : Holomorphic f)
    (a b : Scalar) (ha : f.domain a) (hb : f.domain b) (he : a ≈ b) (u v : Scalar)
    (hu : Converges (localCauchyContour f hf a ha) u)
    (hv : Converges (localCauchyContour f hg b hb) v) : u ≈ v :=
  Setoid.trans (localCauchyContour_limit_identity f hf a ha u hu)
    (Setoid.trans (localCauchyValue_congr f a b ha hb he)
      (Setoid.symm (localCauchyContour_limit_identity f hg b hb v hv)))

end ComputableAnalysis.RiemannHilbert.RectangularContour
