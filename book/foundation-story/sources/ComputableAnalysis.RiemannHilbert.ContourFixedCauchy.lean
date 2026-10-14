import ComputableAnalysis.RiemannHilbert.ContourShrinkingChain

/-! A fixed local square Cauchy formula, derived from actual holomorphic
annuli and the independently computed reciprocal period. No contour limit
or Cauchy identity is supplied in the hypotheses. -/
namespace ComputableAnalysis.RiemannHilbert.RectangularContour
open ComplexRaw FunctionTheory DomainFunctions
set_option autoImplicit false

def fixedSquareCauchyContour (f : DomainFunctions.Map) (hf : Holomorphic f)
    (a : Scalar) (ha : f.domain a) (n : Nat) : Scalar :=
  nestedSquareInner f hf a ha 0 n

theorem fixedSquareCauchyContour_rectangular (f : DomainFunctions.Map) (hf : Holomorphic f)
    (a : Scalar) (ha : f.domain a) :
    Converges (fixedSquareCauchyContour f hf a ha) (scalarProduct (f.eval a ha) rectangularPeriod) := by
  intro eps
  let eta := divideRadius eps (⟨3,by decide +kernel⟩ : QPos)
  let theta := divideRadius eta (⟨64,by decide +kernel⟩ : QPos)
  let m := contourErrorStage f hf a ha (hf.continuous.delta a ha theta)
  obtain ⟨A,hA⟩ := shrinkingChainError_eventual f hf a ha m eta
  let c := f.eval a ha
  let B := RationalMajorant.natRateStage (32*scalarBound c) eta
  refine ⟨max A B+m, ?_⟩
  intro k hk
  let n := k-m
  have hnA : A≤n := by dsimp [n]; omega
  have hnB : B≤n := by dsimp [n]; omega
  have hekn : n+m=k := by dsimp [n]; omega
  let X := fixedSquareCauchyContour f hf a ha k
  let Y := nestedSquareInner f hf a ha m n
  let P := shrinkingReciprocalPrefix f hf a ha m (2^n)
  let Z := scalarProduct c P
  let U := scalarProduct c rectangularPeriod
  have hXY := hA n hnA
  change Small (sub (nestedSquareInner f hf a ha 0 (n+m)).val Y.val) eta.val at hXY
  rw [hekn] at hXY
  have hnum := shrinkingPrefix_center_estimate f hf a ha theta m (2^n) (Nat.two_pow_pos n) (Nat.le_refl m)
  have he1 : 64*theta.val=eta.val := divideRadius_identity eta (⟨64,by decide +kernel⟩ : QPos)
  rw [he1] at hnum
  have hYZ := Small.congr
    (sub_valid (shrinkingCauchyPrefix f hf a ha m (2^n)).property Z.property)
    (sub_valid Y.property Z.property)
    (FunctionTheory.sub_congr (equiv_symm (nestedSquareInner_actual f hf a ha m n))
      (equiv_refl _ Z.property)) hnum
  have hperiod := reciprocalInnerPrefix_geometric_error (shrinkingContourRadius f hf a ha m) n
  have hmul := Small.mul c.property (sub_valid P.property rectangularPeriod.property)
    (Rat.le_of_lt (scalarBound_pos c))
    (Rat.mul_nonneg (by decide +kernel) (Rat.le_of_lt (Rat.pow_pos (by decide +kernel))))
    (scalar_small c) hperiod
  have hC : 0≤32*scalarBound c := Rat.mul_nonneg (by decide +kernel) (Rat.le_of_lt (scalarBound_pos c))
  have hrate := contour_half_rate (32*scalarBound c) hC eta n hnB
  have hsize : 2*scalarBound c*(16*((1:Rat)/2)^n)=32*scalarBound c*((1:Rat)/2)^n := by grind only
  rw [hsize] at hmul
  have hZU := Small.congr (mul_valid c.property (sub_valid P.property rectangularPeriod.property))
    (sub_valid Z.property U.property) (equiv_symm (product_difference_left c P rectangularPeriod)) (hmul.mono hrate)
  have hs := LocalODE.small_add (LocalODE.small_add hXY hYZ) hZU
  have heps : (eta.val+eta.val)+eta.val=eps.val := by
    have h := divideRadius_identity eps (⟨3,by decide +kernel⟩ : QPos)
    change 3*eta.val=eps.val at h
    grind only
  rw [heps] at hs
  exact Small.congr
    (add_valid (add_valid (sub_valid X.property Y.property) (sub_valid Y.property Z.property))
      (sub_valid Z.property U.property)) (sub_valid X.property U.property)
    (equiv_symm (SeriesLimitLaws.difference_via X.val U.val Y.val Z.val X.property U.property Y.property Z.property)) hs

/-- Actual fixed-square boundary sums converge to the geometric Cauchy value. -/
theorem fixedSquareCauchyContour_converges (f : DomainFunctions.Map) (hf : Holomorphic f)
    (a : Scalar) (ha : f.domain a) :
    Converges (fixedSquareCauchyContour f hf a ha) (localCauchyValue f a ha) := by
  apply converge_limit_congr _ _ _ (fixedSquareCauchyContour_rectangular f hf a ha)
  exact mul_equiv (f.eval a ha).property (f.eval a ha).property rectangularPeriod.property
    geometricPeriod.property (equiv_refl _ (f.eval a ha).property) rectangularPeriod_geometric

theorem fixedSquareCauchyContour_limit_identity (f : DomainFunctions.Map) (hf : Holomorphic f)
    (a : Scalar) (ha : f.domain a) (u : Scalar)
    (hu : Converges (fixedSquareCauchyContour f hf a ha) u) : u ≈ localCauchyValue f a ha :=
  converge_unique _ _ _ hu (fixedSquareCauchyContour_converges f hf a ha)

def normalizedFixedSquareCauchyContour (f : DomainFunctions.Map) (hf : Holomorphic f)
    (a : Scalar) (ha : f.domain a) (n : Nat) : Scalar :=
  scalarProduct inverseGeometricPeriod (fixedSquareCauchyContour f hf a ha n)

/-- A normalized fixed contour recovers the actual value at every represented center. -/
theorem normalizedFixedSquareCauchyContour_converges (f : DomainFunctions.Map) (hf : Holomorphic f)
    (a : Scalar) (ha : f.domain a) :
    Converges (normalizedFixedSquareCauchyContour f hf a ha) (f.eval a ha) :=
  converge_limit_congr _ _ _
    (converge_product_left inverseGeometricPeriod _ _ (fixedSquareCauchyContour_converges f hf a ha))
    (normalizedCauchyValue f a ha)

theorem normalizedFixedSquareCauchyContour_limit_identity (f : DomainFunctions.Map) (hf : Holomorphic f)
    (a : Scalar) (ha : f.domain a) (u : Scalar)
    (hu : Converges (normalizedFixedSquareCauchyContour f hf a ha) u) : u ≈ f.eval a ha :=
  converge_unique _ _ _ hu (normalizedFixedSquareCauchyContour_converges f hf a ha)

theorem normalizedFixedSquareCauchy_center_limits_agree (f : DomainFunctions.Map) (hf hg : Holomorphic f)
    (a b : Scalar) (ha : f.domain a) (hb : f.domain b) (he : a ≈ b) (u v : Scalar)
    (hu : Converges (normalizedFixedSquareCauchyContour f hf a ha) u)
    (hv : Converges (normalizedFixedSquareCauchyContour f hg b hb) v) : u ≈ v :=
  Setoid.trans (normalizedFixedSquareCauchyContour_limit_identity f hf a ha u hu)
    (Setoid.trans (f.eval_congr a b ha hb he)
      (Setoid.symm (normalizedFixedSquareCauchyContour_limit_identity f hg b hb v hv)))

end ComputableAnalysis.RiemannHilbert.RectangularContour
