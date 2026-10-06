import ComputableAnalysis.RiemannHilbert.LocalSystemODEIdentity
import ComputableAnalysis.RiemannHilbert.LimitLinearMaps

/-! The constructed coefficient function is linear, holomorphic in every
coordinate, and independent of names and certified geometric majorants. -/
namespace ComputableAnalysis.RiemannHilbert.LocalSystem
open ComplexRaw FunctionTheory LocalODE
variable {n : Nat}

theorem operatorValue_linear (a : Nat → ValueMap (Fiber n) (Fiber n)) (ha : ∀ k, IsLinear (a k))
    (z : Scalar) (M K R : Rat) (hM : 0 ≤ M) (hK : 0 ≤ K) (hR : 0 ≤ R)
    (haB : OperatorMajorant a M K) (hz : Small z.val R) (hlocal : 2*K*R ≤ (1 : Rat)/2) :
    IsLinear (operatorValue a z M K R hM hK hR haB hz hlocal) := by
  apply linear_of_prefixes _ (operatorPrefixMap a z) (operatorPrefixMap_linear a ha z)
    (fun x N => 8*M*initialBound x*(2*K*R)^N)
  · intro x
    exact operatorError_shrinks M (initialBound x) K R hM (initialBound_nonneg x) hK hR hlocal
  · intro x N
    exact Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg (by decide) hM) (initialBound_nonneg x))
      (Rat.pow_nonneg (Rat.mul_nonneg (Rat.mul_nonneg (by decide) hK) hR))
  · intro x N
    exact operatorValue_close a z M K R (initialBound x) hM hK hR (initialBound_nonneg x)
      haB hz hlocal x (initialBound_valid x) N

theorem coefficientValueMap_linear (a : Nat → ValueMap (Fiber n) (Fiber n)) (ha : ∀ k, IsLinear (a k))
    (M K : Rat) (hM : 0 ≤ M) (hK : 0 ≤ K) (haB : OperatorMajorant a M K)
    (z : Scalar) (hz : interior (solutionRadius K hK).val z) :
    IsLinear (coefficientValueMap a M K hM hK haB z hz) :=
  operatorValue_linear a ha z M K (solutionRadius K hK).val hM hK
    (Rat.le_of_lt (solutionRadius K hK).property) haB (interior_bound _ z hz)
    (by
      have := solutionRadius_small K hK
      have := Rat.mul_nonneg hK (Rat.le_of_lt (solutionRadius K hK).property)
      grind)

theorem coefficientValueMap_congr
    (a b : Nat → ValueMap (Fiber n) (Fiber n)) (hab : ∀ k, ValueMap.Equiv (a k) (b k))
    (M K P L : Rat) (hM : 0 ≤ M) (hK : 0 ≤ K) (hP : 0 ≤ P) (hL : 0 ≤ L)
    (haB : OperatorMajorant a M K) (hbB : OperatorMajorant b P L)
    (z w : Scalar) (hzw : z.val.Equiv w.val)
    (hz : interior (solutionRadius K hK).val z) (hw : interior (solutionRadius L hL).val w)
    (x y : Fiber n) (hxy : x ≈ y) :
    (coefficientValueMap a M K hM hK haB z hz).eval x ≈
      (coefficientValueMap b P L hP hL hbB w hw).eval y :=
  VectorSeries.value_congr _ _ z w
    (fun k => Setoid.trans ((a k).congr hxy) (hab k y)) hzw
    (2*M*initialBound x) K (solutionRadius K hK).val
    (2*P*initialBound y) L (solutionRadius L hL).val
    (Rat.mul_nonneg (Rat.mul_nonneg (by decide) hM) (initialBound_nonneg x)) hK
    (Rat.le_of_lt (solutionRadius K hK).property)
    (Rat.mul_nonneg (Rat.mul_nonneg (by decide) hP) (initialBound_nonneg y)) hL
    (Rat.le_of_lt (solutionRadius L hL).property)
    (operatorCoefficient_bound a M K (initialBound x) (initialBound_nonneg x) haB x (initialBound_valid x))
    (operatorCoefficient_bound b P L (initialBound y) (initialBound_nonneg y) hbB y (initialBound_valid y))
    (interior_bound _ z hz) (interior_bound _ w hw)
    (by
      have := solutionRadius_small K hK
      have := Rat.mul_nonneg hK (Rat.le_of_lt (solutionRadius K hK).property)
      grind)
    (by
      have := solutionRadius_small L hL
      have := Rat.mul_nonneg hL (Rat.le_of_lt (solutionRadius L hL).property)
      grind)

def coefficientCoordinateMap (a : Nat → ValueMap (Fiber n) (Fiber n))
    (M K : Rat) (hM : 0 ≤ M) (hK : 0 ≤ K) (haB : OperatorMajorant a M K)
    (x : Fiber n) (d : Fin n) : CertifiedFunctions.Map :=
  BoundedSeries.seriesMap (fun k => ((a k).eval x).val d) (fun k => ((a k).eval x).property d)
    (2*M*initialBound x) K (solutionRadius K hK).val
    (Rat.mul_nonneg (Rat.mul_nonneg (by decide) hM) (initialBound_nonneg x)) hK
    (Rat.le_of_lt (solutionRadius K hK).property)
    (fun k => operatorCoefficient_bound a M K (initialBound x) (initialBound_nonneg x)
      haB x (initialBound_valid x) k d)
    (solutionRadius_small K hK)

def coefficientCoordinateMap_holomorphic (a : Nat → ValueMap (Fiber n) (Fiber n))
    (M K : Rat) (hM : 0 ≤ M) (hK : 0 ≤ K) (haB : OperatorMajorant a M K)
    (x : Fiber n) (d : Fin n) : CertifiedFunctions.Holomorphic (coefficientCoordinateMap a M K hM hK haB x d) :=
  BoundedSeries.seriesMap_holomorphic (fun k => ((a k).eval x).val d) (fun k => ((a k).eval x).property d)
    (2*M*initialBound x) K (solutionRadius K hK).val
    (Rat.mul_nonneg (Rat.mul_nonneg (by decide) hM) (initialBound_nonneg x)) hK
    (Rat.le_of_lt (solutionRadius K hK).property)
    (fun k => operatorCoefficient_bound a M K (initialBound x) (initialBound_nonneg x)
      haB x (initialBound_valid x) k d)
    (solutionRadius_small K hK)

theorem coefficientValueMap_coordinate (a : Nat → ValueMap (Fiber n) (Fiber n))
    (M K : Rat) (hM : 0 ≤ M) (hK : 0 ≤ K) (haB : OperatorMajorant a M K)
    (x : Fiber n) (d : Fin n) (z : Scalar) (hz : interior (solutionRadius K hK).val z) :
    (coefficientCoordinateMap a M K hM hK haB x d).eval z =
      ((coefficientValueMap a M K hM hK haB z hz).eval x).val d := rfl

theorem coefficientValueMap_initial (a : Nat → ValueMap (Fiber n) (Fiber n))
    (M K : Rat) (hM : 0 ≤ M) (hK : 0 ≤ K) (haB : OperatorMajorant a M K) (x : Fiber n) :
    (coefficientValueMap a M K hM hK haB ⟨zero, ofQComplex_valid _⟩
      (interior_zero _ (solutionRadius K hK).property)).eval x ≈ (a 0).eval x :=
  fun d => BoundedSeries.seriesMap_initial _ _ _ _ _
    (Rat.mul_nonneg (Rat.mul_nonneg (by decide) hM) (initialBound_nonneg x)) hK
    (Rat.le_of_lt (solutionRadius K hK).property)
    (fun k => operatorCoefficient_bound a M K (initialBound x) (initialBound_nonneg x)
      haB x (initialBound_valid x) k d) (solutionRadius_small K hK)

end ComputableAnalysis.RiemannHilbert.LocalSystem
