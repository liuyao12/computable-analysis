import ComputableAnalysis.RiemannHilbert.LocalSystemSuperposition
import ComputableAnalysis.RiemannHilbert.GeneralSeriesHolomorphic

/-! Holomorphic coordinates of the actual finite-rank local series value. -/
namespace ComputableAnalysis.RiemannHilbert.LocalSystem
open ComplexRaw FunctionTheory
variable {n : Nat}

def coordinateMap (a : Nat → ValueMap (Fiber n) (Fiber n)) (initial : Fiber n)
    (M K : Rat) (hM : 0 ≤ M) (hK : 0 ≤ K) (hMK : 2*M ≤ K)
    (haB : OperatorMajorant a M K) (i : Fin n) : CertifiedFunctions.Map :=
  BoundedSeries.seriesMap (coordinateSeries a initial i) (coordinateSeries_valid a initial i)
    (initialBound initial) K (LocalODE.solutionRadius K hK).val
    (initialBound_nonneg initial) hK (Rat.le_of_lt (LocalODE.solutionRadius K hK).property)
    (fun k => coefficient_majorant a initial M (initialBound initial) K hM
      (initialBound_nonneg initial) hK hMK haB (initialBound_valid initial) k i)
    (LocalODE.solutionRadius_small K hK)

def coordinateMap_holomorphic (a : Nat → ValueMap (Fiber n) (Fiber n)) (initial : Fiber n)
    (M K : Rat) (hM : 0 ≤ M) (hK : 0 ≤ K) (hMK : 2*M ≤ K)
    (haB : OperatorMajorant a M K) (i : Fin n) :
    CertifiedFunctions.Holomorphic (coordinateMap a initial M K hM hK hMK haB i) :=
  BoundedSeries.seriesMap_holomorphic (coordinateSeries a initial i) (coordinateSeries_valid a initial i)
    (initialBound initial) K (LocalODE.solutionRadius K hK).val
    (initialBound_nonneg initial) hK (Rat.le_of_lt (LocalODE.solutionRadius K hK).property)
    (fun k => coefficient_majorant a initial M (initialBound initial) K hM
      (initialBound_nonneg initial) hK hMK haB (initialBound_valid initial) k i)
    (LocalODE.solutionRadius_small K hK)

/-- The holomorphic witness is for the vector evaluator itself. -/
theorem coordinateMap_value (a : Nat → ValueMap (Fiber n) (Fiber n)) (initial : Fiber n)
    (M K : Rat) (hM : 0 ≤ M) (hK : 0 ≤ K) (hMK : 2*M ≤ K)
    (haB : OperatorMajorant a M K) (i : Fin n) (z : Scalar)
    (hz : LocalODE.interior (LocalODE.solutionRadius K hK).val z) :
    (coordinateMap a initial M K hM hK hMK haB i).eval z =
      (localValue a initial M K hM hK hMK haB z hz).val i := rfl

theorem coordinateMap_initial (a : Nat → ValueMap (Fiber n) (Fiber n)) (initial : Fiber n)
    (M K : Rat) (hM : 0 ≤ M) (hK : 0 ≤ K) (hMK : 2*M ≤ K)
    (haB : OperatorMajorant a M K) (i : Fin n) :
    ((coordinateMap a initial M K hM hK hMK haB i).eval ⟨zero, ofQComplex_valid _⟩).Equiv
      (initial.val i) :=
  localValue_initial a initial M K hM hK hMK haB i

def localDerivative (a : Nat → ValueMap (Fiber n) (Fiber n)) (initial : Fiber n)
    (M K : Rat) (hM : 0 ≤ M) (hK : 0 ≤ K) (hMK : 2*M ≤ K)
    (haB : OperatorMajorant a M K) (z : Scalar)
    (hz : LocalODE.interior (LocalODE.solutionRadius K hK).val z) : Fiber n :=
  ⟨fun i => (coordinateMap_holomorphic a initial M K hM hK hMK haB i).derivative z,
    fun i => ((coordinateMap_holomorphic a initial M K hM hK hMK haB i).atPoint z hz).derivative_valid⟩

theorem localDerivative_congr (a b : Nat → ValueMap (Fiber n) (Fiber n)) (x y : Fiber n)
    (hab : ∀ k, (a k).Equiv (b k)) (hxy : x ≈ y)
    (M K P L : Rat) (hM : 0 ≤ M) (hK : 0 ≤ K) (hP : 0 ≤ P) (hL : 0 ≤ L)
    (hMK : 2*M ≤ K) (hPL : 2*P ≤ L)
    (haB : OperatorMajorant a M K) (hbB : OperatorMajorant b P L)
    (z w : Scalar) (hzw : z.val.Equiv w.val)
    (hz : LocalODE.interior (LocalODE.solutionRadius K hK).val z)
    (hw : LocalODE.interior (LocalODE.solutionRadius L hL).val w) :
    localDerivative a x M K hM hK hMK haB z hz ≈ localDerivative b y P L hP hL hPL hbB w hw := by
  intro i
  exact BoundedSeries.sumDerivative_congr_of_bounds (coordinateSeries a x i) (coordinateSeries b y i)
    z.val w.val (coordinateSeries_valid a x i) (coordinateSeries_valid b y i) z.property w.property
    (fun k => coefficient_congr a b x y hab hxy k i) hzw
    (initialBound x) K (LocalODE.solutionRadius K hK).val
    (initialBound y) L (LocalODE.solutionRadius L hL).val
    (initialBound_nonneg x) hK (Rat.le_of_lt (LocalODE.solutionRadius K hK).property)
    (initialBound_nonneg y) hL (Rat.le_of_lt (LocalODE.solutionRadius L hL).property)
    (fun k => coefficient_majorant a x M (initialBound x) K hM (initialBound_nonneg x) hK hMK haB
      (initialBound_valid x) k i)
    (fun k => coefficient_majorant b y P (initialBound y) L hP (initialBound_nonneg y) hL hPL hbB
      (initialBound_valid y) k i)
    (LocalODE.interior_bound _ z hz) (LocalODE.interior_bound _ w hw)
    (by have := LocalODE.solutionRadius_small K hK
        have := Rat.mul_nonneg hK (Rat.le_of_lt (LocalODE.solutionRadius K hK).property)
        grind)
    (by have := LocalODE.solutionRadius_small L hL
        have := Rat.mul_nonneg hL (Rat.le_of_lt (LocalODE.solutionRadius L hL).property)
        grind)

end ComputableAnalysis.RiemannHilbert.LocalSystem
