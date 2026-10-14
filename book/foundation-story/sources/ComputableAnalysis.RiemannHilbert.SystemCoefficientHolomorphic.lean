import ComputableAnalysis.RiemannHilbert.CoordinateCoefficientHolomorphic
import ComputableAnalysis.RiemannHilbert.CoordinatePullbackChart

/-! The actual bounded-series coefficient operator of every constructed
system chart is holomorphic. Its reciprocal coordinate pullback therefore
has constructed holomorphic coefficient evidence at every finite rank. -/
namespace ComputableAnalysis.RiemannHilbert.SystemChart
open ComplexRaw FunctionTheory LocalSystem
variable {n : Nat}

def operatorCoordinate (c : SystemChart n) (x : Fiber n) (i : Fin n) : CertifiedFunctions.Map :=
  CertifiedFunctions.translateInput c.center
    (BoundedSeries.seriesMap (fun k => ((c.coefficients k).eval x).val i)
      (fun k => ((c.coefficients k).eval x).property i)
      (2*c.M*initialBound x) c.K c.radius.val
      (Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) c.nonnegM) (initialBound_nonneg x))
      c.nonnegK (Rat.le_of_lt c.radius.property)
      (fun k => operatorCoefficient_bound c.coefficients c.M c.K (initialBound x)
        (initialBound_nonneg x) c.majorant x (initialBound_valid x) k i)
      (LocalODE.solutionRadius_small c.K c.nonnegK))

def operatorCoordinate_holomorphic (c : SystemChart n) (x : Fiber n) (i : Fin n) :
    CertifiedFunctions.Holomorphic (c.operatorCoordinate x i) :=
  CertifiedFunctions.translateDerivative c.center
    (BoundedSeries.seriesMap_holomorphic (fun k => ((c.coefficients k).eval x).val i)
      (fun k => ((c.coefficients k).eval x).property i)
      (2*c.M*initialBound x) c.K c.radius.val
      (Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) c.nonnegM) (initialBound_nonneg x))
      c.nonnegK (Rat.le_of_lt c.radius.property)
      (fun k => operatorCoefficient_bound c.coefficients c.M c.K (initialBound x)
        (initialBound_nonneg x) c.majorant x (initialBound_valid x) k i)
      (LocalODE.solutionRadius_small c.K c.nonnegK))

theorem operatorCoordinate_value (c : SystemChart n) (x : Fiber n) (i : Fin n)
    (z : Scalar) (hz : c.domain z) :
    (c.operatorCoordinate x i).eval z = ((c.operator z hz).eval x).val i := rfl

theorem operator_point_congr (c : SystemChart n) (z w : Scalar)
    (hz : c.domain z) (hw : c.domain w) (hzw : z.val.Equiv w.val) :
    (c.operator z hz).Equiv (c.operator w hw) :=
  fun x => c.operator_congr c (equiv_refl _ c.center.property)
    (fun _ => ValueMap.equiv_refl _) z w hzw hz hw x x (Setoid.refl x)

def operator_holomorphic (c : SystemChart n) (initial : Fiber n) :
    CoordinateConnection.HolomorphicCoefficient (CoordinatePullbackChart.solution c initial)
      c.operator c.operator_point_congr := by
  intro x
  exact {
    openDomain := {
      radius := (CoordinatePullbackChart.solution_holomorphic c initial).openDomain.radius
      inside := (CoordinatePullbackChart.solution_holomorphic c initial).openDomain.inside }
    coordinates := fun i => DomainFunctions.ofCertifiedHolomorphic (c.operatorCoordinate_holomorphic x i) }

def reciprocalOperator_holomorphic (c : SystemChart n) (initial : Fiber n) :
    CoordinateConnection.HolomorphicCoefficient
      (DomainVectorFunctions.pullback (CoordinatePullbackChart.solution c initial) ReciprocalHolomorphic.function)
      (CoordinateConnection.pullback (CoordinatePullbackChart.solution c initial)
        ReciprocalHolomorphic.function ReciprocalHolomorphic.holomorphic c.operator)
      (CoordinateConnection.pullback_point_congr (CoordinatePullbackChart.solution c initial)
        ReciprocalHolomorphic.function ReciprocalHolomorphic.holomorphic c.operator c.operator_point_congr) :=
  CoordinateConnection.reciprocal_holomorphic (CoordinatePullbackChart.solution c initial)
    c.operator c.operator_point_congr (c.operator_holomorphic initial)

end ComputableAnalysis.RiemannHilbert.SystemChart
