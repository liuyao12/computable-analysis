import ComputableAnalysis.RiemannHilbert.InverseFieldHolomorphic
import ComputableAnalysis.RiemannHilbert.FiniteMatrixBounds
import ComputableAnalysis.RiemannHilbert.SystemCoefficientHolomorphic

/-! Every supplied bounded coefficient chart has an actual holomorphic
inverse solution evaluator. The needed bounds, uniform matrix remainders
and derivative continuity are constructed from the coefficient majorants.
The statement retains every finite rank and arbitrary represented inputs. -/
namespace ComputableAnalysis.RiemannHilbert.SystemChart
open ComplexRaw FunctionTheory LocalSystem LinearField DomainFunctions
variable {n : Nat}

def evaluationDerivative (c : SystemChart n) : LinearField.Field (n := n) (m := n) c.domain :=
  fun z hz => (c.valueIso z hz).toValueIso.forward.followedBy (c.operator z hz)

theorem evaluationDerivative_linear (c : SystemChart n) (z : Scalar) (hz : c.domain z) :
    IsLinear (c.evaluationDerivative z hz) :=
  IsLinear.followedBy (c.valueIso z hz).linear (c.operator_linear z hz)

theorem evaluation_congr (c : SystemChart n) (z w : Scalar) (hz : c.domain z) (hw : c.domain w)
    (hzw : z.val.Equiv w.val) :
    (forwardField c.valueIso z hz).Equiv (forwardField c.valueIso w hw) := fun x =>
  c.value_congr c x x (equiv_refl _ c.center.property) (fun _ => ValueMap.equiv_refl _)
    (Setoid.refl x) z w hzw hz hw

theorem evaluationDerivative_congr (c : SystemChart n) (z w : Scalar)
    (hz : c.domain z) (hw : c.domain w) (hzw : z.val.Equiv w.val) :
    (c.evaluationDerivative z hz).Equiv (c.evaluationDerivative w hw) :=
  ValueMap.followedBy_congr (c.evaluation_congr z w hz hw hzw) (c.operator_point_congr z w hz hw hzw)

def inverseDomainData (c : SystemChart n) : ScalarTopology.OpenData c.domain :=
  LinearField.vectorOpenData (CoordinatePullbackChart.solution c (Fiber.zero n))
    (CoordinatePullbackChart.solution_holomorphic c (Fiber.zero n))

theorem evaluation_bound (c : SystemChart n) (z : Scalar) (hz : c.domain z)
    (E : Rat) (hE : 0 ≤ E) (x : Fiber n) (hx : CoordinateBound x E) :
    CoordinateBound ((forwardField c.valueIso z hz).eval x) (2*E) := by
  let q := 8*c.K*c.radius.val
  have hs := ValueMap.bound_of_deviation
    (localValueMap c.coefficients c.M c.K c.nonnegM c.nonnegK c.compatible c.majorant
      (Centered.offset c.center z) hz) q
    (localValueMap_deviation c.coefficients c.M c.K c.nonnegM c.nonnegK c.compatible c.majorant
      (Centered.offset c.center z) hz) E hE x hx
  have hq : q ≤ (1 : Rat)/2 := LocalODE.solutionRadius_small c.K c.nonnegK
  intro i
  apply (hs i).mono
  have hm := Rat.mul_le_mul_of_nonneg_right (show 1+q ≤ 2 by grind only) hE
  exact hm

theorem inverse_evaluation_bound (c : SystemChart n) (z : Scalar) (hz : c.domain z)
    (E : Rat) (hE : 0 ≤ E) (x : Fiber n) (hx : CoordinateBound x E) :
    CoordinateBound ((inverseField c.valueIso z hz).eval x) (4*E) :=
  Neumann.valueMap_bound
    (ValueMap.difference ValueMap.identity (localValueMap c.coefficients c.M c.K c.nonnegM c.nonnegK
      c.compatible c.majorant (Centered.offset c.center z) hz)) (8*c.K*c.radius.val)
    (Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) c.nonnegK) (Rat.le_of_lt c.radius.property))
    (LocalODE.solutionRadius_small c.K c.nonnegK)
    (localValueMap_deviation c.coefficients c.M c.K c.nonnegM c.nonnegK c.compatible c.majorant
      (Centered.offset c.center z) hz) E hE x hx

theorem evaluationDerivative_bound (c : SystemChart n) (z : Scalar) (hz : c.domain z)
    (E : Rat) (hE : 0 ≤ E) (x : Fiber n) (hx : CoordinateBound x E) :
    CoordinateBound ((c.evaluationDerivative z hz).eval x) ((16*c.M)*E) := by
  have hs := c.operator_bound z hz (2*E) (Rat.mul_nonneg (by decide +kernel) hE)
    ((forwardField c.valueIso z hz).eval x) (c.evaluation_bound z hz E hE x hx)
  have he : (8*c.M)*(2*E)=(16*c.M)*E := by grind only
  rw [he] at hs
  exact hs

def evaluationRemainderMap (c : SystemChart n) (w z : Scalar) (hw : c.domain w) (hz : c.domain z) :
    ValueMap (Fiber n) (Fiber n) :=
  ValueMap.difference
    (ValueMap.difference (forwardField c.valueIso z hz) (forwardField c.valueIso w hw))
    ((c.evaluationDerivative w hw).followedBy (Fiber.scaleMap ⟨sub z.val w.val,sub_valid z.property w.property⟩))

theorem evaluationRemainderMap_linear (c : SystemChart n) (w z : Scalar)
    (hw : c.domain w) (hz : c.domain z) : IsLinear (c.evaluationRemainderMap w z hw hz) :=
  ValueMap.difference_linear _ _
    (ValueMap.difference_linear _ _ (c.valueIso z hz).linear (c.valueIso w hw).linear)
    (IsLinear.followedBy (c.evaluationDerivative_linear w hw) (Fiber.scaleMap_linear _))

def evaluationDelta (c : SystemChart n) (eps : QPos) : QPos :=
  FiberTopology.finiteRadius (List.ofFn (fun i : Fin n => c.delta (Fiber.basis i)
    (inputError (2*(n : Rat)) (Rat.mul_nonneg (by decide +kernel) Rat.natCast_nonneg) eps)))

private theorem matrix_remainder_budget (N eta H E eps : Rat)
    (h : eta*(2*N) ≤ eps) (hH : 0 ≤ H) (hE : 0 ≤ E) :
    (2*N*(eta*H))*E ≤ (eps*H)*E := by
  have hm := Rat.mul_le_mul_of_nonneg_right h (Rat.mul_nonneg hH hE)
  grind only

theorem evaluation_uniform_remainder (c : SystemChart n)
    (eps H : QPos) (w z : Scalar) (hw : c.domain w) (hz : c.domain z)
    (hH : H.val ≤ (c.evaluationDelta eps).val) (hzw : Small (sub z.val w.val) H.val)
    (E : Rat) (hE : 0 ≤ E) (x : Fiber n) (hx : CoordinateBound x E) :
    CoordinateBound (operatorRemainder (forwardField c.valueIso) c.evaluationDerivative w z hw hz x)
      ((eps.val*H.val)*E) := by
  let eta := inputError (2*(n : Rat)) (Rat.mul_nonneg (by decide +kernel) Rat.natCast_nonneg) eps
  have hb : ∀ i : Fin n, CoordinateBound ((c.evaluationRemainderMap w z hw hz).eval (Fiber.basis i))
      (eta.val*H.val) := by
    intro i
    have hi : H.val ≤ (c.delta (Fiber.basis i) eta).val :=
      Rat.le_trans hH (FiberTopology.finiteRadius_le _ _ (List.mem_ofFn.mpr ⟨i,rfl⟩))
    exact c.value_uniform_remainder (Fiber.basis i) eta H w z hw hz hi hzw
  have hs := ValueMap.linear_bound_of_basis (c.evaluationRemainderMap w z hw hz)
    (c.evaluationRemainderMap_linear w z hw hz) (eta.val*H.val)
    (Rat.mul_nonneg (Rat.le_of_lt eta.property) (Rat.le_of_lt H.property)) hb x E hE hx
  intro i
  exact (hs i).mono (matrix_remainder_budget (n : Rat) eta.val H.val E eps.val
    (inputError_bound _ _ eps) (Rat.le_of_lt H.property) hE)

def evaluationDerivative_continuous (c : SystemChart n) : MatrixContinuous c.evaluationDerivative :=
  fun i j => baseContinuous_congr
    (DomainFunctions.ofCertifiedHolomorphic (c.coordinate_holomorphic (Fiber.basis i) j)).continuousDerivative
    (fun z hz => c.value_ode (Fiber.basis i) z hz j)

def evaluation_holomorphic (c : SystemChart n) :
    MatrixHolomorphic (forwardField c.valueIso) c.inverseDomainData.invariant c.evaluation_congr :=
  fun i j => DomainFunctions.ofCertifiedHolomorphic (c.coordinate_holomorphic (Fiber.basis i) j)

def inverseEvaluation_holomorphic (c : SystemChart n) :
    MatrixHolomorphic (inverseField c.valueIso) c.inverseDomainData.invariant
      (inverseField_congr c.valueIso c.evaluation_congr) :=
  inverseMatrixHolomorphic c.valueIso c.evaluationDerivative c.inverseDomainData c.evaluation_congr
    c.evaluationDerivative_congr 4 (16*c.M) (by decide +kernel)
    (Rat.mul_nonneg (by decide +kernel) c.nonnegM) c.inverse_evaluation_bound c.evaluationDerivative_bound
    c.evaluationDelta c.evaluation_uniform_remainder c.evaluationDerivative_linear c.evaluationDerivative_continuous

def inverseSolution (c : SystemChart n) (x : Fiber n) : DomainVectorFunctions.Map n :=
  inverseVectorMap c.valueIso c.inverseDomainData c.evaluation_congr x

def inverseSolution_holomorphic (c : SystemChart n) (x : Fiber n) :
    DomainVectorFunctions.Holomorphic (c.inverseSolution x) :=
  inverseVectorHolomorphic c.valueIso c.evaluationDerivative c.inverseDomainData c.evaluation_congr
    c.evaluationDerivative_congr 4 (16*c.M) (by decide +kernel)
    (Rat.mul_nonneg (by decide +kernel) c.nonnegM) c.inverse_evaluation_bound c.evaluationDerivative_bound
    c.evaluationDelta c.evaluation_uniform_remainder c.evaluationDerivative_linear c.evaluationDerivative_continuous x

theorem inverseSlope_operator (c : SystemChart n) (z : Scalar) (hz : c.domain z) (x : Fiber n) :
    (inverseSlope c.valueIso c.evaluationDerivative z hz).eval x ≈
      Fiber.sub (Fiber.zero n) ((inverseField c.valueIso z hz).eval ((c.operator z hz).eval x)) :=
  Fiber.sub_congr (Setoid.refl _)
    ((inverseField c.valueIso z hz).congr ((c.operator z hz).congr ((c.valueIso z hz).toValueIso.forward_backward x)))

theorem inverseSolution_derivative (c : SystemChart n) (x : Fiber n) (z : Scalar) (hz : c.domain z) :
    DomainVectorFunctions.derivative (c.inverseSolution x) (c.inverseSolution_holomorphic x) z hz ≈
      Fiber.sub (Fiber.zero n) ((inverseField c.valueIso z hz).eval ((c.operator z hz).eval x)) :=
  c.inverseSlope_operator z hz x

theorem inverseSolution_agreement (c d : SystemChart n) (x y : Fiber n)
    (hcenter : c.center.val.Equiv d.center.val) (hcoeff : ∀ k, (c.coefficients k).Equiv (d.coefficients k))
    (hxy : x ≈ y) (z w : Scalar) (hzw : z.val.Equiv w.val) (hz : c.domain z) (hw : d.domain w) :
    (c.inverseSolution x).eval z hz ≈ (d.inverseSolution y).eval w hw :=
  Setoid.trans ((c.valueIso z hz).toValueIso.backward.congr hxy)
    (ValueIso.inverse_congr (c.valueIso z hz).toValueIso (d.valueIso w hw).toValueIso
      (fun v => c.value_congr d v v hcenter hcoeff (Setoid.refl v) z w hzw hz hw) y)

theorem inverseSolution_derivative_agreement (c d : SystemChart n) (x y : Fiber n)
    (hcenter : c.center.val.Equiv d.center.val) (hcoeff : ∀ k, (c.coefficients k).Equiv (d.coefficients k))
    (hxy : x ≈ y) (z w : Scalar) (hzw : z.val.Equiv w.val) (hz : c.domain z) (hw : d.domain w) :
    DomainVectorFunctions.derivative (c.inverseSolution x) (c.inverseSolution_holomorphic x) z hz ≈
      DomainVectorFunctions.derivative (d.inverseSolution y) (d.inverseSolution_holomorphic y) w hw :=
  Setoid.trans (c.inverseSolution_derivative x z hz)
    (Setoid.trans (Fiber.sub_congr (Setoid.refl _)
      (c.inverseSolution_agreement d ((c.operator z hz).eval x) ((d.operator w hw).eval y) hcenter hcoeff
        (c.operator_congr d hcenter hcoeff z w hzw hz hw x y hxy) z w hzw hz hw))
      (Setoid.symm (d.inverseSolution_derivative y w hw)))

end ComputableAnalysis.RiemannHilbert.SystemChart
