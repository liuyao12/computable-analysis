import ComputableAnalysis.RiemannHilbert.MatrixLogarithmSeries
import ComputableAnalysis.RiemannHilbert.OperatorPowerAlgebra
import ComputableAnalysis.RiemannHilbert.DomainDerivativeUniqueness

/-! The exact resolvent derivative of the constructed Taylor matrix sum.
The inverse of I+zE is constructed by a Neumann evaluator, both inverse laws
are proved, and the actual analytic derivative is identified term by term. -/
namespace ComputableAnalysis.RiemannHilbert.MatrixLogarithm
open ComplexRaw FunctionTheory LocalODE LocalSystem
variable {n : Nat}
set_option maxHeartbeats 1000000

def identityPlus (E : ValueMap (Fiber n) (Fiber n)) (z : Scalar) : ValueMap (Fiber n) (Fiber n) where
  eval x := Fiber.add x (Fiber.scale z (E.eval x))
  congr hxy := Fiber.add_congr hxy (Fiber.scale_congr (equiv_refl _ z.property) (E.congr hxy))

theorem identityPlus_linear (E : ValueMap (Fiber n) (Fiber n)) (hE : IsLinear E) (z : Scalar) : IsLinear (identityPlus E z) := by
  constructor
  · intro x y
    exact Setoid.trans (Fiber.add_congr (Setoid.refl _) (Setoid.trans
      (Fiber.scale_congr (equiv_refl _ z.property) (hE.1 x y)) (Fiber.scale_add z _ _))) (Fiber.add_four _ _ _ _)
  · intro a x
    have h := (IsLinear.followedBy hE (Fiber.scaleMap_linear z)).2 a x
    exact Setoid.trans (Fiber.add_congr (Setoid.refl _) h) (Setoid.symm (Fiber.scale_add a _ _))

theorem identityPlus_congr (E F : ValueMap (Fiber n) (Fiber n)) (hEF : E.Equiv F)
    (z w : Scalar) (hzw : z.val.Equiv w.val) : (identityPlus E z).Equiv (identityPlus F w) :=
  fun x => Fiber.add_congr (Setoid.refl _) (Fiber.scale_congr hzw (hEF x))

def negativeScaled (E : ValueMap (Fiber n) (Fiber n)) (z : Scalar) := OperatorPower.scaled (MatrixExponential.negativeOperator E) z
def deviation (E : ValueMap (Fiber n) (Fiber n)) (z : Scalar) := ValueMap.difference ValueMap.identity (identityPlus E z)

theorem deviation_formula (E : ValueMap (Fiber n) (Fiber n)) (z : Scalar) : (deviation E z).Equiv (negativeScaled E z) := by
  intro x
  have hn := Fiber.scale_congr (equiv_refl _ z.property) (MatrixExponential.negativeOperator_value E x)
  have he : (deviation E z).eval x ≈ Fiber.scale z (Fiber.neg (E.eval x)) := by
    intro i
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := ((deviation E z).eval x).property i) (hright := (Fiber.scale z (Fiber.neg (E.eval x))).property i)
    let X := ComplexRawQuotient.ofRaw (x.val i) (x.property i)
    let Y := ComplexRawQuotient.ofRaw ((E.eval x).val i) ((E.eval x).property i)
    let Z := ComplexRawQuotient.ofRaw z.val z.property
    change X-(X+Z*Y)=Z*(-Y)
    grind only
  exact Setoid.trans he (Setoid.symm hn)

def resolventContraction : Rat := 1/8
theorem deviation_bound (E : ValueMap (Fiber n) (Fiber n)) (hsmall : SmallOperator E)
    (z : Scalar) (hz : interior radius.val z) (B : Rat) (hB : 0 ≤ B) (x : Fiber n) (hx : CoordinateBound x B) :
    CoordinateBound ((deviation E z).eval x) (resolventContraction*B) := by
  have he := hsmall B hB x hx
  have hn : CoordinateBound ((MatrixExponential.negativeOperator E).eval x) (contraction*B) :=
    bound_congr (Setoid.symm (MatrixExponential.negativeOperator_value E x)) (fun i => SeriesLimitLaws.small_neg (he i))
  have hs := bound_scale (c := z) (Rat.le_of_lt radius.property)
    (Rat.mul_nonneg (by decide +kernel : (0 : Rat) ≤ contraction) hB) (interior_bound radius.val z hz) hn
  have hr : 2*radius.val*(contraction*B)=resolventContraction*B := by
    have hnum : 2*radius.val*contraction=resolventContraction := by decide +kernel
    rw [← Rat.mul_assoc,hnum]
  rw [hr] at hs
  exact bound_congr (Setoid.symm (deviation_formula E z x)) hs

def resolventIso (E : ValueMap (Fiber n) (Fiber n)) (hE : IsLinear E) (hsmall : SmallOperator E)
    (z : Scalar) (hz : interior radius.val z) : LinearIso n n :=
  Neumann.linearIso (identityPlus E z) (identityPlus_linear E hE z) resolventContraction (by decide +kernel) (by decide +kernel)
    (deviation_bound E hsmall z hz)

def resolvent (E : ValueMap (Fiber n) (Fiber n)) (hE : IsLinear E) (hsmall : SmallOperator E)
    (z : Scalar) (hz : interior radius.val z) := (resolventIso E hE hsmall z hz).toValueIso.backward

theorem resolvent_linear (E : ValueMap (Fiber n) (Fiber n)) (hE : IsLinear E) (hsmall : SmallOperator E)
    (z : Scalar) (hz : interior radius.val z) : IsLinear (resolvent E hE hsmall z hz) :=
  (resolventIso E hE hsmall z hz).inverse.linear

theorem resolvent_left (E : ValueMap (Fiber n) (Fiber n)) (hE : IsLinear E) (hsmall : SmallOperator E)
    (z : Scalar) (hz : interior radius.val z) (x : Fiber n) :
    (identityPlus E z).eval ((resolvent E hE hsmall z hz).eval x) ≈ x :=
  (resolventIso E hE hsmall z hz).toValueIso.forward_backward x

theorem resolvent_right (E : ValueMap (Fiber n) (Fiber n)) (hE : IsLinear E) (hsmall : SmallOperator E)
    (z : Scalar) (hz : interior radius.val z) (x : Fiber n) :
    (resolvent E hE hsmall z hz).eval ((identityPlus E z).eval x) ≈ x :=
  (resolventIso E hE hsmall z hz).toValueIso.backward_forward x

theorem derivativeTerm_formula (E : ValueMap (Fiber n) (Fiber n)) (x : Fiber n) (z : Scalar) (k : Nat) (i : Fin n) :
    (BoundedSeries.derivativeTerm (fun j => ((coefficientMap E j).eval x).val i) z.val k).Equiv
      ((Fiber.scale ⟨power z.val k,power_valid z.val z.property k⟩
        (ratScale (FormalPowerSeries.altSign k) ((Neumann.power E (k+1)).eval x))).val i) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := BoundedSeries.derivativeTerm_valid _ z.val (fun j => ((coefficientMap E j).eval x).property i) z.property k)
    (hright := (Fiber.scale ⟨power z.val k,power_valid z.val z.property k⟩
      (ratScale (FormalPowerSeries.altSign k) ((Neumann.power E (k+1)).eval x))).property i)
  let Y := ComplexRawQuotient.ofRaw (((Neumann.power E (k+1)).eval x).val i) (((Neumann.power E (k+1)).eval x).property i)
  let P := ComplexRawQuotient.ofRaw (power z.val k) (power_valid z.val z.property k)
  change ComplexRawQuotient.scaleRat ((k+1 : Nat) : Rat)
    ((ComplexRawQuotient.scaleRat (LocalLogarithm.coefficientRat (k+1)) (1 : ScalarAlgebra.Value)*Y)*P) =
    P*ComplexRawQuotient.scaleRat (FormalPowerSeries.altSign k) Y
  rw [← ComplexRawQuotient.scaleRat_mul,← ComplexRawQuotient.scaleRat_mul,
    ComplexRawQuotient.scaleRat_scaleRat,LocalLogarithm.coefficient_equation]
  have hOne : ((1 : ScalarAlgebra.Value)*Y)*P=Y*P := by grind only
  rw [hOne,ComplexRawQuotient.scaleRat_mul]
  grind only

theorem derivativeTerm_power (E : ValueMap (Fiber n) (Fiber n)) (hE : IsLinear E) (x : Fiber n) (z : Scalar) (k : Nat) (i : Fin n) :
    (BoundedSeries.derivativeTerm (fun j => ((coefficientMap E j).eval x).val i) z.val k).Equiv
      (((Neumann.power (deviation E z) k).eval (E.eval x)).val i) := by
  have hp := Setoid.trans (Neumann.power_congr (deviation E z) (negativeScaled E z) (deviation_formula E z) k (E.eval x))
    (OperatorPower.negative_scaled_power E hE z x k)
  exact equiv_trans (BoundedSeries.derivativeTerm_valid _ z.val (fun j => ((coefficientMap E j).eval x).property i) z.property k)
    ((Fiber.scale ⟨power z.val k,power_valid z.val z.property k⟩
      (ratScale (FormalPowerSeries.altSign k) ((Neumann.power E (k+1)).eval x))).property i)
    (((Neumann.power (deviation E z) k).eval (E.eval x)).property i)
    (derivativeTerm_formula E x z k i) (equiv_symm (hp i))

theorem vector_derivative_resolvent (E : ValueMap (Fiber n) (Fiber n)) (hE : IsLinear E) (hsmall : SmallOperator E)
    (x : Fiber n) (hF : DomainVectorFunctions.Holomorphic (vector E hsmall x)) (z : Scalar) (hz : interior radius.val z) :
    DomainVectorFunctions.derivative (vector E hsmall x) hF z hz ≈ (resolvent E hE hsmall z hz).eval (E.eval x) := by
  have he : DomainVectorFunctions.derivative (vector E hsmall x) hF z hz ≈
      DomainVectorFunctions.derivative (vector E hsmall x) (vector_holomorphic E hsmall x) z hz :=
    fun i => (hF.coordinates i).derivative_unique ((vector_holomorphic E hsmall x).coordinates i) z hz
  apply Setoid.trans he
  intro i
  let c := fun j => ((coefficientMap E j).eval x).val i
  let hc := fun j => ((coefficientMap E j).eval x).property i
  let B := initialBound x
  let C := 2*1*B
  let K := contraction
  let R := radius.val
  let F := initialBound (E.eval x)
  have hC : 0 ≤ C := Rat.mul_nonneg (Rat.mul_nonneg (by decide) (by decide)) (LocalSystem.initialBound_nonneg x)
  have hK : 0 ≤ K := by decide +kernel
  have hR : 0 ≤ R := by decide +kernel
  have hcoef : ∀ j, Small (c j) (C*K^j) := fun j =>
    operatorCoefficient_bound (coefficientMap E) 1 contraction B (LocalSystem.initialBound_nonneg x)
      (coefficientMap_majorant E hsmall) x (LocalSystem.initialBound_valid x) j i
  change (ScalarSeries.value (BoundedSeries.derivativeTerm c z.val)
      (BoundedSeries.derivativeTerm_valid c z.val hc z.property) (C*K) (4*K*R)).Equiv
    (ScalarSeries.value (fun k => ((Neumann.power (deviation E z) k).eval (E.eval x)).val i)
      (fun k => ((Neumann.power (deviation E z) k).eval (E.eval x)).property i) F resolventContraction)
  exact ScalarSeries.value_congr _ _ _ _ (C*K) (4*K*R) F resolventContraction
    (Rat.mul_nonneg hC hK) (by decide +kernel) (LocalSystem.initialBound_nonneg (E.eval x)) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (fun k => by
      simpa only [Rat.mul_assoc] using BoundedSeries.derivativeTerm_majorant c z.val hc z.property
        C K R hC hK hR hcoef (interior_bound radius.val z hz) k)
    (fun k => Neumann.term_bound (deviation E z) resolventContraction (by decide +kernel)
      (deviation_bound E hsmall z hz) F (LocalSystem.initialBound_nonneg (E.eval x)) (E.eval x) (LocalSystem.initialBound_valid (E.eval x)) k i)
    (derivativeTerm_power E hE x z · i)

end ComputableAnalysis.RiemannHilbert.MatrixLogarithm
