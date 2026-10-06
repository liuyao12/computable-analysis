import ComputableAnalysis.RiemannHilbert.MatrixLogarithmUniform
import ComputableAnalysis.RiemannHilbert.ExponentialOperatorIncrement

/-! Actual exponentials of the constructed Taylor matrix field. Its values
commute, so the proved operator increment formula gives a uniform quadratic
remainder. No exponential–logarithm identity is assumed in these estimates. -/
namespace ComputableAnalysis.RiemannHilbert.MatrixLogarithm
open ComplexRaw FunctionTheory LocalSystem LocalODE LinearField
variable {n : Nat}
set_option maxHeartbeats 2000000

def exponential (E : ValueMap (Fiber n) (Fiber n)) (hE : IsLinear E) (hsmall : SmallOperator E) :
    LinearField.Field (n := n) (m := n) (interior radius.val) :=
  fun z hz => MatrixExponential.value (parameterValue E hsmall z hz) (parameterValue_linear E hE hsmall z hz) MatrixExponential.operatorUnit

def exponentialBound : Rat := MatrixExponential.suppliedValueBound 8
theorem exponentialBound_nonneg : 0 ≤ exponentialBound := MatrixExponential.suppliedValueBound_nonneg 8

theorem exponential_bound (E : ValueMap (Fiber n) (Fiber n)) (hE : IsLinear E) (hsmall : SmallOperator E)
    (z : Scalar) (hz : interior radius.val z) (B : Rat) (hB : 0 ≤ B) (x : Fiber n) (hx : CoordinateBound x B) :
    CoordinateBound ((exponential E hE hsmall z hz).eval x) (exponentialBound*B) :=
  MatrixExponential.value_supplied_bound (parameterValue E hsmall z hz) (parameterValue_linear E hE hsmall z hz) 8
    (by decide +kernel) (parameterValue_bound E hsmall z hz) B hB x hx

theorem exponential_linear (E : ValueMap (Fiber n) (Fiber n)) (hE : IsLinear E) (hsmall : SmallOperator E)
    (z : Scalar) (hz : interior radius.val z) : IsLinear (exponential E hE hsmall z hz) :=
  MatrixExponential.value_linear _ (parameterValue_linear E hE hsmall z hz) _

theorem exponential_congr (E : ValueMap (Fiber n) (Fiber n)) (hE : IsLinear E) (hsmall : SmallOperator E)
    (z w : Scalar) (hz : interior radius.val z) (hw : interior radius.val w) (hzw : z.val.Equiv w.val) :
    (exponential E hE hsmall z hz).Equiv (exponential E hE hsmall w hw) :=
  fun x => MatrixExponential.value_congr _ _ (parameterValue_linear E hE hsmall z hz) (parameterValue_linear E hE hsmall w hw)
    (field_congr E hsmall z w hz hw hzw) _ _ (equiv_refl _ MatrixExponential.operatorUnit.property) x x (Setoid.refl _)

theorem slope_linear (E : ValueMap (Fiber n) (Fiber n)) (hE : IsLinear E) (hsmall : SmallOperator E)
    (z : Scalar) (hz : interior radius.val z) : IsLinear (slope E hE hsmall z hz) :=
  IsLinear.followedBy hE (resolvent_linear E hE hsmall z hz)

theorem slope_commutes (E : ValueMap (Fiber n) (Fiber n)) (hE : IsLinear E) (hsmall : SmallOperator E)
    (z w : Scalar) (hz : interior radius.val z) (hw : interior radius.val w) (x : Fiber n) :
    (parameterValue E hsmall z hz).eval ((slope E hE hsmall w hw).eval x) ≈
      (slope E hE hsmall w hw).eval ((parameterValue E hsmall z hz).eval x) :=
  Setoid.trans (parameterValue_resolvent_commutes E hE hsmall z w hz hw (E.eval x))
    ((resolvent E hE hsmall w hw).congr (Setoid.symm (parameterValue_commutes E hE hsmall z hz x)))

theorem exponential_slope_commutes (E : ValueMap (Fiber n) (Fiber n)) (hE : IsLinear E) (hsmall : SmallOperator E)
    (z : Scalar) (hz : interior radius.val z) (x : Fiber n) :
    (slope E hE hsmall z hz).eval ((exponential E hE hsmall z hz).eval x) ≈
      (exponential E hE hsmall z hz).eval ((slope E hE hsmall z hz).eval x) :=
  MatrixExponential.value_intertwines _ (parameterValue_linear E hE hsmall z hz) _ (parameterValue_linear E hE hsmall z hz)
    (slope E hE hsmall z hz) (slope_linear E hE hsmall z hz)
    (fun y => Setoid.symm (slope_commutes E hE hsmall z z hz hz y)) MatrixExponential.operatorUnit x

def exponentialSlope (E : ValueMap (Fiber n) (Fiber n)) (hE : IsLinear E) (hsmall : SmallOperator E) :
    LinearField.Field (n := n) (m := n) (interior radius.val) :=
  fun z hz => (slope E hE hsmall z hz).followedBy (exponential E hE hsmall z hz)

theorem exponential_remainder_decompose (E : ValueMap (Fiber n) (Fiber n)) (hE : IsLinear E) (hsmall : SmallOperator E)
    (w z : Scalar) (hw : interior radius.val w) (hz : interior radius.val z) (x : Fiber n) :
    operatorRemainder (exponential E hE hsmall) (exponentialSlope E hE hsmall) w z hw hz x ≈
      Fiber.add (MatrixExponential.incrementRemainder (parameterValue E hsmall w hw) (parameterValue E hsmall z hz)
        (parameterValue_linear E hE hsmall w hw) (parameterValue_linear E hE hsmall z hz) x)
        ((exponential E hE hsmall w hw).eval (operatorRemainder (field E hsmall) (slope E hE hsmall) w z hw hz x)) := by
  let d : Scalar := ⟨sub z.val w.val,sub_valid z.property w.property⟩
  let v := (ValueMap.difference (parameterValue E hsmall z hz) (parameterValue E hsmall w hw)).eval x
  let F := exponential E hE hsmall w hw
  have hFl := exponential_linear E hE hsmall w hw
  have hi : F.eval (operatorRemainder (field E hsmall) (slope E hE hsmall) w z hw hz x) ≈
      Fiber.sub (F.eval v) (Fiber.scale d (F.eval ((slope E hE hsmall w hw).eval x))) :=
    Setoid.trans (hFl.sub v (Fiber.scale d ((slope E hE hsmall w hw).eval x)))
      (Fiber.sub_congr (Setoid.refl _) (hFl.2 d _))
  exact Setoid.trans (Fiber.difference_split _ _ (F.eval v)) (Fiber.add_congr (Setoid.refl _) (Setoid.symm hi))

theorem exponential_remainder_bound (E : ValueMap (Fiber n) (Fiber n)) (hE : IsLinear E) (hsmall : SmallOperator E)
    (w z : Scalar) (hw : interior radius.val w) (hz : interior radius.val z) (H : QPos)
    (hH : H.val ≤ 1/5) (hzw : Small (sub z.val w.val) H.val)
    (B : Rat) (hB : 0 ≤ B) (x : Fiber n) (hx : CoordinateBound x B) :
    CoordinateBound (operatorRemainder (exponential E hE hsmall) (exponentialSlope E hE hsmall) w z hw hz x)
      ((51*exponentialBound*H.val^2)*B) := by
  have hh : H.val ≤ 32 := Rat.le_trans hH (by decide +kernel)
  have ht : 0 ≤ (5/4 : Rat)*H.val := Rat.mul_nonneg (by decide +kernel) (Rat.le_of_lt H.property)
  have hq := MatrixExponential.incrementRemainder_bound (parameterValue E hsmall w hw) (parameterValue E hsmall z hz)
    (parameterValue_linear E hE hsmall w hw) (parameterValue_linear E hE hsmall z hz)
    (parameterValues_commute E hE hsmall w z hw hz) 8 ((5/4)*H.val) (by decide +kernel) ht (by grind only)
    (parameterValue_bound E hsmall w hw) (difference_bound E hE hsmall w z hw hz H hh hzw) B hB x hx
  have h50 : 32*MatrixExponential.suppliedValueBound 8*((5/4)*H.val)^2*B=(50*exponentialBound*H.val^2)*B := by
    simp only [Rat.pow_succ,Rat.pow_zero,Rat.one_mul]
    dsimp [exponentialBound]
    grind only
  rw [h50] at hq
  have hl := remainder_bound E hE hsmall w z hw hz H.val (Rat.le_of_lt H.property) hzw B hB x hx
  have hi := exponential_bound E hE hsmall w hw (((1/32)*H.val^2)*B)
    (Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) (Rat.pow_nonneg (Rat.le_of_lt H.property))) hB) _ hl
  have hb := bound_congr (Setoid.symm (exponential_remainder_decompose E hE hsmall w z hw hz x)) (bound_add hq hi)
  have hn : 0 ≤ exponentialBound*H.val^2*B := Rat.mul_nonneg
    (Rat.mul_nonneg exponentialBound_nonneg (Rat.pow_nonneg (Rat.le_of_lt H.property))) hB
  intro i
  exact (hb i).mono (by grind only)

def exponentialDelta (eps : QPos) : QPos :=
  smallerRadius ⟨1/5,by decide +kernel⟩ ⟨eps.val/(51*exponentialBound+1),by
    rw [Rat.div_def]
    exact Rat.mul_pos eps.property ((Rat.inv_pos).2 (by have := exponentialBound_nonneg; grind only))⟩

theorem exponential_uniform_remainder (E : ValueMap (Fiber n) (Fiber n)) (hE : IsLinear E) (hsmall : SmallOperator E)
    (eps H : QPos) (w z : Scalar) (hw : interior radius.val w) (hz : interior radius.val z)
    (hH : H.val ≤ (exponentialDelta eps).val) (hzw : Small (sub z.val w.val) H.val)
    (B : Rat) (hB : 0 ≤ B) (x : Fiber n) (hx : CoordinateBound x B) :
    CoordinateBound (operatorRemainder (exponential E hE hsmall) (exponentialSlope E hE hsmall) w z hw hz x) ((eps.val*H.val)*B) := by
  have h1 : H.val ≤ 1/5 := Rat.le_trans hH (smallerRadius_le_left _ _)
  have h2 : H.val ≤ eps.val/(51*exponentialBound+1) := Rat.le_trans hH (smallerRadius_le_right _ _)
  have hn : 0 ≤ 51*exponentialBound := Rat.mul_nonneg (by decide +kernel) exponentialBound_nonneg
  have he : (eps.val/(51*exponentialBound+1))*(51*exponentialBound+1)=eps.val :=
    Rat.div_mul_cancel (Rat.ne_of_gt (by grind only))
  have hm := Rat.mul_le_mul_of_nonneg_right h2 (by grind only : 0 ≤ 51*exponentialBound+1)
  rw [he] at hm
  have hprod : (51*exponentialBound)*H.val ≤ eps.val := by have := H.property; grind only
  have hb := Rat.mul_le_mul_of_nonneg_right (Rat.mul_le_mul_of_nonneg_right hprod (Rat.le_of_lt H.property)) hB
  have hs := exponential_remainder_bound E hE hsmall w z hw hz H h1 hzw B hB x hx
  intro i
  exact (hs i).mono (by simpa only [Rat.pow_succ,Rat.pow_zero,Rat.one_mul,Rat.mul_assoc] using hb)

end ComputableAnalysis.RiemannHilbert.MatrixLogarithm
