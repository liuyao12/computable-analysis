import ComputableAnalysis.RiemannHilbert.MatrixLogarithmIntertwiners
import ComputableAnalysis.RiemannHilbert.MatrixCompositionRemainders

/-! Uniform first-order estimates for the actual Taylor matrix field.
Supplied input bounds replace the evaluator's first-box bounds by proved
series agreement. The rational error radius is independent of the input. -/
namespace ComputableAnalysis.RiemannHilbert.MatrixLogarithm
open ComplexRaw FunctionTheory LocalSystem LocalODE LinearField
variable {n : Nat}
set_option maxHeartbeats 1000000

theorem value_series_agreement (E : ValueMap (Fiber n) (Fiber n)) (hsmall : SmallOperator E)
    (z : Scalar) (hz : interior radius.val z) (B : Rat) (hB : 0 ≤ B)
    (x : Fiber n) (hx : CoordinateBound x B) (i : Fin n) :
    (((parameterValue E hsmall z hz).eval x).val i).Equiv
      (BoundedSeries.sumValue (fun k => ((coefficientMap E k).eval x).val i) z.val
        (fun k => ((coefficientMap E k).eval x).property i) z.property (2*1*B) contraction radius.val) :=
  operatorValue_agreement (coefficientMap E) z 1 contraction radius.val B
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hB (coefficientMap_majorant E hsmall)
    (interior_bound radius.val z hz) (by decide +kernel) x hx i

def slope (E : ValueMap (Fiber n) (Fiber n)) (hE : IsLinear E) (hsmall : SmallOperator E) :
    LinearField.Field (n := n) (m := n) (interior radius.val) :=
  fun z hz => E.followedBy (resolvent E hE hsmall z hz)

theorem slope_bound (E : ValueMap (Fiber n) (Fiber n)) (hE : IsLinear E) (hsmall : SmallOperator E)
    (z : Scalar) (hz : interior radius.val z) (B : Rat) (hB : 0 ≤ B) (x : Fiber n) (hx : CoordinateBound x B) :
    CoordinateBound ((slope E hE hsmall z hz).eval x) ((1/8 : Rat)*B) := by
  have hs := resolvent_bound E hE hsmall z hz (contraction*B) (Rat.mul_nonneg (by decide +kernel) hB)
    (E.eval x) (hsmall B hB x hx)
  have he : 4*(contraction*B)=(1/8 : Rat)*B := by
    rw [← Rat.mul_assoc]
    congr 1
    decide +kernel
  rw [he] at hs
  exact hs

theorem derivative_series_agreement (E : ValueMap (Fiber n) (Fiber n)) (hE : IsLinear E) (hsmall : SmallOperator E)
    (z : Scalar) (hz : interior radius.val z) (B : Rat) (hB : 0 ≤ B)
    (x : Fiber n) (hx : CoordinateBound x B) (i : Fin n) :
    (BoundedSeries.sumDerivative (fun k => ((coefficientMap E k).eval x).val i) z.val
      (fun k => ((coefficientMap E k).eval x).property i) z.property (2*1*B) contraction radius.val).Equiv
      (((slope E hE hsmall z hz).eval x).val i) := by
  let c := fun k => ((coefficientMap E k).eval x).val i
  let hc := fun k => ((coefficientMap E k).eval x).property i
  have hC : 0 ≤ 2*1*B := Rat.mul_nonneg (Rat.mul_nonneg (by decide) (by decide)) hB
  have hD : 0 ≤ 2*1*LocalSystem.initialBound x :=
    Rat.mul_nonneg (Rat.mul_nonneg (by decide) (by decide)) (LocalSystem.initialBound_nonneg x)
  have hv := BoundedSeries.sumDerivative_valid c z.val hc z.property (2*1*B) contraction radius.val
    hC (by decide +kernel) (by decide +kernel)
    (fun k => operatorCoefficient_bound (coefficientMap E) 1 contraction B hB (coefficientMap_majorant E hsmall) x hx k i)
    (interior_bound radius.val z hz) (by decide +kernel)
  let d := DomainVectorFunctions.derivative (vector E hsmall x) (vector_holomorphic E hsmall x) z hz
  have he := BoundedSeries.sumDerivative_congr_of_bounds c c z.val z.val hc hc z.property z.property
    (fun k => equiv_refl _ (hc k)) (equiv_refl _ z.property)
    (2*1*B) contraction radius.val (2*1*LocalSystem.initialBound x) contraction radius.val
    hC (by decide +kernel) (by decide +kernel) hD (by decide +kernel) (by decide +kernel)
    (fun k => operatorCoefficient_bound (coefficientMap E) 1 contraction B hB (coefficientMap_majorant E hsmall) x hx k i)
    (fun k => operatorCoefficient_bound (coefficientMap E) 1 contraction (LocalSystem.initialBound x)
      (LocalSystem.initialBound_nonneg x) (coefficientMap_majorant E hsmall) x (LocalSystem.initialBound_valid x) k i)
    (interior_bound radius.val z hz) (interior_bound radius.val z hz) (by decide +kernel) (by decide +kernel)
  exact equiv_trans hv (d.property i) (((slope E hE hsmall z hz).eval x).property i) he
    (vector_derivative_resolvent E hE hsmall x (vector_holomorphic E hsmall x) z hz i)

theorem remainder_bound (E : ValueMap (Fiber n) (Fiber n)) (hE : IsLinear E) (hsmall : SmallOperator E)
    (w z : Scalar) (hw : interior radius.val w) (hz : interior radius.val z)
    (H : Rat) (hH : 0 ≤ H) (hzw : Small (sub z.val w.val) H)
    (B : Rat) (hB : 0 ≤ B) (x : Fiber n) (hx : CoordinateBound x B) :
    CoordinateBound (operatorRemainder (field E hsmall) (slope E hE hsmall) w z hw hz x)
      (((1/32 : Rat)*H^2)*B) := by
  let C := 2*1*B
  have hC : 0 ≤ C := Rat.mul_nonneg (Rat.mul_nonneg (by decide) (by decide)) hB
  intro i
  let c := fun k => ((coefficientMap E k).eval x).val i
  let hc := fun k => ((coefficientMap E k).eval x).property i
  have hcb : ∀ k, Small (c k) (C*contraction^k) := fun k =>
    operatorCoefficient_bound (coefficientMap E) 1 contraction B hB (coefficientMap_majorant E hsmall) x hx k i
  have hv := BoundedSeries.sumValue_valid c z.val hc z.property C contraction radius.val hC
    (by decide +kernel) (by decide +kernel) hcb (interior_bound radius.val z hz) (by decide +kernel)
  have hwv := BoundedSeries.sumValue_valid c w.val hc w.property C contraction radius.val hC
    (by decide +kernel) (by decide +kernel) hcb (interior_bound radius.val w hw) (by decide +kernel)
  have hd := BoundedSeries.sumDerivative_valid c w.val hc w.property C contraction radius.val hC
    (by decide +kernel) (by decide +kernel) hcb (interior_bound radius.val w hw) (by decide +kernel)
  have hs := BoundedSeries.sum_remainder_bound c w.val z.val hc w.property z.property C contraction radius.val H
    hC (by decide +kernel) (by decide +kernel) hH hcb (interior_bound radius.val w hw) (interior_bound radius.val z hz)
    hzw (by decide +kernel)
  have he : 16*C*contraction^2*H^2=((1/32 : Rat)*H^2)*B := by
    have hq : 32*contraction^2=(1/32 : Rat) := by decide +kernel
    dsimp [C]
    grind only
  rw [he] at hs
  have hde : (mul (BoundedSeries.sumDerivative c w.val hc w.property C contraction radius.val) (sub z.val w.val)).Equiv
      (mul (sub z.val w.val) (((slope E hE hsmall w hw).eval x).val i)) :=
    equiv_trans (mul_valid hd (sub_valid z.property w.property))
      (mul_valid (((slope E hE hsmall w hw).eval x).property i) (sub_valid z.property w.property))
      (mul_valid (sub_valid z.property w.property) (((slope E hE hsmall w hw).eval x).property i))
      (mul_equiv hd (((slope E hE hsmall w hw).eval x).property i)
        (sub_valid z.property w.property) (sub_valid z.property w.property)
        (derivative_series_agreement E hE hsmall w hw B hB x hx i) (equiv_refl _ (sub_valid z.property w.property)))
      (mul_comm_equiv _ _ (((slope E hE hsmall w hw).eval x).property i) (sub_valid z.property w.property))
  exact Small.congr (SeriesLimitLaws.remainder_valid _ _ _ _ hv hwv hd (sub_valid z.property w.property))
    ((operatorRemainder (field E hsmall) (slope E hE hsmall) w z hw hz x).property i)
    (FunctionTheory.sub_congr (FunctionTheory.sub_congr (equiv_symm (value_series_agreement E hsmall z hz B hB x hx i))
      (equiv_symm (value_series_agreement E hsmall w hw B hB x hx i))) hde) hs

def delta (eps : QPos) : QPos := ⟨32*eps.val,Rat.mul_pos (by decide +kernel) eps.property⟩

theorem uniform_remainder (E : ValueMap (Fiber n) (Fiber n)) (hE : IsLinear E) (hsmall : SmallOperator E)
    (eps H : QPos) (w z : Scalar) (hw : interior radius.val w) (hz : interior radius.val z)
    (hH : H.val ≤ (delta eps).val) (hzw : Small (sub z.val w.val) H.val)
    (B : Rat) (hB : 0 ≤ B) (x : Fiber n) (hx : CoordinateBound x B) :
    CoordinateBound (operatorRemainder (field E hsmall) (slope E hE hsmall) w z hw hz x) ((eps.val*H.val)*B) := by
  have hs := remainder_bound E hE hsmall w z hw hz H.val (Rat.le_of_lt H.property) hzw B hB x hx
  have hscale := Rat.mul_le_mul_of_nonneg_left hH (by decide +kernel : (0 : Rat) ≤ 1/32)
  have hnum : (1/32 : Rat)*32=1 := by decide +kernel
  change (1/32 : Rat)*H.val ≤ (1/32 : Rat)*(32*eps.val) at hscale
  rw [← Rat.mul_assoc,hnum,Rat.one_mul] at hscale
  have hb := Rat.mul_le_mul_of_nonneg_right
    (Rat.mul_le_mul_of_nonneg_right hscale (Rat.le_of_lt H.property)) hB
  intro i
  exact (hs i).mono (by simpa only [Rat.pow_succ,Rat.pow_zero,Rat.one_mul,Rat.mul_assoc] using hb)

theorem matrix_uniform_remainder (E : ValueMap (Fiber n) (Fiber n)) (hE : IsLinear E) (hsmall : SmallOperator E)
    (hM : MatrixHolomorphic (field E hsmall) (vector E hsmall (Fiber.zero n)).domain_congr (field_congr E hsmall))
    (eps H : QPos) (w z : Scalar) (hw : interior radius.val w) (hz : interior radius.val z)
    (hH : H.val ≤ (delta eps).val) (hzw : Small (sub z.val w.val) H.val)
    (B : Rat) (hB : 0 ≤ B) (x : Fiber n) (hx : CoordinateBound x B) :
    CoordinateBound (operatorRemainder (field E hsmall) (derivativeField hM) w z hw hz x) ((eps.val*H.val)*B) :=
  bound_congr (operatorRemainder_congr (field E hsmall) (slope E hE hsmall) (field E hsmall) (derivativeField hM)
    (fun _ _ => ValueMap.equiv_refl _) (fun v hv y => Setoid.symm (field_derivative_resolvent E hE hsmall hM v hv y)) w z hw hz x)
    (uniform_remainder E hE hsmall eps H w z hw hz hH hzw B hB x hx)

theorem difference_bound (E : ValueMap (Fiber n) (Fiber n)) (hE : IsLinear E) (hsmall : SmallOperator E)
    (w z : Scalar) (hw : interior radius.val w) (hz : interior radius.val z) (H : QPos)
    (hH : H.val ≤ 32) (hzw : Small (sub z.val w.val) H.val)
    (B : Rat) (hB : 0 ≤ B) (x : Fiber n) (hx : CoordinateBound x B) :
    CoordinateBound ((ValueMap.difference (field E hsmall z hz) (field E hsmall w hw)).eval x) (((5/4 : Rat)*H.val)*B) := by
  have hs := operator_difference_bound (field E hsmall) (slope E hE hsmall) (1/8) (by decide +kernel)
    (slope_bound E hE hsmall) w z hw hz H hzw
    (by
      intro C hC y hy
      simpa only [Rat.one_mul] using uniform_remainder E hE hsmall ⟨1,by decide +kernel⟩ H w z hw hz
        (by simpa only [delta,Rat.mul_one] using hH) hzw C hC y hy)
    B hB x hx
  simpa only [show 2*(1/8 : Rat)+1=5/4 by decide +kernel] using hs

end ComputableAnalysis.RiemannHilbert.MatrixLogarithm
