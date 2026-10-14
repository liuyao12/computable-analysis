import ComputableAnalysis.RiemannHilbert.ExponentialMatrixDerivative
import ComputableAnalysis.RiemannHilbert.MatrixCompositionRemainders

/-! Uniform operator remainder estimates for the entire exponential on every
finite disc. Independently supplied input bounds replace first-box bounds by
proved series agreement, so the radius does not depend on the input vector. -/
namespace ComputableAnalysis.RiemannHilbert.MatrixExponential
open ComplexRaw FunctionTheory LocalSystem LocalODE
variable {n : Nat}

theorem disc_coefficient_bound (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A)
    (R : QPos) (E : Rat) (hE : 0 ≤ E) (x : Fiber n) (hx : CoordinateBound x E) (k : Nat) :
    CoordinateBound (coefficient A x k) ((2*discBudget A R.val*E)*(rate R.val)^k) :=
  operatorCoefficient_bound (coefficientMap A) _ _ E hE
    (disc_majorant A hA R.val (Rat.le_of_lt R.property)) x hx k

theorem value_series_agreement (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A)
    (R : QPos) (z : Scalar) (hz : interior R.val z) (E : Rat) (hE : 0 ≤ E)
    (x : Fiber n) (hx : CoordinateBound x E) (i : Fin n) :
    (((value A hA z).eval x).val i).Equiv
      (BoundedSeries.sumValue (fun k => (coefficient A x k).val i) z.val
        (fun k => (coefficient A x k).property i) z.property
        (2*discBudget A R.val*E) (rate R.val) R.val) := by
  have hR := Rat.le_of_lt R.property
  have hK := Rat.le_of_lt (rate_pos R.val hR)
  have h2 : 2*rate R.val*R.val ≤ (1 : Rat)/2 := by
    have := rate_small R.val hR; have := Rat.mul_nonneg hK hR; grind
  exact Setoid.trans (value_onDisc A hA R z hz x)
    (operatorValue_agreement (coefficientMap A) z _ _ _ E (discBudget_nonneg A R.val) hK hR hE
      (disc_majorant A hA R.val hR) (interior_bound R.val z hz) h2 x hx) i

theorem derivative_series_agreement (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A)
    (R : QPos) (z : Scalar) (hz : interior R.val z) (E : Rat) (hE : 0 ≤ E)
    (x : Fiber n) (hx : CoordinateBound x E) (i : Fin n) :
    (BoundedSeries.sumDerivative (fun k => (coefficient A x k).val i) z.val
      (fun k => (coefficient A x k).property i) z.property
      (2*discBudget A R.val*E) (rate R.val) R.val).Equiv
      ((A.eval ((value A hA z).eval x)).val i) := by
  let c := fun k => (coefficient A x k).val i
  let hc := fun k => (coefficient A x k).property i
  let M := discBudget A R.val
  let K := rate R.val
  have hR := Rat.le_of_lt R.property
  have hK : 0 ≤ K := Rat.le_of_lt (rate_pos R.val hR)
  have hM : 0 ≤ M := discBudget_nonneg A R.val
  have hC : 0 ≤ 2*M*E := Rat.mul_nonneg (Rat.mul_nonneg (by decide) hM) hE
  have hD : 0 ≤ 2*M*LocalSystem.initialBound x :=
    Rat.mul_nonneg (Rat.mul_nonneg (by decide) hM) (LocalSystem.initialBound_nonneg x)
  have h4 : 4*K*R.val ≤ (1 : Rat)/2 := by
    have := rate_small R.val hR; have := Rat.mul_nonneg hK hR; grind
  have hv := BoundedSeries.sumDerivative_valid c z.val hc z.property (2*M*E) K R.val hC hK hR
    (fun k => disc_coefficient_bound A hA R E hE x hx k i) (interior_bound R.val z hz) h4
  let d := DomainVectorFunctions.derivative (discVector A hA R x) (discVector_holomorphic A hA R x) z hz
  have he := BoundedSeries.sumDerivative_congr_of_bounds c c z.val z.val hc hc z.property z.property
    (fun k => equiv_refl _ (hc k)) (equiv_refl _ z.property)
    (2*M*E) K R.val (2*M*LocalSystem.initialBound x) K R.val hC hK hR hD hK hR
    (fun k => disc_coefficient_bound A hA R E hE x hx k i)
    (fun k => disc_coefficient_bound A hA R _ (LocalSystem.initialBound_nonneg x)
      x (LocalSystem.initialBound_valid x) k i)
    (interior_bound R.val z hz) (interior_bound R.val z hz) h4 h4
  exact equiv_trans hv (d.property i) ((A.eval ((value A hA z).eval x)).property i) he
    (Setoid.trans (onDisc_derivative_ode A hA R x z hz)
      (A.congr (Setoid.symm (value_onDisc A hA R z hz x))) i)

def discField (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A) (R : QPos) :
    LinearField.Field (n := n) (m := n) (interior R.val) := fun z _ => value A hA z

def discSlope (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A) (R : QPos) :
    LinearField.Field (n := n) (m := n) (interior R.val) := fun z _ => (value A hA z).followedBy A

theorem discSlope_linear (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A)
    (R : QPos) (z : Scalar) (_hz : interior R.val z) : IsLinear (discSlope A hA R z _hz) :=
  IsLinear.followedBy (value_linear A hA z) hA

theorem disc_remainder_bound (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A)
    (R : QPos) (w z : Scalar) (hw : interior R.val w) (hz : interior R.val z)
    (H : Rat) (hH : 0 ≤ H) (hzw : Small (sub z.val w.val) H)
    (E : Rat) (hE : 0 ≤ E) (x : Fiber n) (hx : CoordinateBound x E) :
    CoordinateBound (LinearField.operatorRemainder (discField A hA R) (discSlope A hA R) w z hw hz x)
      ((32*discBudget A R.val*(rate R.val)^2)*H^2*E) := by
  let M := discBudget A R.val
  let K := rate R.val
  let C := 2*M*E
  have hM : 0 ≤ M := discBudget_nonneg A R.val
  have hK : 0 ≤ K := Rat.le_of_lt (rate_pos R.val (Rat.le_of_lt R.property))
  have hR := Rat.le_of_lt R.property
  have hC : 0 ≤ C := Rat.mul_nonneg (Rat.mul_nonneg (by decide) hM) hE
  have h8 : 8*K*R.val ≤ (1 : Rat)/2 := rate_small R.val hR
  have h2 : 2*K*R.val ≤ (1 : Rat)/2 := by have := Rat.mul_nonneg hK hR; grind
  have h4 : 4*K*R.val ≤ (1 : Rat)/2 := by have := Rat.mul_nonneg hK hR; grind
  intro i
  let c := fun k => (coefficient A x k).val i
  let hc := fun k => (coefficient A x k).property i
  have hcb : ∀ k, Small (c k) (C*K^k) := fun k => disc_coefficient_bound A hA R E hE x hx k i
  have hF := BoundedSeries.sumValue_valid c z.val hc z.property C K R.val hC hK hR hcb
    (interior_bound R.val z hz) h2
  have hG := BoundedSeries.sumValue_valid c w.val hc w.property C K R.val hC hK hR hcb
    (interior_bound R.val w hw) h2
  have hD := BoundedSeries.sumDerivative_valid c w.val hc w.property C K R.val hC hK hR hcb
    (interior_bound R.val w hw) h4
  have hs := BoundedSeries.sum_remainder_bound c w.val z.val hc w.property z.property C K R.val H
    hC hK hR hH hcb (interior_bound R.val w hw) (interior_bound R.val z hz) hzw h8
  have he : 16*C*K^2*H^2=(32*M*K^2)*H^2*E := by dsimp [C]; grind
  rw [he] at hs
  have hdEq : (mul (BoundedSeries.sumDerivative c w.val hc w.property C K R.val) (sub z.val w.val)).Equiv
      (mul (sub z.val w.val) ((A.eval ((value A hA w).eval x)).val i)) :=
    equiv_trans (mul_valid hD (sub_valid z.property w.property))
      (mul_valid ((A.eval ((value A hA w).eval x)).property i) (sub_valid z.property w.property))
      (mul_valid (sub_valid z.property w.property) ((A.eval ((value A hA w).eval x)).property i))
      (mul_equiv hD ((A.eval ((value A hA w).eval x)).property i)
        (sub_valid z.property w.property) (sub_valid z.property w.property)
        (derivative_series_agreement A hA R w hw E hE x hx i) (equiv_refl _ (sub_valid z.property w.property)))
      (mul_comm_equiv _ _ ((A.eval ((value A hA w).eval x)).property i) (sub_valid z.property w.property))
  exact Small.congr (SeriesLimitLaws.remainder_valid _ _ _ _ hF hG hD (sub_valid z.property w.property))
    ((LinearField.operatorRemainder (discField A hA R) (discSlope A hA R) w z hw hz x).property i)
    (FunctionTheory.sub_congr
      (FunctionTheory.sub_congr (equiv_symm (value_series_agreement A hA R z hz E hE x hx i))
        (equiv_symm (value_series_agreement A hA R w hw E hE x hx i)))
      hdEq) hs

def discDelta (A : ValueMap (Fiber n) (Fiber n)) (R : QPos) (eps : QPos) : QPos :=
  ⟨eps.val/(32*discBudget A R.val*(rate R.val)^2+1), by
    have hb : 0 ≤ 32*discBudget A R.val*(rate R.val)^2 :=
      Rat.mul_nonneg (Rat.mul_nonneg (by decide) (discBudget_nonneg A R.val))
        (Rat.pow_nonneg (Rat.le_of_lt (rate_pos R.val (Rat.le_of_lt R.property))))
    rw [Rat.div_def]
    exact Rat.mul_pos eps.property ((Rat.inv_pos).2 (by grind))⟩

theorem disc_uniform_remainder (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A)
    (R : QPos) (eps H : QPos) (w z : Scalar) (hw : interior R.val w) (hz : interior R.val z)
    (hH : H.val ≤ (discDelta A R eps).val) (hzw : Small (sub z.val w.val) H.val)
    (E : Rat) (hE : 0 ≤ E) (x : Fiber n) (hx : CoordinateBound x E) :
    CoordinateBound (LinearField.operatorRemainder (discField A hA R) (discSlope A hA R) w z hw hz x)
      ((eps.val*H.val)*E) := by
  have hs := disc_remainder_bound A hA R w z hw hz H.val (Rat.le_of_lt H.property) hzw E hE x hx
  let B := 32*discBudget A R.val*(rate R.val)^2
  have hB : 0 ≤ B := Rat.mul_nonneg (Rat.mul_nonneg (by decide) (discBudget_nonneg A R.val))
    (Rat.pow_nonneg (Rat.le_of_lt (rate_pos R.val (Rat.le_of_lt R.property))))
  have he : (discDelta A R eps).val*(B+1)=eps.val := Rat.div_mul_cancel (Rat.ne_of_gt (by grind : 0 < B+1))
  have hm := Rat.mul_le_mul_of_nonneg_right hH (show 0 ≤ B+1 by grind)
  have hBH : B*H.val ≤ eps.val := by rw [he] at hm; have := Rat.le_of_lt H.property; grind
  have hh := Rat.mul_le_mul_of_nonneg_right hBH (Rat.le_of_lt H.property)
  have hb := Rat.mul_le_mul_of_nonneg_right hh hE
  intro i
  apply (hs i).mono
  simpa only [B, Rat.pow_succ, Rat.pow_zero, Rat.one_mul, Rat.mul_assoc] using hb

def discValueBound (A : ValueMap (Fiber n) (Fiber n)) (R : QPos) : Rat := 8*discBudget A R.val
def discDerivativeBound (A : ValueMap (Fiber n) (Fiber n)) (R : QPos) : Rat := ValueMap.linearBound A*discValueBound A R

theorem discValueBound_nonneg (A : ValueMap (Fiber n) (Fiber n)) (R : QPos) : 0 ≤ discValueBound A R :=
  Rat.mul_nonneg (by decide) (discBudget_nonneg A R.val)
theorem discDerivativeBound_nonneg (A : ValueMap (Fiber n) (Fiber n)) (R : QPos) : 0 ≤ discDerivativeBound A R :=
  Rat.mul_nonneg (ValueMap.linearBound_nonneg A) (discValueBound_nonneg A R)

theorem discField_bound (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A) (R : QPos)
    (z : Scalar) (hz : interior R.val z) (E : Rat) (hE : 0 ≤ E) (x : Fiber n) (hx : CoordinateBound x E) :
    CoordinateBound ((discField A hA R z hz).eval x) (discValueBound A R*E) :=
  value_disc_bound A hA R z hz E hE x hx

theorem discSlope_bound (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A) (R : QPos)
    (z : Scalar) (hz : interior R.val z) (E : Rat) (hE : 0 ≤ E) (x : Fiber n) (hx : CoordinateBound x E) :
    CoordinateBound ((discSlope A hA R z hz).eval x) (discDerivativeBound A R*E) := by
  have hs := ValueMap.linear_bound A hA _ (Rat.mul_nonneg (discValueBound_nonneg A R) hE)
    _ (discField_bound A hA R z hz E hE x hx)
  simpa only [discDerivativeBound, discSlope, discField, ValueMap.followedBy, Rat.mul_assoc] using hs

end ComputableAnalysis.RiemannHilbert.MatrixExponential
