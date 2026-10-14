import ComputableAnalysis.RiemannHilbert.ExponentialIntertwiners
import ComputableAnalysis.RiemannHilbert.ExponentialUniformRemainder
import ComputableAnalysis.RiemannHilbert.ConstantLinearFields

/-! Both inverse identities for the entire represented matrix exponential.
Uniform product remainders and proved zero-ODE uniqueness give the identities
on arbitrary finite discs. No inverse law is supplied as a record field. -/
namespace ComputableAnalysis.RiemannHilbert.MatrixExponential
open ComplexRaw FunctionTheory LocalSystem LocalODE LinearField
variable {n : Nat}

def minusOne : Scalar := ⟨scaleRat (-1) one, scaleRat_valid (ofQComplex_valid _)⟩
def negativeOperator (A : ValueMap (Fiber n) (Fiber n)) : ValueMap (Fiber n) (Fiber n) :=
  A.followedBy (Fiber.scaleMap minusOne)

theorem negativeOperator_linear (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A) :
    IsLinear (negativeOperator A) := IsLinear.followedBy hA (Fiber.scaleMap_linear minusOne)

theorem negativeOperator_value (A : ValueMap (Fiber n) (Fiber n)) (x : Fiber n) :
    (negativeOperator A).eval x ≈ Fiber.neg (A.eval x) := Setoid.symm (Fiber.neg_as_scale _)

theorem negativeOperator_twice (A : ValueMap (Fiber n) (Fiber n)) :
    (negativeOperator (negativeOperator A)).Equiv A := by
  intro x i
  have he : (negativeOperator (negativeOperator A)).eval x ≈ Fiber.neg (Fiber.neg (A.eval x)) :=
    Setoid.trans (negativeOperator_value (negativeOperator A) x)
    (fun j => neg_equiv (negativeOperator_value A x j))
  apply equiv_trans ((negativeOperator (negativeOperator A)).eval x |>.property i)
    (neg_valid (neg_valid ((A.eval x).property i))) ((A.eval x).property i) (he i)
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := neg_valid (neg_valid ((A.eval x).property i))) (hright := (A.eval x).property i)
  change -(-ComplexRawQuotient.ofRaw (A.eval x |>.val i) (A.eval x |>.property i)) =
    ComplexRawQuotient.ofRaw (A.eval x |>.val i) (A.eval x |>.property i)
  rw [ComplexRawQuotient.neg_eq_scaleRat_neg_one, ComplexRawQuotient.neg_eq_scaleRat_neg_one,
    ComplexRawQuotient.scaleRat_scaleRat]
  have hc : (-1 : Rat)*(-1)=1 := by decide +kernel
  rw [hc, ComplexRawQuotient.scaleRat_one]

theorem negativeOperator_congr (A B : ValueMap (Fiber n) (Fiber n)) (hAB : A.Equiv B) :
    (negativeOperator A).Equiv (negativeOperator B) :=
  fun x => Fiber.scale_congr (equiv_refl _ minusOne.property) (hAB x)

theorem negative_exponential_commutes (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A)
    (z : Scalar) (x : Fiber n) :
    A.eval ((value (negativeOperator A) (negativeOperator_linear A hA) z).eval x) ≈
      (value (negativeOperator A) (negativeOperator_linear A hA) z).eval (A.eval x) :=
  value_intertwines (negativeOperator A) (negativeOperator_linear A hA)
    (negativeOperator A) (negativeOperator_linear A hA) A hA (fun y => hA.2 minusOne (A.eval y)) z x

def inverseProduct (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A) (R : QPos) :
    Field (n := n) (m := n) (interior R.val) :=
  composeFields (discField A hA R)
    (discField (negativeOperator A) (negativeOperator_linear A hA) R) (fun _ hz => hz)

def inverseSlope (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A) (R : QPos) :
    Field (n := n) (m := n) (interior R.val) :=
  compositionSlope (discField A hA R) (discSlope A hA R)
    (discField (negativeOperator A) (negativeOperator_linear A hA) R)
    (discSlope (negativeOperator A) (negativeOperator_linear A hA) R) (fun _ hz => hz)

theorem inverseSlope_zero (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A) (R : QPos)
    (z : Scalar) (hz : interior R.val z) : (inverseSlope A hA R z hz).Equiv (ValueMap.zeroBetween n n) := by
  intro x
  let y := (value A hA z).eval x
  let u := (value (negativeOperator A) (negativeOperator_linear A hA) z).eval y
  have he : (inverseSlope A hA R z hz).eval x ≈ Fiber.add (Fiber.neg (A.eval u)) (A.eval u) :=
    Fiber.add_congr (negativeOperator_value A u) (Setoid.symm (negative_exponential_commutes A hA z y))
  exact Setoid.trans he (Setoid.trans (Fiber.add_comm _ _) (fun i => add_neg_equiv _ ((A.eval u).property i)))

def inverseDelta (A : ValueMap (Fiber n) (Fiber n)) (R : QPos) : QPos → QPos :=
  productDelta (discValueBound (negativeOperator A) R) (discDerivativeBound (negativeOperator A) R)
    (discValueBound A R) (discDerivativeBound A R)
    (discValueBound_nonneg (negativeOperator A) R) (discDerivativeBound_nonneg (negativeOperator A) R)
    (discValueBound_nonneg A R) (discDerivativeBound_nonneg A R)
    (discDelta A R) (discDelta (negativeOperator A) R)

theorem inverse_product_uniform_remainder (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A)
    (R : QPos) (eps H : QPos) (w z : Scalar) (hw : interior R.val w) (hz : interior R.val z)
    (hH : H.val ≤ (inverseDelta A R eps).val) (hzw : Small (sub z.val w.val) H.val)
    (E : Rat) (hE : 0 ≤ E) (x : Fiber n) (hx : CoordinateBound x E) :
    CoordinateBound (operatorRemainder (inverseProduct A hA R) (constant (interior R.val) (ValueMap.zeroBetween n n))
      w z hw hz x) ((eps.val*H.val)*E) := by
  have hs := compose_uniform_remainder (discField A hA R) (discSlope A hA R)
    (discField (negativeOperator A) (negativeOperator_linear A hA) R)
    (discSlope (negativeOperator A) (negativeOperator_linear A hA) R)
    (fun z _ => value_linear (negativeOperator A) (negativeOperator_linear A hA) z)
    (discValueBound (negativeOperator A) R) (discDerivativeBound (negativeOperator A) R)
    (discValueBound A R) (discDerivativeBound A R)
    (discValueBound_nonneg (negativeOperator A) R) (discDerivativeBound_nonneg (negativeOperator A) R)
    (discValueBound_nonneg A R) (discDerivativeBound_nonneg A R)
    (discField_bound (negativeOperator A) (negativeOperator_linear A hA) R)
    (discSlope_bound (negativeOperator A) (negativeOperator_linear A hA) R)
    (discField_bound A hA R) (discSlope_bound A hA R)
    (discDelta A R) (discDelta (negativeOperator A) R)
    (disc_uniform_remainder A hA R)
    (disc_uniform_remainder (negativeOperator A) (negativeOperator_linear A hA) R)
    eps H w z hw hz hH hzw E hE x hx
  exact bound_congr (operatorRemainder_congr (inverseProduct A hA R) (inverseSlope A hA R)
    (inverseProduct A hA R) (constant (interior R.val) (ValueMap.zeroBetween n n))
    (fun _ _ _ => Setoid.refl _) (inverseSlope_zero A hA R) w z hw hz x) hs

theorem affine_zero_radial (z : Scalar) (t : Rat) :
    (AffineSegment.point ⟨zero, ofQComplex_valid _⟩ z t).val.Equiv (RadialSegment.point z t).val := by
  have hzero := (ofQComplex_valid QComplex.zero)
  have hn : (neg zero).Equiv zero :=
    equiv_trans (neg_valid hzero) (add_valid hzero (neg_valid hzero)) hzero
      (equiv_symm (zero_add_equiv (neg zero) (neg_valid hzero))) (add_neg_equiv zero hzero)
  have hs : (sub z.val zero).Equiv z.val :=
    equiv_trans (sub_valid z.property hzero) (add_valid z.property hzero) z.property
      (add_equiv (equiv_refl _ z.property) hn) (add_zero_equiv _ z.property)
  exact equiv_trans (AffineSegment.point ⟨zero, hzero⟩ z t).property
    (scaleRat_valid (sub_valid z.property hzero)) (RadialSegment.point z t).property
    (zero_add_equiv _ (scaleRat_valid (sub_valid z.property hzero))) (scaleRat_equiv hs)

/-- The exponential of the negative residue is a left inverse at every
represented argument, without a smallness or radius hypothesis. -/
theorem negative_after_value (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A)
    (z : Scalar) (x : Fiber n) :
    (value (negativeOperator A) (negativeOperator_linear A hA) z).eval ((value A hA z).eval x) ≈ x := by
  let R := pointRadius z
  let p : Scalar := ⟨zero, ofQComplex_valid _⟩
  let E := LocalSystem.initialBound x
  let Z := ValueMap.zeroBetween n n
  let D := interior R.val
  let f : UniformSegment.Field (n := n) D := fun w hw => (inverseProduct A hA R w hw).eval x
  let g : UniformSegment.Field (n := n) D := fun _ _ => x
  let W := pointRadius (AffineSegment.displacement p z)
  let eta := fun eps : QPos => (⟨eps.val/(E+1), by
    rw [Rat.div_def]
    exact Rat.mul_pos eps.property ((Rat.inv_pos).2 (by have := LocalSystem.initialBound_nonneg x; grind))⟩ : QPos)
  have hE : 0 ≤ E := LocalSystem.initialBound_nonneg x
  have hfB : ∀ w hw, CoordinateBound (f w hw)
      (discValueBound (negativeOperator A) R*(discValueBound A R*E)) := by
    intro w hw
    exact discField_bound (negativeOperator A) (negativeOperator_linear A hA) R w hw _
      (Rat.mul_nonneg (discValueBound_nonneg A R) hE) _
      (discField_bound A hA R w hw E hE x (LocalSystem.initialBound_valid x))
  have hfrem : ∀ (eps H : QPos) w v hw hv, H.val ≤ (inverseDelta A R (eta eps)).val →
      Small (sub v.val w.val) H.val → CoordinateBound (UniformSegment.remainder (fun _ _ => Z) f w v hw hv) (eps.val*H.val) := by
    intro eps H w v hw hv hH hvw
    have hs := inverse_product_uniform_remainder A hA R (eta eps) H w v hw hv hH hvw
      E hE x (LocalSystem.initialBound_valid x)
    have he : (eta eps).val*(E+1)=eps.val := Rat.div_mul_cancel (Rat.ne_of_gt (by grind : 0 < E+1))
    have hm := Rat.mul_le_mul_of_nonneg_right (show E ≤ E+1 by grind) (Rat.le_of_lt (eta eps).property)
    have hh := Rat.mul_le_mul_of_nonneg_right hm (Rat.le_of_lt H.property)
    intro i
    apply (hs i).mono
    rw [← he]
    grind
  have hc := UniformSegment.equal D p z (interior_zero R.val R.property) (pointRadius_inside z)
    (fun t ht => Centered.interior_congr R.val (RadialSegment.point z t) (AffineSegment.point p z t)
      (equiv_symm (affine_zero_radial z t)) (RadialSegment.mem R.val z (pointRadius_inside z) t ht))
    W (interior_bound W.val (AffineSegment.displacement p z) (pointRadius_inside _))
    (fun _ _ => Z) f g 0
    (discValueBound (negativeOperator A) R*(discValueBound A R*E)) E (by decide)
    (by simpa only [Rat.mul_zero] using (by decide +kernel : (0 : Rat) ≤ (1 : Rat)/2))
    (Rat.mul_nonneg (discValueBound_nonneg (negativeOperator A) R) (Rat.mul_nonneg (discValueBound_nonneg A R) hE)) hE
    (by
      intro w v hw hv hwv
      exact Setoid.trans ((value (negativeOperator A) (negativeOperator_linear A hA) w).congr
        (value_congr A A hA hA (fun _ => Setoid.refl _) w v hwv x x (Setoid.refl _)))
        (value_congr _ _ (negativeOperator_linear A hA) (negativeOperator_linear A hA)
          (fun _ => Setoid.refl _) w v hwv _ _ (Setoid.refl _)))
    (fun _ _ _ _ _ => Setoid.refl _)
    (Setoid.trans ((value (negativeOperator A) (negativeOperator_linear A hA) p).congr (value_initial A hA x))
      (value_initial (negativeOperator A) (negativeOperator_linear A hA) x))
    hfB (fun _ _ => LocalSystem.initialBound_valid x)
    (fun _ _ => ValueMap.zeroBetween_linear n n)
    (by intro _ _ C _ y _; simpa only [Z, ValueMap.zeroBetween, Rat.zero_mul] using (bound_zero (n := n) 0 (by decide)))
    (fun eps => inverseDelta A R (eta eps)) (fun eps => eps) hfrem
    (by
      intro eps H w v hw hv _ _
      simpa only [Rat.mul_one, UniformSegment.remainder, operatorRemainder, constant, Z, g,
        ValueMap.zeroBetween, ValueMap.identity, id] using
        constant_uniform_remainder D ValueMap.identity eps H w v hw hv 1 (by decide) x)
  exact hc

theorem value_after_negative (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A)
    (z : Scalar) (x : Fiber n) :
    (value A hA z).eval ((value (negativeOperator A) (negativeOperator_linear A hA) z).eval x) ≈ x :=
  Setoid.trans
    (Setoid.symm (value_congr (negativeOperator (negativeOperator A)) A
      (negativeOperator_linear (negativeOperator A) (negativeOperator_linear A hA)) hA
      (negativeOperator_twice A) z z (equiv_refl _ z.property) _ _ (Setoid.refl _)))
    (negative_after_value (negativeOperator A) (negativeOperator_linear A hA) z x)

/-- Both inverse laws have already been proved before packaging the frame. -/
def frame (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A) (z : Scalar) : LinearIso n n where
  toValueIso := {
    forward := value A hA z
    backward := value (negativeOperator A) (negativeOperator_linear A hA) z
    forward_backward := value_after_negative A hA z
    backward_forward := negative_after_value A hA z }
  linear := value_linear A hA z

theorem frame_congr (A B : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A) (hB : IsLinear B)
    (hAB : A.Equiv B) (z w : Scalar) (hzw : z.val.Equiv w.val) :
    ((frame A hA z).toValueIso.forward).Equiv ((frame B hB w).toValueIso.forward) :=
  fun x => value_congr A B hA hB hAB z w hzw x x (Setoid.refl _)

theorem frame_backward_congr (A B : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A) (hB : IsLinear B)
    (hAB : A.Equiv B) (z w : Scalar) (hzw : z.val.Equiv w.val) :
    ((frame A hA z).toValueIso.backward).Equiv ((frame B hB w).toValueIso.backward) :=
  fun x => value_congr _ _ (negativeOperator_linear A hA) (negativeOperator_linear B hB)
    (negativeOperator_congr A B hAB) z w hzw x x (Setoid.refl _)

end ComputableAnalysis.RiemannHilbert.MatrixExponential
