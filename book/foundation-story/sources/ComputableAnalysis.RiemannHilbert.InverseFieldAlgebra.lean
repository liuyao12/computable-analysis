import ComputableAnalysis.RiemannHilbert.ConnectionFrameChange
import ComputableAnalysis.RiemannHilbert.ConstantLinearFields

/-! Exact inverse-field difference and first-order remainder identities.
The pointwise inverses are supplied justified isomorphisms. Their derivative
and error are conclusions, with multiplication order preserved. -/
namespace ComputableAnalysis.RiemannHilbert.LinearField
open ComplexRaw FunctionTheory LocalSystem
variable {n : Nat} {D : Scalar → Prop}

def forwardField (F : (z : Scalar) → D z → LinearIso n n) : Field (n := n) (m := n) D :=
  fun z hz => (F z hz).toValueIso.forward

def inverseField (F : (z : Scalar) → D z → LinearIso n n) : Field (n := n) (m := n) D :=
  fun z hz => (F z hz).toValueIso.backward

def inverseSlope (F : (z : Scalar) → D z → LinearIso n n)
    (DF : Field (n := n) (m := n) D) : Field (n := n) (m := n) D :=
  fun z hz => ValueMap.difference (ValueMap.zeroBetween n n)
    (((inverseField F z hz).followedBy (DF z hz)).followedBy (inverseField F z hz))

theorem inverse_difference (F : (z : Scalar) → D z → LinearIso n n)
    (w z : Scalar) (hw : D w) (hz : D z) (x : Fiber n) :
    Fiber.sub ((inverseField F z hz).eval x) ((inverseField F w hw).eval x) ≈
      (inverseField F z hz).eval
        (Fiber.sub ((forwardField F w hw).eval ((inverseField F w hw).eval x))
          ((forwardField F z hz).eval ((inverseField F w hw).eval x))) := by
  apply (F z hz).toValueIso.forward_reflects
  exact Setoid.trans ((F z hz).linear.sub _ _)
    (Setoid.trans (Fiber.sub_congr ((F z hz).toValueIso.forward_backward x) (Setoid.refl _))
      (Setoid.symm (Setoid.trans ((F z hz).toValueIso.forward_backward _)
        (Fiber.sub_congr ((F w hw).toValueIso.forward_backward x) (Setoid.refl _)))))

theorem inverse_remainder (F : (z : Scalar) → D z → LinearIso n n)
    (DF : Field (n := n) (m := n) D)
    (w z : Scalar) (hw : D w) (hz : D z) (x : Fiber n) :
    operatorRemainder (inverseField F) (inverseSlope F DF) w z hw hz x ≈
      Fiber.sub
        (Fiber.scale ⟨sub z.val w.val,sub_valid z.property w.property⟩
          ((ValueMap.difference (inverseField F w hw) (inverseField F z hz)).eval
            ((DF w hw).eval ((inverseField F w hw).eval x))))
        ((inverseField F z hz).eval
          (operatorRemainder (forwardField F) DF w z hw hz ((inverseField F w hw).eval x))) := by
  let d : Scalar := ⟨sub z.val w.val,sub_valid z.property w.property⟩
  let y := (inverseField F w hw).eval x
  let a := (forwardField F w hw).eval y
  let b := (forwardField F z hz).eval y
  let c := (DF w hw).eval y
  let U := inverseField F w hw
  let V := inverseField F z hz
  have hV := (F z hz).inverse.linear
  have hR : V.eval (Fiber.sub (Fiber.sub b a) (Fiber.scale d c)) ≈
      Fiber.sub (Fiber.sub (V.eval b) (V.eval a)) (Fiber.scale d (V.eval c)) :=
    Setoid.trans (hV.sub _ _) (Fiber.sub_congr (hV.sub _ _) (hV.2 d c))
  have hdiff : Fiber.sub (V.eval x) (U.eval x) ≈ Fiber.sub (V.eval a) (V.eval b) :=
    Setoid.trans (inverse_difference F w z hw hz x) (hV.sub _ _)
  apply Setoid.trans (Fiber.sub_congr hdiff (Setoid.refl _))
  apply Setoid.trans (b := Fiber.sub
    (Fiber.scale d (Fiber.sub (U.eval c) (V.eval c)))
    (Fiber.sub (Fiber.sub (V.eval b) (V.eval a)) (Fiber.scale d (V.eval c))))
  · intro i
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := (Fiber.sub (Fiber.sub (V.eval a) (V.eval b))
        (Fiber.scale d ((inverseSlope F DF w hw).eval x))).property i)
      (hright := (Fiber.sub (Fiber.scale d (Fiber.sub (U.eval c) (V.eval c)))
        (Fiber.sub (Fiber.sub (V.eval b) (V.eval a)) (Fiber.scale d (V.eval c)))).property i)
    change (ComplexRawQuotient.ofRaw ((V.eval a).val i) ((V.eval a).property i)-
      ComplexRawQuotient.ofRaw ((V.eval b).val i) ((V.eval b).property i))-
      ComplexRawQuotient.ofRaw d.val d.property*(0-
        ComplexRawQuotient.ofRaw ((U.eval c).val i) ((U.eval c).property i)) =
      ComplexRawQuotient.ofRaw d.val d.property*
        (ComplexRawQuotient.ofRaw ((U.eval c).val i) ((U.eval c).property i)-
          ComplexRawQuotient.ofRaw ((V.eval c).val i) ((V.eval c).property i))-
      ((ComplexRawQuotient.ofRaw ((V.eval b).val i) ((V.eval b).property i)-
          ComplexRawQuotient.ofRaw ((V.eval a).val i) ((V.eval a).property i))-
        ComplexRawQuotient.ofRaw d.val d.property*
          ComplexRawQuotient.ofRaw ((V.eval c).val i) ((V.eval c).property i))
    grind
  · exact Fiber.sub_congr (Setoid.refl _) (Setoid.symm hR)

end ComputableAnalysis.RiemannHilbert.LinearField
